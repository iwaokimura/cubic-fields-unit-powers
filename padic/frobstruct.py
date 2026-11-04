r"""
frobstruct --- E048 Phase 4, step (6b): the Frobenius structure on
A_Z, i.e. equation (22) of

  J. S. Balakrishnan, N. Dogra, J. S. Mueller, J. Tuitman, J. Vonk,
  *Explicit Chabauty-Kim for the split Cartan modular curve of level 13*,
  Annals of Math. 189 (2019), 885--944 (arXiv:1711.05846v1).

Equation, section and lemma numbers in this module are those of arXiv v1
unless marked otherwise.  In the Annals version (22) is (45) in §5.3,
(17) is (27), and v1 Lemmas 5.4 and 5.5 are Annals Lemmas 5.5 and 5.7.

§5.2 asks for an invertible matrix G with entries in H^0(]Y[, j^dagger O_Y)
solving the gauge equation  Lambda_phi G + dG = G Lambda,  where (17) and its
Frobenius pullback are

    Lambda     = -[[0,0,0], [omega,0,0], [eta, omega^T Z, 0]],
    Lambda_phi = -[[0,0,0], [phi^*omega,0,0], [phi^*eta, (phi^*omega)^T Z, 0]].

WHAT THE GAUGE EQUATION GIVES, DERIVED HERE RATHER THAN QUOTED.  Put
G = [[1,0,0],[f,F,0],[h,g^T,p]] with F and p constant.  Then

    Lambda_phi G + dG - G Lambda = 0

has exactly four nonzero blocks, and they read

    (2,1):  phi^*omega = F omega + df                       [defines F and f]
    (3,2):  dg^T = (phi^*omega)^T Z F - p omega^T Z
                 = omega^T (F^T Z F - pZ) + df^T Z F
                 = df^T Z F                                 [by §4.4(a)]
    (3,1):  dh = (phi^*omega)^T Z f - g^T omega + phi^*eta - p eta
    (2,2), (3,3):  0 = 0.

So (22) is reproduced verbatim -- unlike (19), which E071 had to correct --
and §4.4(a), F^T Z F = pZ, is used exactly once, in the (3,2) block.  That is
why E071 (Z is the CLASS Z_e M^-1, not the endomorphism) is a prerequisite:
with the endomorphism matrix the (3,2) block does not close.

THE CONSTANT OF INTEGRATION IN g, WHICH THE PAPER DOES NOT FIX.  Z F is a
CONSTANT matrix, so the (3,2) block integrates in closed form:

    g^T = f^T Z F + c^T,        c a constant vector.

(22) prescribes f(b) = 0 and h(b) = 0 but says nothing about c.  It is
nonetheless forced, and not by a normalisation: h exists at all only if the
right-hand side of the (3,1) block is exact on ]Y[, i.e. only if its class in
H^1_rig(Y) vanishes.  Writing the class of the c = 0 right-hand side as

    lambda^T omega + mu^T theta,     theta = the third-kind basis omega_2g...,

the omega-part can be cancelled by c and the theta-part cannot, so

    c = lambda,   and   mu = 0 is a CHECK on the theory, not a choice.

E072 measures c on two curves with a nonzero correspondence and finds it
NONZERO in both.  In particular g(b) = c^T is not 0: the three functions of
(22) are not all normalised at the base point, and taking g(b) = 0 -- the
reading the printed system invites -- leaves the (3,1) block with a nonzero
class and no solution h.  The gate's negative control is exactly that.

THE BASIS.  Everything here is in the basis of [BT] Definition 2.16(1) made
symplectic (Cohomology.phase4_basis), which is what §4.1 and the height formula
need; E070 established that.  The p-adic pipeline computes Phi and the
primitives f in the saturated computational basis instead, and they are carried
over here:

    omega~ = S omega + du   (rows of S, u in H^0(Y,O)),
    F~ = S F S^-1 = S Phi^T S^-1,
    f~ = S f + phi^*u - F~ u,

the last line being the only place the exact parts du of the representatives
enter.  It is derived, not assumed: apply phi^* to omega~ = S omega + du and
substitute omega = S^-1(omega~ - du).

TWO CONSTRAINTS ON THE INPUT THAT §5 DOES NOT MENTION.  First, the base point
must be a GOOD point: the r-adic representation of f, g and h converges only
where ord_p(r(x)) < 1/p ([BT] Prop 4.3, Rmk 4.4), so f(b) = 0 cannot even be
imposed at a very bad point.  E068-E070 took b = (0,0) for C_4, which is very
bad at p = 13 (x divides r), and Phase 4 moves to (t,w) = (1,3).  Second, Z has
to be rescaled so that eta is p-integral; see _rescale_Z.

E073 ADDS (23) AND (24), the trivialisation itself.  Solving (22) gives the
matrix G of overconvergent functions; what Lemma 5.4 consumes is the
Frobenius-equivariant trivialisation s^phi(b,x), which is G repackaged:

  frob_triv_teich   (23) at a Teichmuller point, from G(x_0) M = M diag(1,F,p);
  transport_series  (24)'s I(x,x_0), the parallel transport of d + Lambda,
                    whose bottom-left entry is an ITERATED integral;
  frob_triv         their composite at an arbitrary good point.

The Teichmuller point itself is points.teichmuller_point, which needs no Newton
iteration on phi: for Tuitman's lift phi^*x = x^p it is (Teichmuller lift of the
x-coordinate, Hensel root of Q above it).  See the proof there.

E091 ADDS frob_triv_general, THE SAME THING WITHOUT A TEICHMULLER POINT.  A BAD
residue disk has none the port can reach, so (23) cannot start there at all;
the gauge equation of (22) supplies the law that (23) is the fixed-point case
of, and its bottom-left block is a tiny ITERATED integral.  That is what lets
the Frobenius structure -- and with it theta -- be evaluated on C_4's leftover
disk ](0,0)[ with the ORIGINAL base point, which Lemma 5.5 (Annals Lemma 5.7)
cannot do (E090).
See frob_triv_general.
"""

from sage.all import QQ, ZZ, matrix, vector

from padic.frobenius import FrobeniusMatrix
from padic.points import CurvePoint, LocalExpansion, teichmuller_point


class FrobeniusStructure(object):
    """f, g, h of [BDM+19] (22), in the basis of phase4_basis()."""

    def __init__(self, C, H, p, N, base_point, sx=1, sy=1, FM=None,
                 verbose=False, reps=None, S=None, Z=None, eta=None):
        """reps, S, Z, eta override the defaults computed from the curve.

        The defaults are the ones E070-E074 use: the basis of phase4_basis()
        and the correspondence that Cohomology.correspondence_class builds from
        an automorphism of C_4.  A curve whose correspondences come from Hecke
        operators has neither -- [BDM+19] §6.4 prints a basis and two matrices
        Z_1, Z_2 and says nothing about where a program should get them -- so
        all four are exposed (E076).  When reps is given, S must be given with
        it: it expresses the CLASSES of reps in the H1X basis, and it is what
        carries Phi and the primitives f over (see the module docstring).  Z is
        then read in the basis reps, and eta as an E-vector.

        eta matters because §4.4 pins it only inside the span of the
        third-kind differentials omega_2g, ..., omega_2g+d-2, which is a CHOICE
        that §6.4 does not print; E075 recovered [BDM+19]'s from the printed
        eta_{Z_i} themselves, and passing it here is what makes the Hodge side
        agree with the published beta_Fil and gamma_Fil.
        """
        self.C, self.H = C, H
        self.p, self.N = ZZ(p), ZZ(N)
        self.g = ZZ(C.genus)
        self.n = 2 * self.g
        self.verbose = verbose

        if reps is None:
            self.reps, S = H.phase4_basis()
        else:
            if S is None:
                raise ValueError("reps was given without S")
            self.reps = list(reps)
        self.S = matrix(QQ, S)
        self.Si = self.S.inverse()
        if Z is None:
            Zcomp = matrix(QQ, H.correspondence_class(sx, sy))
            self.Z = self.Si.transpose() * Zcomp * self.Si  # class law, E071
        else:
            self.Z = matrix(QQ, Z)          # already in the basis reps

        self.FM = FM if FM is not None else FrobeniusMatrix(C, H, p, N)
        if getattr(self.FM, "Phi", None) is None or not hasattr(self.FM, "f"):
            self.FM.compute(primitives=True)
        self.RR = self.FM.RR
        self.K = self.FM.base
        self.cert = ZZ(self.FM.certified_precision()[0])
        self.Phi = self.FM.Phi
        Sk, Sik = self._toK(self.S), self._toK(self.Si)
        self.F = Sk * self.Phi.transpose() * Sik
        self.Zk = self._toK(self.Z)

        self.base_point = CurvePoint(self.RR, self.K(base_point[0]),
                                     y=self.K(base_point[1]))
        if not self.base_point.on_curve():
            raise ValueError("the base point is not on the curve")

        self.u = self._exact_parts()
        self.f = self._transport_f()
        if eta is None:
            self.eta_coeffs, self.eta, self.eta_info, _ = \
                H.hodge_eta(self.Z, basis=self.reps)
        else:
            self.eta_coeffs, self.eta, self.eta_info = None, list(eta), None
        self._rescale_Z()
        self.c = self.g_vec = self.h = None
        self.mu = self.solve_residual = None

    def _rescale_Z(self):
        """Clear p from the denominator of eta by rescaling Z.

        §4.4 pins Z only up to scale, and everything downstream -- eta, g, h,
        c, and the height itself -- is LINEAR in Z, so a rescaling is a global
        normalisation of h_p and nothing more.  It is needed: on C_4 at p = 13
        the primitive integral class produced by correspondence_class() gives
        eta = 41796864/6565 with 6565 = 5*13*101, and the r-adic ring is over
        Z_p.  Recomputing eta is unnecessary since hodge_eta solves a linear
        system whose right-hand side is linear in Z.
        """
        k = ZZ(0)
        for c in self.eta:
            d = QQ(c).denominator()
            if d != 0:
                k = max(k, ZZ(d).valuation(self.p))
        self.Zscale = self.p**k
        if k == 0:
            return
        self.Z = self.Zscale * self.Z
        self.Zk = self._toK(self.Z)
        self.eta = [self.Zscale * QQ(c) for c in self.eta]
        if self.eta_coeffs is not None:
            self.eta_coeffs = [self.Zscale * QQ(c) for c in self.eta_coeffs]

    # ------------------------------------------------------------- utilities

    def _toK(self, Mq):
        K = self.K
        return matrix(K, [[K(QQ(c)) for c in row] for row in Mq.rows()])

    def _const(self, v):
        """The r-adic element equal to the constant v."""
        RR = self.RR
        return RR.normalize({0: RR.Ry(RR.Rx(self.K(v)))})

    def radic_form(self, vec):
        """E-coordinates of a form -> the r-adic element A with form = A dx.

        The reduction pipeline takes its input in that convention (Tuitman's
        F_p(omega) = ... dx), while E-coordinates are the (sum u_i y^i) dx/r
        convention, so the conversion is a single r-adic digit shift.
        """
        RR = self.RR
        acc = RR.Ry.zero()
        for i, u in enumerate(self.FM._form_coefficients(vec)):
            acc += u * RR.Ry.gen()**i
        return RR.normalize({1: acc}) if acc != 0 else RR.zero()

    def evaluate(self, a, P=None):
        """The value of an r-adic element at a point (the base point default)."""
        P = P if P is not None else self.base_point
        return self.RR.evaluate(a, P.x, P.y, ring=P.ring)

    def series_of(self, a, LE, as_form=True):
        """r-adic element -> Laurent series in the local coordinate of LE.

        as_form=True returns the series of the DIFFERENTIAL a dx, i.e. with the
        factor x'(t); as_form=False the series of a as a function.  This is the
        r-adic analogue of LocalExpansion.series_of_form, and it is what lets
        the gate check dh against the RHS of (22) by local expansion -- a route
        that shares no step with the reduction that produced h.
        """
        L, S = LE.L, LE.S
        rser = S.zero()
        for k, c in enumerate(self.RR.r.list()):
            rser += LE.ring(c) * LE.xt**k
        rinv = L(1) / L(rser)
        tot = L.zero()
        for j, aj in a.items():
            v = S.zero()
            for i, coef in enumerate(self.RR.Ry(aj).list()):
                cv = S.zero()
                for k, cc in enumerate(coef.list()):
                    if cc != 0:
                        cv += LE.ring(cc) * LE.xt**k
                if cv != 0:
                    v += cv * LE.bt[i]
            if v == 0:
                continue
            tot += L(v) * rinv**j if j >= 0 else L(v) * L(rser)**(-j)
        return tot * L(LE.dxdt) if as_form else tot

    # -------------------------------------------------- the basis, transported

    def _exact_parts(self):
        """u_i with omega~_i = sum_j S_ij omega_j + du_i, as r-adic elements."""
        H, RR = self.H, self.RR
        dM = H.d_matrix()
        bas, _ = H.H1X_basis()
        out = []
        for i in range(self.n):
            tgt = vector(QQ, [QQ(c) for c in self.reps[i]])
            for j in range(self.n):
                if self.S[i][j] != 0:
                    tgt -= self.S[i][j] * vector(QQ, [QQ(c) for c in bas[j]])
            v = dM.solve_right(tgt)
            if dM * v != tgt:
                raise ArithmeticError(
                    "omega~_%d differs from S omega by a non-exact form" % i)
            acc = RR.Ry.zero()
            for m, (yi, xd) in enumerate(H.B_basis):
                if v[m] != 0:
                    acc += RR._coerce_QQ(v[m]) * RR.Rx.gen()**xd \
                        * RR.Ry.gen()**yi
            out.append(RR.normalize({0: acc}) if acc != 0 else RR.zero())
        return out

    def _transport_f(self):
        """f~ = S f + phi^*u - F~ u, then shifted so that f~(b) = 0."""
        RR = self.RR
        phiU = [RR.frobenius_apply(u, self.FM.lift.alpha, self.FM.lift.beta)
                for u in self.u]
        out = []
        for i in range(self.n):
            acc = RR.zero()
            for j in range(self.n):
                if self.S[i][j] != 0:
                    acc = RR.add(acc, RR.scalar(self.K(QQ(self.S[i][j])),
                                                self.FM.f[j]))
            acc = RR.add(acc, phiU[i])
            for j in range(self.n):
                if self.F[i][j] != 0:
                    acc = RR.sub(acc, RR.scalar(self.F[i][j], self.u[j]))
            out.append(acc)
        return [RR.sub(a, self._const(self.evaluate(a))) for a in out]

    # ----------------------------------------------------------- the solve

    def dh_rhs(self, c=None):
        """The right-hand side of the (3,1) block, as an r-adic element A with
        the differential equal to A dx.

        c defaults to the zero vector; the solve calls this once with c = 0,
        reads the constant off the class of the answer, and never has to call
        it again -- the primitive of the corrected right-hand side is the
        primitive of this one, because the correction is absorbed by the
        omega-columns of the same linear solve.
        """
        RR, n = self.RR, self.n
        phiW = [self.FM.frobenius_of_form(
            self.FM._form_coefficients(self.reps[k])) for k in range(n)]
        W = [self.radic_form(self.reps[k]) for k in range(n)]
        gt = self.g_of(c)
        out = RR.zero()
        for i in range(n):
            for j in range(n):
                if self.Z[i][j] != 0:
                    out = RR.add(out, RR.scalar(self.K(QQ(self.Z[i][j])),
                                                RR.mul(phiW[i], self.f[j])))
        for k in range(n):
            out = RR.sub(out, RR.mul(gt[k], W[k]))
        if any(cc != 0 for cc in self.eta):
            out = RR.add(out, self.FM.frobenius_of_form(
                self.FM._form_coefficients(self.eta)))
            out = RR.sub(out, RR.scalar(self.K(self.p),
                                        self.radic_form(self.eta)))
        return out

    def g_of(self, c=None):
        """g = ZF^T f + c, as a list of r-adic elements (g^T = f^T Z F + c^T)."""
        RR, n = self.RR, self.n
        ZF = self.Zk * self.F
        out = []
        for k in range(n):
            acc = RR.zero()
            for i in range(n):
                if ZF[i][k] != 0:
                    acc = RR.add(acc, RR.scalar(ZF[i][k], self.f[i]))
            if c is not None and c[k] != 0:
                acc = RR.add(acc, self._const(c[k]))
            out.append(acc)
        return out

    def solve(self):
        """Determine c, g and h.  Returns (c, mu, solve_residual).

        mu is the third-kind part of the class of the c = 0 right-hand side; it
        MUST vanish, and that it does is the one part of this computation that
        the theory predicts and we do not impose.
        """
        H, RR, n, K = self.H, self.RR, self.n, self.K
        rhs0 = self.dh_rhs()
        coords, prim = self.FM.reduce_to_E(rhs0, primitives=True)
        tk = H.third_kind_basis()
        dM = H.d_matrix()
        cols = [vector(QQ, [QQ(cc) for cc in v]) for v in self.reps] \
            + [vector(QQ, [QQ(cc) for cc in v]) for v in tk] \
            + [dM.column(j) for j in range(dM.ncols())]
        A = matrix(K, [[K(QQ(cc)) for cc in col] for col in cols]).transpose()
        sol = A.solve_right(coords)
        res = A * sol - coords
        vals = [cc.valuation() for cc in res.list() if cc != 0]
        self.solve_residual = min(vals) if vals else self.N
        self.c = vector(K, [sol[k] for k in range(n)])
        self.mu = vector(K, [sol[n + a] for a in range(len(tk))])
        # the d(B) tail of the same solve is the rest of the primitive
        acc = RR.Ry.zero()
        for m, (yi, xd) in enumerate(H.B_basis):
            cc = sol[n + len(tk) + m]
            if cc != 0:
                acc += cc * RR.Rx.gen()**xd * RR.Ry.gen()**yi
        h = RR.add(prim, RR.normalize({0: acc})) if acc != 0 else prim
        self.h = RR.sub(h, self._const(self.evaluate(h)))
        self.g_vec = self.g_of(self.c)
        return self.c, self.mu, self.solve_residual

    # ------------------------------------------- (23) and (24): the trivialisation

    def phi_image(self, P):
        """phi(P) = (x(P)^p, beta(P)), Tuitman's lift evaluated at P."""
        RR = self.RR
        return CurvePoint(RR, P.x**self.p,
                          y=RR.evaluate(self.FM.lift.beta, P.x, P.y,
                                        ring=P.ring),
                          inf=P.inf, ring=P.ring)

    def teichmuller(self, P):
        """The Teichmuller point of P's residue disk (points.teichmuller_point)."""
        return teichmuller_point(P)

    def values_at(self, P):
        """(f(P), g(P), h(P)): the non-constant entries of G at a point."""
        if self.h is None:
            self.solve()
        f = vector(P.ring, [self.evaluate(a, P) for a in self.f])
        gv = vector(P.ring, [self.evaluate(a, P) for a in self.g_vec])
        return f, gv, P.ring(self.evaluate(self.h, P))

    def _in(self, M, ring):
        """A matrix or vector over self.K, moved into ring entry by entry.

        Explicit because there is no coercion morphism out of the
        floating-point Q_p the port computes in (padic/integrals.py says the
        same thing about the Eisenstein extensions).
        """
        try:
            rows = M.rows()
        except AttributeError:
            return vector(ring, [ring(c) for c in M])
        return matrix(ring, [[ring(c) for c in row] for row in rows])

    def _block3(self, ring, a, B, c, alpha, gamma, beta):
        """[[a,0,0],[alpha,B,0],[gamma,beta^T,c]] as an (n+2)x(n+2) matrix."""
        n = self.n
        M = matrix(ring, n + 2, n + 2)
        M[0, 0] = ring(a)
        for i in range(n):
            M[1 + i, 0] = ring(alpha[i])
            for j in range(n):
                M[1 + i, 1 + j] = ring(B[i][j])
        M[n + 1, 0] = ring(gamma)
        for j in range(n):
            M[n + 1, 1 + j] = ring(beta[j])
        M[n + 1, n + 1] = ring(c)
        return M

    def read_triv(self, M):
        """(alpha, beta, gamma) read off a trivialisation matrix."""
        n = self.n
        ring = M.base_ring()
        alpha = vector(ring, [M[1 + i, 0] for i in range(n)])
        beta = vector(ring, [M[n + 1, 1 + j] for j in range(n)])
        return alpha, beta, M[n + 1, 0]

    def G_at(self, P):
        """G of (22) evaluated at P: [[1,0,0],[f,F,0],[h,g^T,p]]."""
        f, gv, hv = self.values_at(P)
        return self._block3(P.ring, 1, self._in(self.F, P.ring), self.p,
                            f, hv, gv)

    def frobenius_diag(self, ring):
        """diag(1, F, p): the Frobenius of Q_p + V_dR + Q_p(1)."""
        n = self.n
        return self._block3(ring, 1, self._in(self.F, ring), self.p,
                            [ring(0)] * n, ring(0), [ring(0)] * n)

    def frob_triv_teich(self, x0):
        r"""(23): s_0^{-1}(x_0) o s^phi(b, x_0) at a Teichmuller point x_0.

        DERIVED, not quoted.  phi fixes x_0, so Frobenius acts on the fibre
        x_0^*A_Z by the matrix G(x_0) in the trivialisation s_0, while the
        source Q_p + V_dR + Q_p(1) carries diag(1, F, p).  Frobenius-
        equivariance of M := s_0^{-1}(x_0) o s^phi(b,x_0) is therefore

            G(x_0) M = M diag(1, F, p),

        and with M = [[1,0,0],[alpha,1,0],[gamma,beta^T,1]] the three nonzero
        blocks of that equation read

            (2,1): f + F alpha = alpha        =>  alpha = (I-F)^{-1} f,
            (3,2): g^T + p beta^T = beta^T F  =>  beta^T = g^T (F-p)^{-1},
            (3,1): h + g^T alpha + p gamma = gamma
                                              =>  gamma = (g^T(I-F)^{-1}f + h)/(1-p),

        which is (23) verbatim.  Unlike (19) -- corrected in E071 -- and unlike
        (22)'s silent constant in g -- supplied in E072 -- \S5.2's second
        display needs nothing added.

        x_0 is NOT assumed to be Teichmuller: it is checked here, because the
        formula is simply false at a non-fixed point (the Frobenius of the fibre
        is then a map between two different fibres and G(x_0) is not it).
        """
        if self.h is None:
            self.solve()
        ring = x0.ring
        Fx = self.phi_image(x0)
        if min(x0.vp(Fx.x - x0.x), x0.vp(Fx.y - x0.y)) < self.cert:
            raise ValueError(
                "%s is not a Frobenius fixed point: (23) does not apply there "
                "(use points.teichmuller_point first)" % x0)
        n = self.n
        f, gv, hv = self.values_at(x0)
        F = self._in(self.F, ring)
        I = matrix.identity(ring, n)
        alpha = (I - F).inverse() * f
        beta = (F - self.p * I).inverse().transpose() * gv
        gamma = (gv * alpha + hv) / ring(1 - self.p)
        return self._block3(ring, 1, I, 1, alpha, gamma, beta)

    def frob_triv_general(self, P, at=None, tprec=None, LE=None):
        r"""M(x) = s_0^{-1}(x) o s^phi(b,x) at a point that is NOT phi-fixed.

        (23) needs a Teichmuller point, and a BAD residue disk has none that the
        port can reach: teichmuller_point refuses a bad point, and f, g, h do not
        converge at the very bad point anyway.  E091 needs the trivialisation on
        exactly such a disk -- ](0,0)[ of C_4 -- so (23) is replaced here by the
        law it is a special case of.

        DERIVED.  Write I(x,x') for the parallel transport of d + Lambda (see
        transport_series).  The gauge equation of (22), Lambda_phi G + dG =
        G Lambda, says precisely that G intertwines the two transports: the
        matrix J(x) := G(x) I(x,x') G(x')^{-1} satisfies

            dJ = (dG) I G'^{-1} + G (dI) G'^{-1}
               = (G Lambda - Lambda_phi G) I G'^{-1} - G Lambda I G'^{-1}
               = -Lambda_phi J,        J(x') = 1,

        so J is the transport of d + Lambda_phi = phi^*(d + Lambda), i.e.

            (*)   G(x) I(x,x') = I(phi x, phi x') G(x').

        Now take x' = b in (*).  With M(x) := I(x,b) M(b) -- the trivialisation
        as the port defines it -- and D := diag(1,F,p), and using that b is
        phi-FIXED (for C_4, x(b) = 1 is its own Teichmuller lift, so phi b = b):

            G(x) M(x) = G(x) I(x,b) M(b)
                      = I(phi x, phi b) G(b) M(b)          by (*)
                      = I(phi x, b) M(b) D                 by (23) AT b
                      = M(phi x) D .                                      [T]

        No constancy or connectedness argument is needed for this step: it is
        (*) with one endpoint at the base point, plus (23) there.  What (*)
        itself needs is that G be analytic along the path, i.e. BT Proposition
        4.3's region ord_p(r(x)) < 1/p -- which contains ]U[ together with the
        outer annuli of the bad disks.  For C_4 at p = 13 there is exactly ONE
        bad disk (E080), so that region is X^an minus one closed disk.

        Writing M(phi x) = Itilde M(x) with
        Itilde := I(phi x, x) -- a TINY transport, since phi preserves residue
        disks -- and Itilde = [[1,0,0],[utilde,1,0],[vtilde, utilde^T Z,1]], the
        three nonzero blocks read

            (2,1): f + F alpha = utilde + alpha
                                   =>  alpha = (I-F)^{-1} (f - utilde),
            (3,2): g^T + p beta^T = (utilde^T Z + beta^T) F
                                   =>  beta^T = (g^T - utilde^T Z F)(F-p)^{-1},
            (3,1): h + g^T alpha + p gamma = vtilde + utilde^T Z alpha + gamma
                                   =>  gamma = (h + g^T alpha - vtilde
                                                - utilde^T Z alpha)/(1-p),

        which is (23) exactly when utilde = vtilde = 0, i.e. at a Teichmuller
        point.  The (2,1) line is Algorithm 3.7 of [BT] with P = b: that
        algorithm's extra term int_b^{F(b)} omega is absent only because
        f(b) = 0 AND b is phi-fixed, and the gate checks the latter rather than
        inheriting it.

        vtilde is a TINY ITERATED integral, which transport_series already has.
        That is the whole reason this route reaches a bad disk while (24)-from-a-
        Teichmuller-point does not.

        ``at`` is the expansion point of Algorithm 3.4(1): the very bad point of
        the disk when there is one, P itself otherwise.  Returns (M, LE, I_P)
        with I_P = I(P, at), so that the caller can transport M to any other
        point R of the same disk by M(R) = I(R,at) I_P^{-1} M.
        """
        if self.h is None:
            self.solve()
        n, ring = self.n, P.ring
        base = P if at is None else (at if at.ring is ring
                                     else at.change_ring(ring))
        if LE is None:
            LE = LocalExpansion(base, tprec if tprec is not None
                                else 4 * self.N + 20)
        _, u, w, v = self.transport_series(base, LE=LE)

        def I_at(tv):
            tv = LE.ring(tv)
            return self._block3(ring, 1, matrix.identity(ring, n), 1,
                                [ring(uu(tv)) for uu in u], ring(v(tv)),
                                [ring(ww(tv)) for ww in w])

        IP = I_at(LE.t_of(P))
        Itil = I_at(LE.t_of(self.phi_image(P))) * IP.inverse()
        ut, wt, vt = self.read_triv(Itil)
        f, gv, hv = self.values_at(P)
        F = self._in(self.F, ring)
        I = matrix.identity(ring, n)
        alpha = (I - F).inverse() * (f - ut)
        beta = (F - self.p * I).inverse().transpose() * (gv - F.transpose() * wt)
        gamma = (hv + gv * alpha - vt - wt * alpha) / ring(1 - self.p)
        return self._block3(ring, 1, I, 1, alpha, gamma, beta), LE, IP

    def transport_series(self, P0, tprec=None, LE=None):
        r"""(24)'s I(x, x_0) as series in the local coordinate at P0.

        I(x,x_0) is the parallel transport of the connection d + Lambda of (17).
        A horizontal section satisfies ds = -Lambda s, so with

            N := -Lambda = [[0,0,0],[omega,0,0],[eta, omega^T Z, 0]]

        the transport matrix solves dI = N I, I(x_0,x_0) = 1.  Writing
        I = [[1,0,0],[u,1,0],[v,w^T,1]] and expanding N I gives

            du = omega,   dw^T = omega^T Z,   dv = eta + omega^T Z u,

        so that

            u = int_{x_0}^x omega,   w^T = u^T Z,
            v = int_{x_0}^x ( eta + omega^T Z int_{x_0}^{.} omega ),

        the last being an ITERATED integral -- the only one in the whole port.
        The paper never displays these; the check on them is [BDM+19] Lemma 5.5,
        whose proof writes out exactly this matrix for I(b',b) with Coleman
        integrals in place of the tiny ones.

        Returns (LE, u, w, v) with u, w lists of series and v a series.  A form
        with a pole in the disk is REFUSED rather than integrated formally: that
        is precisely the disk being outside ]U[, and eta is the entry where it
        can happen.
        """
        n = self.n
        if LE is None:
            LE = LocalExpansion(P0, tprec if tprec is not None
                                else 4 * self.N + 20)
        ring = LE.ring
        W = [self.series_of(self.radic_form(self.reps[k]), LE) for k in range(n)]
        u = [_antiderivative(s, "omega_%d" % k) for k, s in enumerate(W)]
        Z = self._in(self.Zk, ring)
        w = []
        for j in range(n):
            acc = LE.L.zero()
            for i in range(n):
                if Z[i][j] != 0:
                    acc += Z[i][j] * u[i]
            w.append(acc)
        inner = LE.L.zero()
        if any(cc != 0 for cc in self.eta):
            inner += self.series_of(self.radic_form(self.eta), LE)
        for i in range(n):
            for j in range(n):
                if Z[i][j] != 0:
                    inner += Z[i][j] * W[i] * u[j]
        v = _antiderivative(inner, "eta + omega^T Z u")
        return LE, u, w, v

    def transport(self, P0, tval, tprec=None, LE=None):
        """(24)'s I(x, x_0) as a matrix, x the point of ]P0[ at t = tval."""
        LE, u, w, v = self.transport_series(P0, tprec=tprec, LE=LE)
        tv = LE.ring(tval)
        n = self.n
        return LE, self._block3(
            LE.ring, 1, matrix.identity(LE.ring, n), 1,
            [uu(tv) for uu in u], v(tv), [ww(tv) for ww in w])

    def frob_triv(self, P, tprec=None):
        """s_0^{-1}(x) o s^phi(b,x) at any good point: (24) o (23).

        Explicitly, with M(x_0) = [[1,0,0],[alpha_0,1,0],[gamma_0,beta_0^T,1]],

            alpha_phi(x) = alpha_0 + u,
            beta_phi(x)^T = beta_0^T + w^T,
            gamma_phi(x) = gamma_0 + v + w^T alpha_0,

        the cross term w^T alpha_0 in the last line being the one thing that a
        reading of (24) as "add the integrals" would drop.
        """
        x0 = self.teichmuller(P)
        M0 = self.frob_triv_teich(x0)
        LE = LocalExpansion(x0, tprec if tprec is not None else 4 * self.N + 20)
        _, I = self.transport(x0, LE.t_of(P), LE=LE)
        return I * M0, x0

    # --------------------------------------------------------- verification

    def check_f_locally(self, P, tval, tprec=None):
        """f~_i(Q) - f~_i(P) against the tiny integral of phi^*omega~_i - F~ omega~.

        P a good point, Q = the point of its disk with local coordinate tval.
        Nothing here goes through the reduction that produced Phi and f: the
        forms are expanded in t and integrated termwise.  Returns the list of
        differences.
        """
        RR, n = self.RR, self.n
        LE = LocalExpansion(P, tprec if tprec is not None else 4 * self.N + 20)
        Q = LE.point_at(tval)
        W = [self.series_of(self.radic_form(self.reps[k]), LE) for k in range(n)]
        out = []
        for i in range(n):
            ser = self.series_of(self.FM.frobenius_of_form(
                self.FM._form_coefficients(self.reps[i])), LE)
            for j in range(n):
                if self.F[i][j] != 0:
                    ser = ser - LE.ring(self.F[i][j]) * W[j]
            lhs = self.evaluate(self.f[i], Q) - self.evaluate(self.f[i], P)
            out.append(lhs - _integrate(ser, LE.ring(tval)))
        return out

    def check_h_locally(self, P, tval, c=None, tprec=None):
        """h(Q) - h(P) against the tiny integral of the (3,1) right-hand side.

        With c = None the constant found by solve() is used and the answer must
        vanish; passing c = 0 is the negative control, and it must NOT.
        """
        LE = LocalExpansion(P, tprec if tprec is not None else 4 * self.N + 20)
        Q = LE.point_at(tval)
        cc = self.c if c is None else c
        ser = self.series_of(self.dh_rhs(cc), LE)
        lhs = self.evaluate(self.h, Q) - self.evaluate(self.h, P)
        return lhs - _integrate(ser, LE.ring(tval))


def _antiderivative(ser, what):
    """The primitive of a series, normalised to vanish at t = 0.

    A pole is refused, not integrated formally: a basis form or eta with a pole
    inside the residue disk means the disk is outside ]U[, where (24) has no
    meaning, and a t^-1 term means it is not even formally integrable.  Both
    are conditions of [BDM+19] \\S5, and both are checked here rather than
    assumed of the caller.
    """
    if ser != 0 and ser.valuation() < 0:
        raise ArithmeticError(
            "%s has a pole of order %d in this residue disk: the disk is "
            "outside ]U[ and (24) does not apply there"
            % (what, -ser.valuation()))
    return ser.integral()


def _integrate(ser, tval):
    """int_0^tval of a power series, termwise; a t^-1 term is refused."""
    out = tval.parent()(0)
    for k in range(ser.valuation(), ser.prec()):
        if k == -1:
            if ser[k] != 0:
                raise ArithmeticError("the form has a residue at the point")
            continue
        if ser[k] != 0:
            out += ser[k] / QQ(k + 1) * tval**(k + 1)
    return out
