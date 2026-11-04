r"""
height --- E048 Phase 4, step (7): the local p-adic height itself, i.e.
Lemma 5.5 of the published version (= Lemma 5.4 of arXiv v1) of

  J. S. Balakrishnan, N. Dogra, J. S. Mueller, J. Tuitman, J. Vonk,
  *Explicit Chabauty-Kim for the split Cartan modular curve of level 13*,
  Annals of Math. 189 (2019), 885--944 (arXiv:1711.05846v1).

NB: equation and lemma numbers in this module are those of arXiv v1 unless
stated otherwise; they differ in the published version.  In particular
v1 Lemma 5.4 = Annals Lemma 5.5, v1 (14) = Annals (17) (the formula for
h_p(M)), and v1 (17) = Annals (27) (the connection matrix Lambda).

Everything that goes into it exists already: E068-E070 built the Hodge side
(beta_Fil, gamma_Fil), E072 solved (22) and E073 turned it into the
Frobenius-equivariant trivialisation (alpha_phi, beta_phi, gamma_phi) as
functions on ]U[.  What this module adds is the assembly

    theta(x) = h_p(A_Z(b,x))
             = gamma_phi(x) - gamma_Fil(x)
               - beta_phi^T s_1(alpha_phi)(x) - beta_Fil^T s_2(alpha_phi)(x),

together with the two readings it needs, both of which arXiv v1 leaves to be
reconstructed and one of which E070 got wrong.  (The published version makes
both explicit: beta_Fil = (0,...,0,b_g,...,b_{2g-1})^T and N N^T = s_2.)

WHAT s_1 AND s_2 ARE.  §3.3 defines them as the idempotents of V_dR cutting out
s(V_dR/Fil^0) and Fil^0 V_dR.  The middle slot of A_Z is

    V_dR = H^1_dR(X)^*,   with T_0, ..., T_{2g-1} the DUAL basis   (§4.2, §3.1)

carrying the dual filtration, so that V_dR/Fil^0 = H^0(X, Omega^1)^*.  Hence

    Fil^0 V_dR = Ann(Fil^1 H^1_dR) = span(T_g, ..., T_{2g-1})

as soon as omega_0, ..., omega_{g-1} are honest holomorphic differentials, which
is [BT] Definition 2.16(1) = Cohomology.phase4_basis.  With the splitting s
defined by that same basis:

    s_2 = projection onto the LAST g coordinates,  s_1 = onto the first g,

and beta^T . v is the plain dot product of coordinates -- beta^T is a row of a
matrix acting on V_dR-columns, i.e. an element of V_dR^*, and there is nothing
to raise or lower.  This is consistent with how beta_Fil is computed in the
first place: its defining condition pairs it with Omega_x, the vector of local
primitives, which is a V_dR-column in the same dual basis.

E070 CORRECTED.  E070 concluded from the same formula that the pairing must be
the CUP product, because the ambiguity of beta_Fil is Fil^1 H^1_dR, which is
Lagrangian for the cup product and not isotropic for the dot product.  The
measurement was right and the inference was wrong: with s_2 read in V_dR the
ambiguity (first g coordinates) and s_2(alpha_phi) (last g) are supported on
disjoint indices, so the dot product kills it identically.  The gate keeps
E070's reading as a NEGATIVE control and measures that it does not.

INVARIANCE, WHICH IS WHY THIS MATTERS.  E069 showed beta_Fil is not unique:
adding any c in Fil^1 H^1_dR leaves the defining condition of §4.5(iii)
unchanged (sum_i c_i omega_i is holomorphic, so c^T Omega_x has no principal
part), and in the basis of Def 2.16(1) gamma_Fil does not move with it (E070).
In that basis c is supported on the first g coordinates, so

    Delta theta = -c^T s_2(alpha_phi) = 0                              [T]

identically, and h_p is well defined.  Under E070's reading the same shift
changes theta by a nonzero cup product, which is the control mentioned above.

THE SIGN OF THE HODGE SIDE.  Cohomology.hodge_filtration solves

    g_x - gamma - beta^T Omega_x  regular,

while what Lemma 5.4 wants are the entries of s_0^{-1} s^Fil.  They are the
NEGATIVES of the returned pair.  Reason: with G_x = s_x^{-1} s_0 as in §4.5,
fixed by the gauge equation G_x^{-1} dG_x = Lambda of (17) to be

    G_x = [[1,0,0], [-Omega,1,0], [g_x, -Omega^T Z, 1]]      (E071)

-- the same Lambda, with the same sign, that E072 and E073 use on the Frobenius
side, which is what makes the two halves comparable at all -- the columns of
G_x (s_0^{-1} s^Fil) are

    (1, -Omega, g_x + gamma_Fil)  and  (0, v, (beta_Fil^T - Omega^T Z) v),

and the condition below reads g_x + gamma_Fil + ... regular.  So the solver's
gamma is -gamma_Fil and its beta is -beta_Fil.

THE CONDITION ITSELF, WHICH arXiv v1 GETS WRONG.  Step (iii) of v1 §4.5 asks
for the first column above to be regular.  It need not be: Fil^0 A_Z is the
subbundle of A_Z on X that maps ISOMORPHICALLY onto Fil^0 A_1 (the defining
sequence is one of filtered connections and Fil^0 Q_p(1) = 0), so its generator
over the Q_p-slot may first be reduced modulo the columns coming from
Fil^0 V_dR.  That reduction is not optional: the poles of Omega_x sit in exactly
those directions, so it is what makes the V_dR-slot regular, and it drags
-Omega_x^T Z s_2 Omega_x into the Q_p(1)-slot.  The condition is therefore

    g_x - Omega_x^T Z s_2 Omega_x - gamma - beta^T Omega_x  in  K[[t_x]],

which is Cohomology.hodge_filtration(..., fil0_correction=True).  If instead the
column is left unreduced and has a pole of order k there, then t^k times it is a
regular section of Fil^0 A_Z whose reduction mod t_x is a pure Q_p(1)-vector, so
Fil^0 A_Z -> Fil^0 A_1 is not injective on that fibre.  The gate checks exactly
that, over Q and exactly, and finds that the pair produced by the printed
condition fails it.

This settles the question E071 left [OPEN]: QCMod's hodge.m does correct g_x by
Omega^T Z s_2 Omega before step (iii), arXiv v1 does not, and the correction is
right.  It was derived here before that code was consulted again.  The
published version already has it: its §4.5 step (iii) and the proof of
Theorem 4.11 use g_x + gamma_Fil - b_Fil^T N^T Omega_x - Omega_x^T Z N N^T
Omega_x, with N N^T the projection s_2 onto Fil^0 V_dR.  (Corrected
2026-11-04: earlier releases said "the paper" gets this wrong; only arXiv v1
does.)
"""

import copy

from sage.all import QQ, ZZ, matrix, vector

from padic.points import LocalExpansion


class LocalHeight(object):
    """theta(x) = h_p(A_Z(b,x)) of [BDM+19] Lemma 5.4 (v1) = 5.5, on ]U[."""

    def __init__(self, FS, base, fil0_correction=True, s1=None, s2=None,
                 prec=None, kmax=None, verbose=False):
        """FS a FrobeniusStructure, base its base point with RATIONAL entries.

        The Hodge side is recomputed here rather than passed in, because it has
        to use the same Z (E072 rescales it), the same eta, the same basis and
        the same base point as the Frobenius side; E068-E070 normalised
        gamma_Fil at b = (0,0) for C_4, which E072 had to abandon.

        s1, s2 default to the coordinate projections onto the first and last g
        coordinates.  They are exposed so that the gate can run E070's reading
        as a negative control, and because §6.4.1 of [BDM+19] uses a
        K-equivariant splitting rather than the one the basis defines.  They
        may be given over Q or over Q_p: the unit root splitting -- the one
        canonical K-equivariant choice, and the only one that needs no input
        beyond the curve and p -- is p-adic (E076).
        """
        self.FS = FS
        self.g, self.n = ZZ(FS.g), ZZ(FS.n)
        n, g = self.n, self.g
        self.base = None if base is None else (QQ(base[0]), QQ(base[1]))
        self.fil0_correction = bool(fil0_correction)
        beta, gamma, info = FS.H.hodge_filtration(
            FS.Z, eta=FS.eta, prec=prec, kmax=kmax, base=self.base,
            basis=FS.reps, fil0_correction=self.fil0_correction)
        self.info = info
        # the entries of s_0^{-1} s^Fil are the NEGATIVES of what the solver
        # returns; see the module docstring.
        self.beta_fil = vector(QQ, [-QQ(c) for c in beta])
        self.gamma_fil = -gamma
        self.s1 = matrix(QQ, n, n, lambda i, j:
                         QQ(1) if (i == j and i < g) else QQ(0)) \
            if s1 is None else matrix(s1)
        self.s2 = matrix(QQ, n, n, lambda i, j:
                         QQ(1) if (i == j and i >= g) else QQ(0)) \
            if s2 is None else matrix(s2)
        self.verbose = verbose

    @staticmethod
    def _co(c, R):
        """A splitting entry in the ring the assembly is happening in.

        The parent is tested rather than the conversion, because Sage will
        happily hand back a rational approximation of a p-adic number and that
        would silently throw the splitting away.
        """
        P = c.parent() if hasattr(c, "parent") else None
        if P is None or P is QQ or P is ZZ:
            return R(QQ(c))
        return R(c)

    # ------------------------------------------------- gamma_Fil, p-adically

    def _fn_at(self, f, P):
        """An element of the function field evaluated at a p-adic point."""
        K = P.ring
        val = K(0)
        for i, c in enumerate(f.list()):
            num, den = c.numerator(), c.denominator()
            d = self._poly_at(den, P.x, K)
            if d == 0 or d.valuation() > 0:
                raise ArithmeticError(
                    "gamma_Fil has a denominator vanishing mod p at %s: the "
                    "point is outside ]U[ for this representation" % P)
            val += self._poly_at(num, P.x, K) / d * P.y**i
        return val

    @staticmethod
    def _poly_at(poly, xv, K):
        out = K(0)
        for k, c in enumerate(poly.list()):
            if c != 0:
                out += K(QQ(c)) * xv**k
        return out

    def gamma_fil_series(self, LE):
        """gamma_Fil as a power series in the local coordinate of LE."""
        S, K = LE.S, LE.ring
        xs = LE.xt
        out = S.zero()
        for i, c in enumerate(self.gamma_fil.list()):
            num, den = c.numerator(), c.denominator()
            ds = self._poly_at(den, xs, S)
            if ds == 0 or ds[0] == 0 or ds[0].valuation() > 0:
                raise ArithmeticError(
                    "gamma_Fil has a denominator vanishing mod p on the disk "
                    "of %s: the disk is outside ]U[" % LE.P)
            out += self._poly_at(num, xs, S) / ds * LE.bt[i]
        return out

    # ------------------------------------------------------------- the height

    def _assemble(self, alpha, beta_phi, gamma_phi, gamma_fil):
        """(14), given the four ingredients at one point or as series."""
        n = self.n
        R = gamma_phi.parent()
        out = gamma_phi - gamma_fil
        for i in range(n):
            s1a = sum((self._co(self.s1[i][j], R) * alpha[j]
                       for j in range(n)), R(0))
            s2a = sum((self._co(self.s2[i][j], R) * alpha[j]
                       for j in range(n)), R(0))
            out = out - beta_phi[i] * s1a - R(QQ(self.beta_fil[i])) * s2a
        return out

    def frob_data(self, P, tprec=None):
        """(alpha_phi, beta_phi, gamma_phi, gamma_Fil) at P: (14)'s ingredients.

        Exposed so that the gate can vary the reading of (14), or beta_Fil, or
        the Hodge side, without recomputing (23) and (24) each time.
        """
        M, x0 = self.FS.frob_triv(P, tprec=tprec)
        alpha, beta_phi, gamma_phi = self.FS.read_triv(M)
        return alpha, beta_phi, gamma_phi, self._fn_at(self.gamma_fil, P)

    def theta(self, P, tprec=None):
        """theta at a single good point of ]U[."""
        return self._assemble(*self.frob_data(P, tprec=tprec))

    def with_splitting(self, s1=None, s2=None, beta_fil=None):
        """A copy with another splitting, or with beta_Fil shifted.

        The Hodge solve is not repeated, and must not be: neither the choice of
        splitting nor a shift of beta_Fil inside its own ambiguity changes it.
        """
        out = copy.copy(self)
        if s1 is not None:
            out.s1 = matrix(s1)
        if s2 is not None:
            out.s2 = matrix(s2)
        if beta_fil is not None:
            out.beta_fil = vector(QQ, beta_fil)
        return out

    def frob_data_series(self, P0, tprec=None, LE=None):
        r"""(14)'s four ingredients as series on the residue disk of P0.

        Returns (LE, alpha_phi, beta_phi, gamma_phi, gamma_Fil).  The composite
        of (23) and (24) is a matrix product, so

            alpha_phi = alpha_0 + u,  beta_phi^T = beta_0^T + w^T,
            gamma_phi = gamma_0 + v + w^T alpha_0,

        the cross term being what a reading of (24) as "add the integrals"
        would drop (E073).

        Split out of theta_series for E077: the extensions E_1 and E_2 of
        [BDM+19] \S6.4.1 are read off alpha_phi and beta_phi, and they are
        needed on a whole disk, not just at a point.
        """
        FS = self.FS
        x0 = FS.teichmuller(P0)
        M0 = FS.frob_triv_teich(x0)
        a0, b0, g0 = FS.read_triv(M0)
        if LE is None:
            LE = LocalExpansion(x0, tprec if tprec is not None
                                else 4 * FS.N + 20)
        _, u, w, v = FS.transport_series(x0, LE=LE)
        L = LE.L
        alpha = [L(a0[i]) + u[i] for i in range(self.n)]
        beta_phi = [L(b0[i]) + w[i] for i in range(self.n)]
        gamma_phi = L(g0) + v + sum((w[i] * L(a0[i]) for i in range(self.n)),
                                    L.zero())
        return LE, alpha, beta_phi, gamma_phi, L(self.gamma_fil_series(LE))

    def theta_series(self, P0, tprec=None, LE=None):
        """theta as a power series on the residue disk of P0. (LE, series)."""
        LE, alpha, beta_phi, gamma_phi, gfil = \
            self.frob_data_series(P0, tprec=tprec, LE=LE)
        return LE, self._assemble(alpha, beta_phi, gamma_phi, gfil)
