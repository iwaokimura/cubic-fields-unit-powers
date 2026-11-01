r"""
coho --- E048 Phase 1, second half: bases of H^1_rig(U) and H^1_rig(X).

Source: J. Tuitman, *Counting points on curves using a map to P^1*,
Math. Comp. 85 (2016), 961--981 (arXiv:1402.6758v2), Section 3.
The statements used, verbatim in content:

  Theorem 3.6.  With
      E_0     = { (sum_i u_i(x) y^i) dx/r        : u in Q_q[x]^{dx} },
      E_inf   = { (sum_i u_i(x,1/x) b^inf_i) dx/r : ord_inf(u) > ord_0(W^inf)
                                                     - deg(r) + 1 },
      B_0     = { sum_i v_i(x) y^i                : v in Q_q[x]^{dx} },
      B_inf   = { sum_i v_i(x,1/x) b^inf_i        : ord_inf(v) > ord_0(W^inf) },
  the spaces E_0 cap E_inf and d(B_0 cap B_inf) are finite dimensional and
      H^1_rig(U) = (E_0 cap E_inf) / d(B_0 cap B_inf).

  Theorem 3.11.  0 -> H^1_rig(X) -> H^1_rig(U) -> (+)_P O_{X,P}/(z_P) is exact,
  the second map being (res (+) res_inf).

  Proposition 3.12.  For omega = (sum_i u_i(x) y^i) dx/r with u in Q_q[x]^{dx},
      res(omega) = 0  <=>  (dQ/dy) sum_i u_i y^i = 0 in
                           O(X - x^{-1}(inf))/(r).
  (No hypothesis on u: this one applies to every element of our basis.)

WHAT IS PORTED HERE AND WHAT IS NOT.  Theorem 3.6 and Propositions 3.12 and
3.13 are ported.  Proposition 3.13 -- the residues at the points over infinity,
phrased through the generalised 0-eigenspace of the residue matrix Ginf_{-1} --
needs its hypothesis ord_inf(u) > -deg(r), which is stronger than what Theorem
3.6's E_0 cap E_inf gives, so it is preceded by the pole-order reduction of
Proposition 3.4; that reduction is in `padic/reductions.py` (E057).  Sage's own
function-field differentials are still computed, but only as the INDEPENDENT
implementation the gate compares against: both residue maps now exist in
Tuitman's terms (`H1X_tuitman`) and in Sage's (`H1X`).  Every function below
says which of the two it is.
"""

from sage.all import (QQ, matrix, vector, ZZ, VectorSpace, FreeModule, lcm,
                      gcd, Infinity)


def _exactify(s):
    """The same Laurent series with its O() term stripped.

    Sage propagates precision as a minimum, which would pin a Newton iterate at
    the precision of its seed; the iterate is a truncation we KNOW, so it is
    re-entered as an exact Laurent polynomial and the precision bookkeeping is
    done by the caller instead.
    """
    R = s.parent()
    if s.is_zero():
        return R.zero()
    p = s.prec()
    if p is None or p == +Infinity:
        return s
    v = s.valuation()
    return R([s[k] for k in range(v, p)]).shift(v)


def _val(s, cap):
    """Valuation of a Laurent series, +Infinity for an exact zero, and the
    working precision for one that is only zero to the precision it carries."""
    if not s.is_zero():
        return ZZ(s.valuation())
    return +Infinity if s.prec() == +Infinity else max(ZZ(s.prec()), ZZ(cap))


def _horner(poly, s):
    """A univariate polynomial over Q evaluated at a Laurent series."""
    R = s.parent()
    out = R.zero()
    for c in reversed(poly.list()):
        out = out * s + R(QQ(c))
    return out


class _LocalExpansion(object):
    r"""Laurent expansions at a place, from the expansions of x and y alone.

    WHY THIS EXISTS (E075).  Sage's own completion map is exponential in the
    requested precision on the function field of X_s(13): measured at each of
    the three places of D, m(y) costs 0.1 s at precision 2, 0.2 s at 3, 1.1 s
    at 4 and 52 s at 6, so the precision 28 that §4.5 needs is out of reach,
    while E066-E074 got away with it on C_4 and the two hyperelliptic curves.
    It is priced per ELEMENT as well: rational functions of x alone are free at
    any precision, y^3 costs 4 s at precision 4, and one of §6.1's own
    differentials -- a forty-monomial numerator over Q_y -- did not finish in
    two hours at precision 4.

    So Sage is asked for x and y ONCE, at a precision it can afford (4 is
    enough on all four curves), and the pair is refined by NEWTON on the two
    equations that define the point of the formal disk:

        Q(x, y) = 0,        T(x, y) = t,

    T being the place's own local uniformizer as an element of L and t the
    variable of the Laurent series ring.  The Jacobian is invertible because
    dT = (T_x Q_y - T_y Q_x)/Q_y dx is nonzero, T being a uniformizer, so the
    iteration is quadratic and the whole cost is series arithmetic.  Every
    other element of L is a polynomial in y over Q(x) and is then evaluated by
    series arithmetic too.  Nothing about the place, the uniformizer or the
    residue field changes -- this is a drop-in for the completion map, and the
    gate compares the two element by element on every curve.

    Refining y alone against Sage's x is not enough: measured on
    y^2 = x^5 - 1, Sage's expansion of x at the ramified place at infinity is
    free but only because it is EXACT there, and on X_s(13) the expansion of x
    at relative precision 114 is not free at all.  Both unknowns have to be
    carried.
    """

    SEEDS = (4, 6, 8, 10)

    def __init__(self, C, P, prec, pad=None):
        self.C, self.P, self.prec = C, P, prec
        # Sage delivers RELATIVE precision prec; work well above it and cut
        # back to that at the end of every evaluation.
        self.pad = 2 * prec + 30 if pad is None else pad
        self.R = None
        self._build()

    def _build(self):
        C = self.C
        W = self.prec + self.pad
        # Building the completion is free; it is APPLYING it that is not, and
        # below it is applied only at the seed precision.
        R = C.L.completion(self.P, prec=W).codomain()
        # The ring is pinned at the first build: a regrow must not hand back
        # series in a different parent from the ones already returned.
        if self.R is None:
            self.R = R
        self.x, self.y = self._newton(W)

    # ---------------------------------------------------------------- Newton

    def _peval(self, poly, xs, ys):
        """A bivariate polynomial over Q at (xs, ys)."""
        out = self.R.zero()
        for (ex, ey), c in poly.dict().items():
            out += self.R(QQ(c)) * xs**ZZ(ex) * ys**ZZ(ey)
        return out

    def _feval(self, coeffs, xs, ys):
        """(sum_i c_i(x) y^i) at (xs, ys), the c_i rational functions."""
        out, yp = self.R.zero(), self.R.one()
        for c in coeffs:
            if c != 0:
                out += yp * (_horner(c.numerator(), xs)
                             / _horner(c.denominator(), xs))
            yp = yp * ys
        return out

    def _uniformizer_data(self):
        """The local uniformizer as (c_i), and its two partial derivatives."""
        T = self.P.local_uniformizer()
        co = list(T.list())
        dTx = [c.derivative() for c in co]
        dTy = [ZZ(i) * co[i] for i in range(1, len(co))]
        return co, dTx, dTy

    def _newton(self, W):
        C, L = self.C, self.C.L
        Q = C.Qxy
        Qx, Qy = Q.derivative(C.xvar), Q.derivative(C.yvar)
        Tc, Tx, Ty = self._uniformizer_data()
        t = self.R.gen()
        self.seed = None
        for seed in self.SEEDS:
            m = L.completion(self.P, prec=seed)
            xs = _exactify(self.R(m(L(C.x))))
            ys = _exactify(self.R(m(C.y)))
            r1 = self._peval(Q, xs, ys)
            r2 = self._feval(Tc, xs, ys) - t
            J = (self._peval(Qx, xs, ys) * self._feval(Ty, xs, ys)
                 - self._peval(Qy, xs, ys) * self._feval(Tx, xs, ys))
            if J.is_zero():
                raise ArithmeticError(
                    "the Jacobian of (Q, T) vanishes at %s" % self.P)
            # Hensel: both residuals must already be inside the radius of
            # quadratic convergence.  Checked, not assumed.
            vr = min(_val(r1, W), _val(r2, W))
            if vr > 2 * ZZ(J.valuation()) + max(ZZ(xs.valuation()),
                                                ZZ(ys.valuation())):
                self.seed = seed
                break
        if self.seed is None:
            raise ArithmeticError(
                "no seed up to relative precision %d satisfies Hensel's "
                "criterion at %s" % (self.SEEDS[-1], self.P))
        acc = -Infinity
        for _ in range(64):
            r1 = self._peval(Q, xs, ys)
            r2 = self._feval(Tc, xs, ys) - t
            a, b = self._peval(Qx, xs, ys), self._peval(Qy, xs, ys)
            c, d = self._feval(Tx, xs, ys), self._feval(Ty, xs, ys)
            det = a * d - b * c
            dx = (d * r1 - b * r2) / det
            dy = (a * r2 - c * r1) / det
            prev, acc = acc, min(_val(dx, W), _val(dy, W))
            if acc >= W or acc <= prev:
                self.accuracy = acc
                return (xs.add_bigoh(acc), ys.add_bigoh(acc)) \
                    if acc != +Infinity else (xs, ys)
            xs, ys = _exactify(xs - dx), _exactify(ys - dy)
        raise ArithmeticError("Newton did not converge at %s" % self.P)

    # ---------------------------------------------- the completion interface

    def _raw(self, f):
        return self._feval(list(f.list()), self.x, self.y)

    def __call__(self, f):
        """The expansion of f in L, at the relative precision Sage would give.

        The working precision is grown rather than guessed: a bound sharp
        enough to be worth deriving would have to know the valuations of every
        coefficient of f at P, so instead the shortfall is detected and the
        expansion rebuilt.  Doubling terminates because each rebuild raises the
        absolute precision of x and y by the same amount.
        """
        if f == 0:
            return self.R.zero()
        for _ in range(6):
            out = self._raw(f)
            if out.is_zero():
                return out
            v = ZZ(out.valuation())
            if out.prec() >= v + self.prec:
                return out.add_bigoh(v + self.prec)
            self.pad = 2 * self.pad
            self._build()
        raise ArithmeticError(
            "working precision %d is still not enough for %s at %s"
            % (self.prec + self.pad, f, self.P))


def _clear_denoms(v):
    """A rational vector scaled to a primitive integral one."""
    d = ZZ(1)
    for c in v:
        d = lcm(d, QQ(c).denominator())
    w = [ZZ(QQ(c) * d) for c in v]
    g = ZZ(0)
    for c in w:
        g = g.gcd(c)
    return [c // g for c in w] if g else w


class Cohomology(object):
    """H^1_rig(U) and H^1_rig(X) for a TuitmanCurve."""

    def __init__(self, C):
        self.C = C
        self.E_basis = self._monomials(C.E_bounds())     # Theorem 3.6, E side
        self.B_basis = self._monomials(C.B_bounds())     # Theorem 3.6, B side
        self.dim_E = len(self.E_basis)
        self.dim_B = len(self.B_basis)
        self._index = {m: k for k, m in enumerate(self.E_basis)}

    # ------------------------------------------------------------------ bases

    @staticmethod
    def _monomials(bounds):
        """[(i, d)] with 0 <= d <= bounds[i]; (i,d) means x^d y^i."""
        out = []
        for i, b in enumerate(bounds):
            for d in range(b + 1):
                out.append((i, d))
        return out

    def _coords_in_E(self, coeffs):
        """Coordinates of (sum_i c_i(x) y^i) dx/r in the monomial basis of E."""
        v = [QQ(0)] * self.dim_E
        for i, c in enumerate(coeffs):
            if c == 0:
                continue
            num, den = c.numerator(), c.denominator()
            if den.degree() > 0:
                raise ArithmeticError("non-polynomial coefficient in E: %s" % c)
            den = QQ(den)
            for d, a in enumerate([QQ(t) / den for t in num.list()]):
                if a == 0:
                    continue
                if (i, d) not in self._index:
                    raise ArithmeticError(
                        "monomial x^%d y^%d outside the E bounds" % (d, i))
                v[self._index[(i, d)]] = QQ(a)
        return v

    # ------------------------------------------------------- Theorem 3.6: d

    def d_matrix(self):
        """Matrix of d : B_0 cap B_inf -> E_0 cap E_inf, columns = B basis.

        For a basis element x^d y^i of B, d(x^d y^i) = D dx with D computed by
        Sage's function-field derivation; the E-coordinates are those of r*D,
        which Proposition 2.4 (s = r/(dQ/dy) is integral) makes polynomial.
        """
        C = self.C
        L, xL, yL = C.L, C.L(C.x), C.y
        rL = L(C.r)
        cols = []
        for (i, d) in self.B_basis:
            f = xL**d * yL**i
            rD = rL * f.derivative()
            coeffs = list(rD.list())
            coeffs = coeffs + [C.K.zero()] * (C.dx - len(coeffs))
            cols.append(self._coords_in_E(coeffs))
        return matrix(QQ, self.dim_E, self.dim_B,
                      lambda a, b: cols[b][a])

    def H1U(self):
        """(dim, quotient data) for H^1_rig(U) = E / d(B), Theorem 3.6."""
        M = self.d_matrix()
        im = M.column_space()
        return self.dim_E - im.dimension(), im

    # --------------------------------------------- Proposition 3.12 (ported)

    def finite_residue_kernel_tuitman(self):
        """Subspace of E on which res = 0, by Proposition 3.12.

        The condition is (dQ/dy)*(sum u_i y^i) = 0 in O(X - x^{-1}(inf))/(r).
        Assumption 2 makes O(X - x^{-1}(inf)) = Q[x,y]/(Q) with basis the powers
        of y (that is W0 = identity, checked in auxpolys), so the condition is
        that every coordinate of the product, reduced mod Q, vanish mod r.
        """
        C = self.C
        L, xL, yL = C.L, C.L(C.x), C.y
        Rx = C.r.parent()
        dQdy = self._dQdy_in_L()
        rows = []
        for (i, d) in self.E_basis:
            prod = dQdy * (xL**d * yL**i)
            coeffs = list(prod.list())
            coeffs = coeffs + [C.K.zero()] * (C.dx - len(coeffs))
            col = []
            for c in coeffs:
                if c.denominator().degree() > 0:
                    raise ArithmeticError("non-polynomial coefficient: %s" % c)
                red = Rx(c.numerator()) % C.r
                col += [QQ(a) for a in red.list()] + \
                       [QQ(0)] * (C.degr - len(red.list()))
            rows.append(col)
        M = matrix(QQ, rows).transpose()
        return M.right_kernel()

    def _dQdy_in_L(self):
        C = self.C
        yv = C.yvar
        dQ = C.Qxy.derivative(yv)
        L, xL, yL = C.L, C.L(C.x), C.y
        out = L.zero()
        for (ex, ey), c in dQ.dict().items():
            out += QQ(c) * xL**ZZ(ex) * yL**ZZ(ey)
        return out

    # ------------------------------- Proposition 3.13 (ported, via 3.4)

    def infinite_residue_kernel_tuitman(self, red=None):
        """Subspace of E on which res_inf = 0, by Propositions 3.4 and 3.13.

        A basis element x^d y^i of E is rewritten in the b^inf basis (multiply
        the coefficient vector by (W^inf)^{-1} W^0 = (W^inf)^{-1}, since W^0 = I),
        reduced with Proposition 3.4 until ord_inf > -deg(r), which is exactly
        the hypothesis of Proposition 3.13, and then sent to the projection of
        v = (x^{1-deg r} u)|_{x=inf} onto the generalised 0-eigenspace of
        Ginf_{-1}.  That projection vanishes iff the residues at infinity do.

        The reduction is run on a fixed schedule so that the whole assignment is
        linear; see padic/reductions.py.
        """
        from padic.reductions import InfiniteReduction
        C = self.C
        K = C.K
        if red is None:
            red = InfiniteReduction(C)
        T = C.Winf.inverse()                     # W0 = identity (Assumption 2)
        cols = []
        for (i, d) in self.E_basis:
            w = vector(K, [T[j, i] * K.gen()**d for j in range(C.dx)])
            cols.append(red.residue_infinity_row(w))
        nrows = len(cols[0])
        M = matrix(QQ, nrows, self.dim_E, lambda a, b: cols[b][a])
        return M.right_kernel(), M

    def H1X_tuitman(self):
        """H^1_rig(X) with BOTH residue maps in Tuitman's own terms.

        Theorem 3.11 with the kernel of res from Proposition 3.12 and the kernel
        of res_inf from Proposition 3.13.  No Sage differential is used.
        Returns (dim, dim of the residue image, dim of the finite kernel,
        dim of the infinite kernel).
        """
        kfin = self.finite_residue_kernel_tuitman()
        kinf, Minf = self.infinite_residue_kernel_tuitman()
        ker = kfin.intersection(kinf)
        im = self.d_matrix().column_space()
        if not im.is_subspace(ker):
            raise ArithmeticError("exact forms have nonzero residue: bug")
        return (ker.dimension() - im.dimension(), self.dim_E - ker.dimension(),
                kfin.dimension(), kinf.dimension())

    def H1X_basis(self):
        """A basis of H^1_rig(X) inside E, and one of d(B_0 cap B_inf).

        Returns (vectors, dvectors): 2g integral vectors whose classes form a
        basis of ker(res + res_inf)/d(B), and an integral basis of d(B), such
        that TOGETHER they are a Z-BASIS OF THE SATURATED LATTICE
        ker(res + res_inf) cap Z^{dim E}.

        Saturation is not tidiness, it is what makes the p-adic pipeline work.
        Writing the reduced Frobenius image in this basis means solving a
        linear system whose matrix is unimodular; with an arbitrary rational
        basis -- Sage's kernel basis, say -- the lattice can have index
        divisible by p, the solve divides by that, and the resulting Phi is
        wrong by a power of p in a whole block.  Measured on C_4 at p = 5: a
        factor p^4 on the Prym block, and a characteristic polynomial with
        coefficients of valuation -16.
        """
        kfin = self.finite_residue_kernel_tuitman()
        kinf, _ = self.infinite_residue_kernel_tuitman()
        ker = kfin.intersection(kinf)
        im = self.d_matrix().column_space()
        V = FreeModule(ZZ, self.dim_E)
        Lker = V.span([_clear_denoms(v) for v in ker.basis()]).saturation()
        Lim = V.span([_clear_denoms(v) for v in im.basis()]).saturation()
        Qmod = Lker.quotient(Lim)
        if any(inv != 0 for inv in Qmod.invariants()):
            raise ArithmeticError(
                "d(B) is not saturated inside the residue kernel: %s"
                % (Qmod.invariants(),))
        lifts = [vector(QQ, g.lift()) for g in Qmod.gens()]
        dvectors = [vector(QQ, b) for b in Lim.basis()]
        return lifts, dvectors

    # ------------------------- Definition 2.16(1): the holomorphic differentials

    def holomorphic_forms_in_E(self):
        """E-coordinates of Sage's basis of H^0(X, Omega^1): the FORMS.

        holomorphic_classes() returns their classes in the H1X basis, which is
        a weaker piece of information: a class has many representatives, and
        [BT] Definition 2.16(1) asks for the forms themselves.  E070 measured
        that the difference matters -- see phase4_basis().
        """
        return [self.form_in_E(om)
                for om in self.C.L.basis_of_holomorphic_differentials()]

    def phase4_basis(self, symplectic=True):
        """Representatives satisfying [BT] Definition 2.16(1) and, with
        symplectic=True, also [BDM+19] §4.1, and the change of basis on classes.

        Returns (reps, S): reps is a list of 2g E-coordinate vectors whose
        FIRST g entries are honest holomorphic differentials, and S is the
        matrix expressing the classes of reps in the H1X basis, so that a
        correspondence transforms as Z |--> S^-T Z S^-1 and a covector as
        beta |--> S^-T beta.

        WHY THIS EXISTS (E070 step 0).  E069 found that beta_Fil is not unique
        and that moving it inside Fil^1 moves gamma_Fil by a FUNCTION, so that
        the pair is canonical only relative to a convention.  The reason is
        exactly that the H1X basis is a basis of CLASSES: for a c in Fil^1 the
        form sum_i c_i omega_i is only cohomologous to a holomorphic one,

            c^T omega = omega_hol + du,    u in H^0(Y, O),

        and E070 measured u to be non-constant for all three holomorphic
        classes of C_4 (u = -38w^2 + 3130t^2 - 952t is one of them) while it is
        constant for both test curves -- which is why the phenomenon is
        invisible on a hyperelliptic curve.  With honest holomorphic
        representatives u is constant by construction, Omega_i has no principal
        part for i <= g, and gamma no longer moves.

        [BT] Def 2.16(1) asks for precisely this and our computational basis
        does not supply it: E064 measured that every one of C_4's six basis
        elements has a pole of order 3 at infinity, so no REORDERING can work.
        Changing the representative can, because omega_i + du_i has the same
        class and is still in E (du is a column of d_matrix).

        THE SYMPLECTIC HALF.  [BDM+19] §4.2 additionally asks that the basis be
        symplectic for the cup product, and it is kept here.

        (E074 CORRECTS what E070 concluded from that.  E070 read the pairings
        beta^T . v of [BDM+19] (14) as cup products, on the ground that the
        residual ambiguity of beta_Fil is Fil^1 H^1_dR, that Fil^1 is Lagrangian
        for the cup product, and that it is NOT isotropic for the coordinate dot
        product -- all three measured here.  The premise is right and the
        conclusion is wrong: the pairing is the plain evaluation of a functional,
        because the middle slot is V_dR = H^1_dR(X)^* in its DUAL basis (§4.2),
        so beta^T . v is a dot product of coordinates and s_2 projects onto
        Fil^0 V_dR = Ann(Fil^1 H^1_dR) = the LAST g coordinates.  The ambiguity
        then pairs to zero because it lives in the first g, not because Fil^1 is
        Lagrangian.  What the symplectic normalisation buys the height formula is
        therefore nothing; Def 2.16(1) is the hypothesis that does the work.)

        The two requirements are compatible: since the first g forms span a
        Lagrangian, M = [[0, B], [-B^T, Dl]] with B invertible, and
        T = [[I, 0], [C, D]] with D = B^-T and C = -(D Dl D^T)/2 sends M to the
        standard symplectic form while KEEPING the first g forms.  (Dl is
        antisymmetric, hence so is D Dl D^T, which is why halving it works.)
        """
        C = self.C
        g, n = ZZ(C.genus), 2 * ZZ(C.genus)
        basis, _ = self.H1X_basis()
        if len(basis) != n:
            raise ArithmeticError("H1X has dimension %d, expected 2g = %d"
                                  % (len(basis), n))
        S = self.adapted_change_of_basis()
        reps = [list(v) for v in self.holomorphic_forms_in_E()]
        for i in range(g, n):
            row = S.row(i)
            nz = [j for j in range(n) if row[j] != 0]
            if len(nz) != 1 or row[nz[0]] != 1:
                raise ArithmeticError(
                    "row %d of the adapted basis is not a standard vector: %s"
                    % (i, row))
            reps.append(list(basis[nz[0]]))
        if not symplectic:
            return reps, S
        M = self.cup_product_matrix(basis=reps)
        A = M.submatrix(0, 0, g, g)
        B = M.submatrix(0, g, g, g)
        if A != 0:
            raise ArithmeticError(
                "the holomorphic forms are not isotropic for the cup product: "
                "%s" % A)
        if B.determinant() == 0:
            raise ArithmeticError(
                "the cup product does not pair Fil^0 with the complement")
        D = B.inverse().transpose()
        Cm = -(D * M.submatrix(g, g, g, g) * D.transpose()) / 2
        T = matrix(QQ, n, n, lambda i, j:
                   (QQ(1) if i == j else QQ(0)) if i < g else
                   (Cm[i - g, j] if j < g else D[i - g, j - g]))
        J = matrix(QQ, n, n, lambda i, j:
                   QQ(1) if (i < g and j == i + g) else
                   (QQ(-1) if (i >= g and j == i - g) else QQ(0)))
        if T * M * T.transpose() != J:
            raise ArithmeticError(
                "the symplectic completion failed: T M T^T - J = %s"
                % (T * M * T.transpose() - J))
        old = [vector(QQ, v) for v in reps]
        reps = [list(sum((T[i][j] * old[j] for j in range(n)),
                         vector(QQ, [QQ(0)] * len(old[0]))))
                for i in range(n)]
        return reps, T * S

    def holomorphic_classes(self, basis=None):
        """The g classes of H^0(X, Omega^1) written in the given basis
        (H1X_basis by default; pass phase4_basis()'s representatives to get
        them in the basis of [BT] Definition 2.16(1), where they must come out
        as the first g standard vectors -- the gate checks that).

        Balakrishnan-Tuitman Definition 2.16(1) asks that omega_1, ..., omega_g
        be a basis of H^0(X, Omega^1).  H1X_basis() gives a basis of the
        SATURATED LATTICE, which is what the p-adic pipeline needs and which
        says nothing about regularity; the two requirements are different and
        this is where they are reconciled.

        Returns a g x 2g rational matrix T whose rows are the holomorphic
        classes.  It is NOT in general a permutation matrix, and for C_4 no
        reordering could do the job: measured, every one of the six basis
        elements has a pole of order 3 at infinity, so the regular subspace is
        spanned by no subset of them.  (For y^2 = x^5-1 it does come out a
        permutation, which is why a hyperelliptic-only test would have left the
        wrong impression.)

        Method: Sage's function field gives a basis of the holomorphic
        differentials directly.  Each is written as (sum_i u_i(x) y^i) dx/r and
        then matched against the H^1 basis MODULO THE IMAGE OF d -- cohomologous
        is not equal, and solving without the d-block simply has no solution.
        """
        rows = self.holomorphic_forms_in_E()
        if basis is None:
            basis, _ = self.H1X_basis()
        dM = self.d_matrix()
        cols = [vector(QQ, list(b)) for b in basis] \
            + [dM.column(j) for j in range(dM.ncols())]
        M = matrix(QQ, cols).transpose()
        lam = [list(M.solve_right(vector(QQ, hv)))[:len(basis)] for hv in rows]
        T = matrix(QQ, lam)
        if T.rank() != ZZ(self.C.genus):
            raise ArithmeticError(
                "the holomorphic classes span %d dimensions, expected g = %d"
                % (T.rank(), self.C.genus))
        return T

    def holomorphic_exact_parts(self, basis=None):
        """[(c, u)] for the g holomorphic classes: the exact part.

        For each class c returned by holomorphic_classes, the function u in
        H^0(Y, O) with

            c^T omega = omega_hol + du.

        u is unique up to a constant (the kernel of d is the constants), and c
        is unique.  E070: u is constant exactly when the basis satisfies [BT]
        Definition 2.16(1) at the level of FORMS, and it is u that measures how
        far gamma_Fil moves when beta_Fil moves by c -- namely by -(u - u(b)),
        verified against the defining condition rather than assumed.
        """
        C = self.C
        L, xL, yL = C.L, C.L(C.x), C.y
        rows = self.holomorphic_forms_in_E()
        bas = basis if basis is not None else self.H1X_basis()[0]
        dM = self.d_matrix()
        cols = [vector(QQ, list(b)) for b in bas] \
            + [dM.column(j) for j in range(dM.ncols())]
        M = matrix(QQ, cols).transpose()
        out = []
        for hv in rows:
            sol = M.solve_right(vector(QQ, hv))
            lam = list(sol)[:len(bas)]
            u = L.zero()
            for j, (i, d) in enumerate(self.B_basis):
                c = list(sol)[len(bas) + j]
                if c != 0:
                    u += QQ(c) * xL**d * yL**i
            # M * sol = hv reads  sum lam_i omega_i + du = omega_hol,
            # so c^T omega = omega_hol + d(-u)
            out.append((lam, -u))
        return out

    def adapted_change_of_basis(self, basis=None):
        """An invertible 2g x 2g matrix S with the first g rows spanning
        H^0(X, Omega^1): the basis Definition 2.16(1) asks for, expressed in the
        given basis (the computational one by default).

        The computational basis is deliberately NOT replaced.  Its integrality
        and saturation are what make the reductions and their precision
        certificates valid (see H1X_basis); an adapted basis need not be
        integral, and switching to it would invalidate E059's Propositions 3.7
        and 3.8 bookkeeping.  Phase 4 applies S to finished results instead.
        """
        T = self.holomorphic_classes(basis)
        g, n = T.nrows(), T.ncols()
        rows = [T.row(i) for i in range(g)]
        V = (QQ**n).span(rows)
        for k in range(n):
            e = (QQ**n).gen(k)
            if e not in V:
                rows.append(e)
                V = (QQ**n).span(rows)
            if len(rows) == n:
                break
        S = matrix(QQ, rows)
        if S.determinant() == 0:
            raise ArithmeticError("failed to extend to a basis")
        return S

    # --------------------------- the cup product (E065 Phase 4, step 2)

    def candidate_places(self):
        """The only places where a differential of E can have a pole.

        omega = (sum_i u_i(x) y^i) dx/r with the u_i polynomial, and with
        W^0 = I (Tuitman's Assumption 2, verified by TuitmanCurve) the function
        sum_i u_i y^i is integral over Q[x], hence regular away from x =
        infinity.  So the poles of omega lie over x = infinity or over the
        zeros of r, and dx contributes nothing new: it is regular away from
        infinity.  That is a proof, and it is what makes this cheap.

        WHY NOT divisor() (E075).  Sage's divisor() is the obvious route and it
        is what this used to do.  On X_s(13) it does not finish: measured, a
        SINGLE form of the computational basis (57-digit coefficients) had not
        produced its divisor after 400 s, while the two ideal factorisations
        here take 0.0 s on all four curves.  Sage's places_infinite() is not a
        substitute either -- it returns two of the three places over x =
        infinity on X_s(13) and the EMPTY list on C_4, where the factorisation
        correctly returns the one place of degree 4.
        """
        cache = self.__dict__.get("_cand_places")
        if cache is None:
            C = self.C
            L, xL = C.L, C.L(C.x)
            cache = [I.place() for I, _ in
                     L.maximal_order_infinite().ideal(1 / xL).factor()]
            cache += [I.place() for I, _ in
                      L.maximal_order().ideal(L(C.r)).factor()]
            self._cand_places = cache
        return cache

    def pole_order(self, om, P):
        """Order of the pole of a differential at a place, 0 if regular."""
        if om.is_zero():
            return ZZ(0)
        C = self.C
        vdx = -ZZ(P.local_uniformizer().derivative().valuation(P))
        return max(ZZ(0),
                   -(ZZ((om / C.L(C.x).differential()).valuation(P)) + vdx))

    def worst_pole(self, forms, places=None):
        """The deepest pole any of the forms has on the candidate places."""
        pl = self.candidate_places() if places is None else places
        return max([self.pole_order(om, P) for om in forms for P in pl]
                   + [ZZ(0)])

    def _pole_places(self, forms):
        """Every place where one of the given differentials has a pole."""
        return [P for P in self.candidate_places()
                if any(self.pole_order(om, P) > 0 for om in forms)]

    def differential_of(self, vec):
        """E-coordinates -> the differential (sum_i u_i(x) y^i) dx/r on L."""
        C = self.C
        L, xL, yL = C.L, C.L(C.x), C.y
        f = L.zero()
        for c, (i, d) in zip(vec, self.E_basis):
            if c != 0:
                f += QQ(c) * xL**d * yL**i
        return (f / L(C.r)) * xL.differential()

    def form_in_E(self, om):
        """E-coordinates of a differential of L: the inverse of differential_of.

        om must be (sum_i u_i(x) y^i) dx / r with the u_i POLYNOMIAL and within
        the bounds of Theorem 3.6; both are checked rather than assumed, since
        a differential written down by hand -- E075 feeds this the published
        basis of [BDM+19] §6.1, given as (polynomial in x, y) dx/Q_y -- has no
        reason to lie in E, and r/(dQ/dy) being integral (Proposition 2.4) is
        what makes that particular shape land inside it.
        """
        C = self.C
        h = (om / C.L(C.x).differential()) * C.L(C.r)
        co = list(h.list())
        co = co + [C.K.zero()] * (C.dx - len(co))
        return self._coords_in_E(co)

    def cup_product_matrix(self, prec=None, basis=None):
        """The matrix of the cup product on H^1_rig(X) in the given basis
        (H1X_basis by default; phase4_basis()'s representatives for the
        symplectic basis [BDM+19] §4.1 requires).

        For forms of the second kind the pairing is

            <omega, eta> = sum_P Res_P(f_omega * eta),    d f_omega = omega,

        the sum over the poles.  E062(d) established that Tuitman's E_0 forms
        are regular at every FINITE point -- their poles are all at infinity --
        so the sum has very few terms (one place, of degree 4, for C_4).

        THIS IS EXACT AND HAPPENS OVER Q.  No p-adic approximation enters: the
        local expansions come from the function field's completion, the residue
        is a coefficient of a Laurent series, and the value is the trace of that
        coefficient down to Q.  That matters because E065(d) showed the cheap
        p-adic route -- solving Phi^T M Phi = p M -- CANNOT determine this
        matrix when End(J) is larger than Z, which is exactly our case.  Here
        that identity becomes an independent CHECK instead (see the gate).
        """
        C = self.C
        L, xL = C.L, C.L(C.x)
        bas = basis if basis is not None else self.H1X_basis()[0]
        forms = [self.differential_of(v) for v in bas]
        n = len(forms)
        poles = self._pole_places(forms)
        if prec is None:
            # enough terms to see s^{-1} in f_omega * eta: pole orders add
            prec = 4 * self.worst_pole(forms) + 10
        M = matrix(QQ, n, n)
        for P in poles:
            m = self.expansion_at(P, prec)
            t = P.local_uniformizer()
            dtdx = t.derivative()
            ser = [m(om / xL.differential() / dtdx) for om in forms]
            prim = []
            for g in ser:
                if g[-1] != 0:
                    raise ArithmeticError(
                        "the form has residue %s at %s: not of the second kind"
                        % (g[-1], P))
                F = g.parent().zero()
                for k in range(g.valuation(), g.prec()):
                    if k != -1 and g[k] != 0:
                        F += g[k] / QQ(k + 1) * g.parent().gen()**(k + 1)
                prim.append(F)
            for i in range(n):
                for j in range(n):
                    c = (prim[i] * ser[j])[-1]
                    M[i, j] += QQ(c.trace()) if hasattr(c, "trace") else QQ(c)
        return M

    # ------------------- Algorithm 3.12 step (5): the correspondence, over Q

    def _in_basis(self, vecs):
        """Write E-coordinate vectors in the H1X basis MODULO the image of d.

        Cohomologous is not equal: without the d-block the system has no
        solution (E064 learned this the expensive way).
        """
        basis, _ = self.H1X_basis()
        dM = self.d_matrix()
        cols = [vector(QQ, list(b)) for b in basis] \
            + [dM.column(j) for j in range(dM.ncols())]
        M = matrix(QQ, cols).transpose()
        return [list(M.solve_right(vector(QQ, v)))[:len(basis)] for v in vecs]

    def automorphism_matrix(self, sx=1, sy=1):
        """The matrix of alpha^* on H^1_rig(X) for alpha : (x,y) -> (sx x, sy y).

        Both curves this project calibrates on have such an automorphism, and it
        is the source of the correspondence quadratic Chabauty needs:
        C_4 has sigma : w -> -w, whose quotient is E (E037), and the bielliptic
        genus 2 curves y^2 = x^6+ax^4+bx^2+c of E050 have tau : x -> -x, whose
        quotients are the two elliptic factors.

        On the monomial basis of E the action is diagonal:
        x^d y^i dx/r  |-->  sx^{d+1} sy^i x^d y^i dx/r, the extra power of sx
        coming from dx.  That r and Q are invariant is CHECKED, not assumed --
        the formula is silently wrong otherwise.
        """
        C = self.C
        sx, sy = ZZ(sx), ZZ(sy)
        Rx = C.r.parent()
        if Rx([c * sx**k for k, c in enumerate(C.r.list())]) != C.r:
            raise ValueError("r is not invariant under x -> %s x" % sx)
        Q2 = C.Qxy.parent().zero()
        for (ex, ey), c in C.Qxy.dict().items():
            Q2 += c * sx**ZZ(ex) * sy**ZZ(ey) \
                * C.xvar**ZZ(ex) * C.yvar**ZZ(ey)
        if Q2 != C.Qxy and Q2 != -C.Qxy:
            raise ValueError("(x,y) -> (%s x, %s y) is not an automorphism"
                             % (sx, sy))
        basis, _ = self.H1X_basis()
        images = []
        for v in basis:
            w = [QQ(0)] * self.dim_E
            for c, (i, d) in zip(v, self.E_basis):
                if c != 0:
                    w[self._index[(i, d)]] = QQ(c) * sx**(d + 1) * sy**i
            images.append(w)
        rows = self._in_basis(images)
        # rows[k] are the coordinates of alpha^*(omega_k): as a matrix acting on
        # coordinate vectors this is the transpose
        return matrix(QQ, rows).transpose()

    def correspondence(self, sx=1, sy=1):
        """A trace-zero, Rosati-symmetric Z in End(J) from that involution.

        THIS IS THE ENDOMORPHISM MATRIX.  Everything in [BDM+19] §§4.5 and 5.2
        needs the CLASS instead -- see correspondence_class, and E071 for the
        measurement that they are different and that only the class satisfies
        the conditions those sections are derived from.

        Balakrishnan-Dogra-Mueller-Tuitman-Vonk need a class in
        Ker(NS(J) -> NS(X)); for a curve NS(X) = Z and the map is the trace, so
        the kernel consists of the symmetric endomorphisms of trace zero.  With
        S the involution and pi_+- = (1 +- S)/2 the projectors onto its
        eigenspaces (the two isogeny factors), the trace-zero combination is
        unique up to scale:

            Z = d_- pi_+  -  d_+ pi_- ,     d_+- = dim of the +- eigenspace,

        normalised here by dividing out the content.  Remark 3.17 of that paper
        explicitly allows this route -- knowing generators of End(J) in advance
        -- in place of the Hecke operator, which is the ONLY step of their
        algorithm specific to modular curves.
        """
        S = self.automorphism_matrix(sx, sy)
        n = S.nrows()
        I = matrix(QQ, n, n, 1)
        if S * S != I:
            raise ArithmeticError("the automorphism is not an involution on H^1")
        dp = ZZ((S.trace() + n) / 2)
        dm = n - dp
        Z = dm * (I + S) / 2 - dp * (I - S) / 2
        den = lcm([QQ(c).denominator() for c in Z.list()])
        Zi = matrix(ZZ, Z * den)
        g = gcd(Zi.list())
        return Zi / g if g else Zi

    def correspondence_class(self, sx=1, sy=1, endo=None):
        """The COHOMOLOGY CLASS of that correspondence: Z = sum Z_ij om_i (x) om_j.

        [BDM+19] §4.1 defines Z as a class in H^1_dR(X) (x) H^1_dR(X) subject to
        four conditions, then in §4.4 writes "the matrix of the correspondence Z
        on H^1_dR(X)" for the same symbol.  Those are two different matrices,
        and every formula of §§4.5 and 5.2 needs the CLASS: (22) is derived from
        F^T Z F = pZ, which is condition (a), and the endomorphism matrix does
        not satisfy it (measured, E071: valuation 0 where the certified
        precision is 5).

        With M the cup product matrix and Z_e = correspondence(), the class is

            Z  =  Z_e M^{-1}   ( = M^{-1} Z_e^T, by Rosati symmetry ),

        and each of §4.1's four conditions is one of E067's four properties of
        Z_e -- so this is a proof, not a fit:

          (d) Z antisymmetric        <=>  M Z_e = Z_e^T M      (Rosati)
          (c) Z |-> 0 under cup       <=>  tr Z_e = 0
                 since Z^T M = -Z_e, so tr(Z^T M) = -tr Z_e
          (b) Z in Fil^1(H^1 (x) H^1) <=>  Z_e preserves Fil^1 -- true because
                 Z_e comes from an automorphism of the curve.  In a symplectic
                 basis with the holomorphic forms first, (Z_e J^{-1})_ij for
                 i, j >= g is -(Z_e)_{i, j-g}.
          (a) F^T Z F = pZ            <=  Z_e Phi = Phi Z_e and Phi M^{-1} Phi^T
                 = p M^{-1} (E066's calibration, inverted), with F = Phi^T:
                 Phi Z_e M^{-1} Phi^T = Z_e (Phi M^{-1} Phi^T) = p Z_e M^{-1}.

        The map Z_e |--> Z_e M^{-1} is a bijection from the Rosati-symmetric,
        trace-zero, Fil^1-preserving, Phi-commuting endomorphisms to the classes
        satisfying (a)-(d), so nothing is lost and the ambiguity is only the
        scale -- which rescales h_p and cancels in quadratic Chabauty.

        NOTE ON F.  compute() stores Phi with F_p(omega_j) = sum_i Phi_ij
        omega_i, i.e. acting on COORDINATE vectors; [BDM+19] write phi^* omega =
        F omega + df for the COLUMN OF FORMS, so F = Phi^T.  The two readings of
        (a) differ and only the class satisfies either.
        """
        Ze = matrix(QQ, self.correspondence(sx, sy)) if endo is None \
            else matrix(QQ, endo)
        M = self.cup_product_matrix()
        Z = Ze * M.inverse()
        if Z.transpose() != -Z:
            raise ArithmeticError(
                "the class is not antisymmetric: the endomorphism is not "
                "Rosati-symmetric for this cup product matrix")
        den = lcm([QQ(c).denominator() for c in Z.list()])
        Zi = matrix(ZZ, Z * den)
        g = gcd(Zi.list())
        return Zi / g if g else Zi

    # ------------- Algorithm 3.12 step (6a): the Hodge filtration, over Q

    def third_kind_basis(self):
        """Differentials of the third kind with poles only over x = infinity.

        Balakrishnan-Dogra-Mueller-Tuitman-Vonk (2019) §4.5 needs
        omega_{2g}, ..., omega_{2g+d-2} extending the symplectic basis of
        H^1_dR(X) to one of H^1_dR(Y), Y the affine curve and D = X - Y of
        degree d.  They are exactly the classes with vanishing residues at the
        FINITE points and nonvanishing ones at infinity, so E056's two residue
        kernels produce them with no new machinery:

            ker(res_finite) / ( ker(res_finite) cap ker(res_inf) )

        has dimension d - 1 (measured: 3 for C_4, whose D is one place of degree
        4; 0 for an odd-degree hyperelliptic model, whose D is one rational
        point -- and there the theory needs none).

        The count d - 1 is right over Q and not only over Qbar: a Galois-stable
        tuple of residues on a degree-d place is an element of the residue
        field, and the residue theorem cuts it down to the trace-zero part,
        which is a (d-1)-dimensional Q-vector space.
        """
        kfin = self.finite_residue_kernel_tuitman()
        kinf, _ = self.infinite_residue_kernel_tuitman()
        both = kfin.intersection(kinf)
        im = self.d_matrix().column_space()
        out = []
        cur = both + im
        for v in kfin.basis():
            if v not in cur:
                out.append(vector(QQ, v))
                cur = cur + (QQ**self.dim_E).span([v])
        return out

    @staticmethod
    def _dg_expr(Z, ser, Om, n, printed=False):
        """The local right-hand side of dg_x, before eta is subtracted.

        THE GAUGE EQUATION, NOT [BDM+19] (19).  Write the gauge transformation
        of §4.5 as G = [[1,0,0],[A,1,0],[c,b^T,1]].  Then

            G^-1 dG = [[0,0,0],[dA,0,0],[dc - b^T dA, db^T, 0]],

        and (18) sets this equal to Lambda of (17), so dA = -omega, giving
        A = -Omega; db^T = -omega^T Z, giving b^T = -Omega^T Z; and

            dc = b^T dA - eta = Omega^T Z omega - eta.

        (19) prints A = +Omega together with dOmega = omega, which already
        contradicts (18) with (17)'s sign, and gives

            dg_x = dOmega^T Z Omega - Omega^T (Z - Z^T) omega - eta
                 = Omega^T (2Z^T - Z) omega - eta,

        which agrees with the gauge equation if and only if Z is SYMMETRIC.
        The Z of §4.1 is antisymmetric, and there the printed formula is -3
        times the right one on the Z term.  E067--E070 used the endomorphism
        matrix, which IS symmetric, so the two errors cancelled and neither was
        visible; E071 corrects both.  printed=True reproduces (19) as printed
        and is used by the gates as a negative control.
        """
        expr = ser[0].parent().zero()
        for i in range(n):
            for j in range(n):
                if printed:
                    if Z[i][j] != 0:
                        expr += QQ(Z[i][j]) * (ser[i] * Om[j] - Om[i] * ser[j])
                    if Z[j][i] != 0:
                        expr += QQ(Z[j][i]) * Om[i] * ser[j]
                elif Z[i][j] != 0:
                    expr += QQ(Z[i][j]) * Om[i] * ser[j]
        return expr

    def hodge_eta(self, Z, prec=None, basis=None, printed=False):
        """Step (i) of BDMTV (2019) §4.5: the differential eta.

        eta is the unique combination of the third-kind differentials for which

            Omega^T Z omega - eta

        has vanishing residue at every point of D -- see _dg_expr for why that,
        and not the expression printed in (19).  Omega is the vector of
        formal integrals of the basis differentials, so this is computed from
        the same local expansions E066 uses for the cup product.

        The residue at a place of degree f is an element of its residue field,
        i.e. f rational conditions; summing to zero by the residue theorem, they
        leave d - 1 independent ones against the d - 1 unknowns, which is the
        uniqueness of [BDM+19, Lemma 4.10] made concrete.

        Returns (coefficients, eta as an E-vector, the residues before and
        after subtracting eta).
        """
        C = self.C
        L, xL = C.L, C.L(C.x)
        bas = basis if basis is not None else self.H1X_basis()[0]
        n = len(bas)
        tk = self.third_kind_basis()
        forms = [self.differential_of(v) for v in bas]
        tkf = [self.differential_of(v) for v in tk]
        poles = self._pole_places(forms + tkf)
        if prec is None:
            prec = 4 * self.worst_pole(forms + tkf) + 10
        rows, rhs = [], []
        info = []
        for P in poles:
            m, ser, _, _ = self.local_data(P, prec, basis)
            dtdx = P.local_uniformizer().derivative()
            tkser = [m(o / xL.differential() / dtdx) for o in tkf]
            Om = []
            for gser in ser:
                F = gser.parent().zero()
                for k in range(gser.valuation(), gser.prec()):
                    if k != -1 and gser[k] != 0:
                        F += gser[k] / QQ(k + 1) * gser.parent().gen()**(k + 1)
                Om.append(F)
            expr = self._dg_expr(Z, ser, Om, n, printed=printed)
            res0 = expr[-1]
            k = P.residue_field() if hasattr(P, "residue_field") else None
            coords = list(res0.vector()) if hasattr(res0, "vector") else [res0]
            for c in range(len(coords)):
                rows.append([QQ(list(tkser[a][-1].vector())[c]
                                if hasattr(tkser[a][-1], "vector")
                                else tkser[a][-1])
                             for a in range(len(tkf))])
                rhs.append(QQ(coords[c]))
            info.append((P, res0))
        if not tkf:
            return [], [QQ(0)] * self.dim_E, info, rhs
        A = matrix(QQ, rows)
        b = vector(QQ, rhs)
        sol = A.solve_right(b)
        eta = [QQ(0)] * self.dim_E
        for c, v in zip(sol, tk):
            for i in range(self.dim_E):
                eta[i] += c * QQ(v[i])
        return list(sol), eta, info, rhs

    # ------- steps (ii) and (iii) of BDMTV (2019) §4.5: g_x, beta_Fil, gamma_Fil

    def local_data(self, P, prec, basis=None):
        """Cached Laurent expansions at a place P to t-adic precision prec.

        Returns (m, ser, mx, mb): the completion map, the expansions of the
        basis differentials as series in dt, and those of x and of the
        integral basis b^0_i.  basis defaults to H1X_basis(); pass the
        representatives of phase4_basis() to work in the basis [BT] Definition
        2.16(1) asks for.

        The cache is what makes the gate affordable.  L.completion(P, prec)
        applied to a differential is expensive at a place of degree 4, and the
        gate deliberately recomputes the same expansions several times -- at
        the solve's precision, at a higher one, and with shifted constants of
        integration -- so without this the same series are rebuilt six times.

        m is _LocalExpansion, not Sage's completion map: on X_s(13) the latter
        is exponential in the precision (E075).  It is a drop-in, and the gates
        compare the two.
        """
        C = self.C
        L, xL = C.L, C.L(C.x)
        cache = self.__dict__.setdefault("_local_cache", {})
        tag = None if basis is None \
            else tuple(tuple(QQ(c) for c in v) for v in basis)
        key = (P, prec, tag)
        if key not in cache:
            if basis is None:
                basis, _ = self.H1X_basis()
            forms = [self.differential_of(v) for v in basis]
            m = self.expansion_at(P, prec)
            dtdx = P.local_uniformizer().derivative()
            ser = [m(o / xL.differential() / dtdx) for o in forms]
            mx = m(xL)
            mb = [m(b) for b in L.maximal_order().basis()]
            cache[key] = (m, ser, mx, mb)
        return cache[key]

    def expansion_at(self, P, prec):
        """_LocalExpansion at P, cached; a drop-in for L.completion(P, prec)."""
        cache = self.__dict__.setdefault("_exp_cache", {})
        if (P, prec) not in cache:
            cache[(P, prec)] = _LocalExpansion(self.C, P, prec)
        return cache[(P, prec)]

    def candidate_series(self, P, prec, kmax):
        """The expansions of the candidates x^k b^0_i at P, with their keys.

        These span the part of H^0(Y, O) with poles bounded on D, and they are
        obtained by MULTIPLYING the cached expansions of x and of the b^0_i --
        never by completing each x^k b^0_i, which is what made the first
        version unusable.

        Exposed (and cached) because the gate needs them too: expanding a
        gamma through L.completion is fine for the SMALL gamma of the main
        solve, and catastrophic for the shifted one -- measured at C_4's
        degree-4 place, no single monomial costs more than 12 s, while the full
        function with fourteen-digit coefficients DID NOT FINISH IN 40 MINUTES.
        So the blow-up is in the combination, not in any one ingredient.
        Rebuilding gamma's series from these costs nothing.
        """
        cache = self.__dict__.setdefault("_cand_cache", {})
        key = (P, prec, kmax)
        if key not in cache:
            _, _, mx, mb = self.local_data(P, prec)
            keys, ser = [], []
            for i in range(len(mb)):
                s = mb[i]
                for k in range(kmax + 1):
                    keys.append((i, k))
                    ser.append(s)
                    s = s * mx
            cache[key] = (keys, ser)
        return cache[key]

    def gamma_series(self, P, prec, info):
        """The expansion at P of the gamma that hodge_filtration returned,
        rebuilt from candidate_series rather than from L.completion."""
        keys, cs = self.candidate_series(P, prec, info["kmax"])
        s = cs[0].parent().zero()
        for c, ser in zip(info["gamma_coeffs"], cs):
            if c != 0:
                s += QQ(c) * ser
        if info["gamma_const"] != 0:
            s -= cs[0].parent()(QQ(info["gamma_const"]))
        return s

    @staticmethod
    def _fil0_quadratic(Z, Om, n, g):
        r"""Omega^T Z s_2 Omega, with s_2 the projection onto Fil^0 V_dR.

        THE TERM [BDM+19] §4.5 STEP (iii) IS MISSING (E074, derived there).
        V_dR = H^1_dR(X)^* (§4.2: "let T_0,...,T_{2g+d-2} be the DUAL basis"),
        so Fil^0 V_dR = Ann(Fil^1 H^1_dR) is spanned by the LAST g dual basis
        vectors as soon as the first g omega_i are honest holomorphic
        differentials -- which is [BT] Def 2.16(1), i.e. phase4_basis().  Hence
        s_2 is the projection onto the last g coordinates, and

            Omega^T Z s_2 Omega = sum_i sum_{j >= g} Z_ij Omega_i Omega_j.

        By §4.1(b), Z_ij = 0 when i and j are both >= g, so this is a sum of
        products of a REGULAR Omega_i (i < g) with a SINGULAR Omega_j, and it
        has a principal part in general.
        """
        out = Om[0].parent().zero()
        for i in range(n):
            for j in range(g, n):
                if Z[i][j] != 0:
                    out += QQ(Z[i][j]) * Om[i] * Om[j]
        return out

    @staticmethod
    def _integrate_series(s):
        """Formal primitive of a Laurent series, constant term 0.

        The t^{-1} coefficient is DROPPED, not an error: the callers check
        separately that it vanishes, which is what step (i) is for.
        """
        F = s.parent().zero()
        if s.is_zero():
            return F
        for k in range(s.valuation(), s.prec()):
            if k != -1 and s[k] != 0:
                F += s[k] / QQ(k + 1) * s.parent().gen()**(k + 1)
        return F

    @staticmethod
    def _principal_part(s, M):
        """Coefficients of t^-M, ..., t^-1, each flattened over Q.

        At a place of degree f a coefficient is an element of the residue
        field, i.e. f rational numbers -- which is how the count comes out
        right over Q for C_4, whose D is a single place of degree 4.
        """
        if not s.is_zero() and s.prec() < 0:
            raise ArithmeticError(
                "the series is only known to O(t^%s): its principal part is "
                "not determined, so the t-adic precision is too low"
                % s.prec())
        out = []
        for k in range(-M, 0):
            c = s[k]
            out += [QQ(v) for v in
                    (c.vector() if hasattr(c, "vector") else [c])]
        return out

    @staticmethod
    def _evaluate(f, x0, y0):
        """f in L evaluated at a finite rational point (x0, y0)."""
        val = QQ(0)
        for i, c in enumerate(f.list()):
            num, den = c.numerator(), c.denominator()
            if den(x0) == 0:
                raise ArithmeticError("gamma is not regular at x = %s" % x0)
            val += QQ(num(x0)) / QQ(den(x0)) * QQ(y0)**i
        return val

    def hodge_filtration(self, Z, eta=None, prec=None, kmax=None, base=None,
                         omega_constants=None, basis=None, printed=False,
                         fil0_correction=False):
        """Steps (ii) and (iii) of [BDM+19] §4.5: g_x, then beta_Fil, gamma_Fil.

        fil0_correction=True subtracts _fil0_quadratic from g_x, i.e. solves

            g_x - Omega^T Z s_2 Omega - gamma - beta^T Omega  in  K[[t_x]]

        instead of the condition printed in step (iii).  E074 derives that the
        printed condition is INCOMPLETE and this one is right; the default is
        False only so that E068-E070 keep reproducing their recorded numbers,
        and everything downstream of E074 (padic/height.py) passes True.  The
        derivation, in one line: Fil^0 A_Z is the subbundle of A_Z on X mapping
        ISOMORPHICALLY onto Fil^0 A_1, so its generator over the Q_p-slot may
        first be reduced modulo the Fil^0 V_dR-columns of G_x s^Fil -- which is
        forced, since the poles of Omega_x live in exactly those directions --
        and those columns carry -Omega_x^T Z v in the Q_p(1)-slot.  Demanding
        the UNREDUCED column to be regular, as step (iii) does, is a strictly
        stronger and wrong condition.  True requires the basis of [BT] Def
        2.16(1) (else s_2 is not the last-g projection) and says so.

        Step (ii) integrates dg_x = Omega^T Z omega - eta place by place (see
        _dg_expr: that is what the gauge equation (18) gives, and it is not the
        expression printed in (19)); it is legitimate exactly because step (i)
        made the residue vanish, and that is CHECKED here rather than assumed.

        Step (iii) asks for constants beta and a function gamma in H^0(Y, O)
        with g_x - gamma - beta^T Omega_x in K[[t_x]] for every x in D.  The
        paper calls this a Riemann-Roch problem, and Sage's function field
        machinery for prescribed principal parts is thin over Q.  WE DO NOT NEED
        IT: with W0 = I (Tuitman's Assumption 2) the places of D all lie over
        x = infinity, so

            H^0(Y, O) = integral closure of Q[x] in L = (+)_i Q[x] b^0_i,

        the b^0_i being the integral basis auxpolys already computes.  A basis of
        H^0(Y, O) filtered by pole order is therefore just { x^k b^0_i }, and
        step (iii) becomes linear algebra on truncated Laurent expansions -- the
        same expansions the cup product and eta use.  The expansions of x and of
        the b^0_i are computed once and the candidates obtained by MULTIPLYING
        series; calling the completion map on each x^k b^0_i separately is what
        made the first version take 12 minutes on C_4 instead of seconds.

        BETA IS NOT UNIQUE, contrary to a literal reading of [BDM+19, Lemma
        4.7].  If sum_i beta_i omega_i is holomorphic its primitive has no
        principal part, so that beta is invisible to the defining condition;
        together with the constants in gamma the solution space is
        (g+1)-dimensional, which the gate measures and compares against
        holomorphic_classes().

        Two consequences, and the second is easy to get wrong.  (1) A choice
        must be made, and we make it by killing the Fil^1 component of beta in
        E064's adapted basis -- deterministic, hence reproducible across
        precisions, which the gate checks.  (2) MOVING BETA MOVES GAMMA.  In OUR
        basis a beta-direction in Fil^1 makes sum_i beta_i omega_i only
        COHOMOLOGOUS to a holomorphic differential; the difference is df with f
        in H^0(Y, O), and f has poles on D, so gamma changes by a FUNCTION and
        not merely by a constant.  This is invisible on a curve whose basis
        happens to have g literally holomorphic members -- our bielliptic test
        curve -- and visible on C_4, where E064 measured that no subset of the
        computational basis is holomorphic.  gamma is unique modulo constants
        only once beta is pinned down.

        gamma is normalised by gamma(base) = 0, base a finite rational point.

        omega_constants is a testing hook: it adds constants c to the local
        primitives Omega.  Since dg_x = Omega^T Z omega - eta the equation gains
        c^T Z omega, so g_x moves by c^T Z Omega and beta by Z^T c modulo the
        above ambiguity; the gate checks that, and checks the sharper statement
        that the corrected pair solves the unshifted problem.  (With (19) as
        printed the shift would be (2Z - Z^T)c instead, so this is also a check
        on _dg_expr.)

        Returns (beta, gamma, info), gamma an element of the function field.
        """
        C = self.C
        L, xL = C.L, C.L(C.x)
        bas = basis if basis is not None else self.H1X_basis()[0]
        n = len(bas)
        g = ZZ(C.genus)
        if fil0_correction:
            T = self.holomorphic_classes(bas)
            if T.submatrix(0, g, g, n - g) != 0 \
                    or T.submatrix(0, 0, g, g).determinant() == 0:
                raise ValueError(
                    "fil0_correction needs the basis of [BT] Def 2.16(1), in "
                    "which the FIRST g basis elements span H^0(X, Omega^1) -- "
                    "so that s_2 is the projection onto the last g coordinates. "
                    "Here the holomorphic classes are %s" % T)
        forms = [self.differential_of(v) for v in bas]
        poles = self._pole_places(forms)
        if eta is None:
            _, eta, _, _ = self.hodge_eta(Z, basis=basis)
        etaform = self.differential_of(eta) if any(c != 0 for c in eta) else None
        worst = self.worst_pole(forms, poles)
        if kmax is None:
            kmax = 3 * worst + 4
        bas0 = list(L.maximal_order().basis())
        if prec is None:
            # The t-adic precision is set by the DEEPEST principal part the
            # system has to see, and that is bounded before any expansion is
            # computed: the candidate x^k b^0_i has pole order at most
            # k*ord_P(x^-1) + max_i ord_P(1/b^0_i), and g_x, a product of two
            # primitives, at most 2*worst + 2.  Getting this from the actual
            # series instead would be circular, and guessing it generously is
            # expensive: measured on C_4's degree-4 place, one pass over the
            # six basis forms costs 12 s at precision 16, 41 s at 24 and 122 s
            # at 32.  A generous default is not free here.
            bound = 2 * worst + 2
            for P in poles:
                ox = -ZZ(L(C.x).valuation(P))
                ob = max(-ZZ(b.valuation(P)) for b in bas0)
                bound = max(bound, kmax * ox + ob)
            prec = bound + 12
        keys = [(i, k) for i in range(len(bas0)) for k in range(kmax + 1)]
        cst = omega_constants
        data = []
        for P in poles:
            if L(C.x).valuation(P) >= 0:
                raise ArithmeticError(
                    "the place %s of D does not lie over x = infinity, so "
                    "H^0(Y,O) is not the integral closure of Q[x]" % P)
            m, ser, mx, mb = self.local_data(P, prec, basis)
            Om = [self._integrate_series(s) for s in ser]
            if cst is not None:
                Om = [Om[i] + Om[i].parent()(QQ(cst[i])) for i in range(n)]
            expr = self._dg_expr(Z, ser, Om, n, printed=printed)
            if etaform is not None:
                dtdx = P.local_uniformizer().derivative()
                expr -= m(etaform / xL.differential() / dtdx)
            if not expr.is_zero() and expr[-1] != 0:
                raise ArithmeticError(
                    "dg_x has residue %s at %s: step (i) did not do its job"
                    % (expr[-1], P))
            gx = self._integrate_series(expr)
            if fil0_correction:
                gx = gx - self._fil0_quadratic(Z, Om, n, g)
            keys, cands = self.candidate_series(P, prec, kmax)
            data.append((P, Om, gx, cands))
        M = 0
        for (P, Om, gx, cands) in data:
            for s in cands + Om + [gx]:
                if not s.is_zero():
                    M = max(M, -s.valuation())
        cols = []
        for c in range(len(keys)):
            v = []
            for (P, Om, gx, cands) in data:
                v += self._principal_part(cands[c], M)
            cols.append(v)
        for i in range(n):
            v = []
            for (P, Om, gx, cands) in data:
                v += self._principal_part(Om[i], M)
            cols.append(v)
        rhs = []
        for (P, Om, gx, cands) in data:
            rhs += self._principal_part(gx, M)
        A = matrix(QQ, cols).transpose()
        sol = A.solve_right(vector(QQ, rhs))
        ker = A.right_kernel()
        nc = len(keys)
        Kb = matrix(QQ, [list(v)[nc:] for v in ker.basis()]) \
            if ker.dimension() else matrix(QQ, 0, n)
        Fil = matrix(QQ, self.holomorphic_classes(basis))
        # Does moving beta move gamma?  The ambiguity always contains the
        # constants of gamma, so the question is whether any kernel vector has
        # a NON-CONSTANT gamma-part.  E070 step 0: it does in the computational
        # basis (C_4) and must not in the basis of [BT] Def 2.16(1), because
        # the height formula uses gamma_Fil and beta_Fil separately.
        constidx = set(j for j, (i, k) in enumerate(keys)
                       if k == 0 and bas0[i].derivative().is_zero())
        kgc = all(list(v)[j] == 0
                  for v in ker.basis()
                  for j in range(nc) if j not in constidx)
        info = {"prec": prec, "kmax": kmax, "depth": M, "rank": A.rank(),
                "system": (A.nrows(), A.ncols()),
                "kernel_dim": ker.dimension(),
                "kernel_beta_is_Fil1": (Kb.row_space() == Fil.row_space()),
                "kernel_gamma_is_constant": kgc,
                "raw_beta": list(sol)[nc:], "places": poles,
                "fil0_correction": bool(fil0_correction),
                # (place, Omega, g_x as used) per place of D: E074's gate needs
                # them to check the Fil^0 subbundle condition directly.
                "local": [(P, Om, gx) for (P, Om, gx, _) in data]}
        # kill the Fil^1 component of beta: [BDM+19, Lemma 4.7]'s ambiguity
        if ker.dimension():
            S = self.adapted_change_of_basis(basis)
            coords = S.solve_left(vector(QQ, list(sol)[nc:]))
            drop = vector(QQ, list(coords)[:g] + [QQ(0)] * (n - g)) * S
            a = Kb.solve_left(drop)
            sol = sol - vector(QQ, a) \
                * matrix(QQ, [list(v) for v in ker.basis()])
        beta = list(sol)[nc:]
        gamma = L.zero()
        for c, (i, k) in zip(list(sol)[:nc], keys):
            if c != 0:
                gamma += QQ(c) * xL**k * bas0[i]
        const = QQ(0)
        if base is not None:
            const = self._evaluate(gamma, QQ(base[0]), QQ(base[1]))
            gamma -= L(const)
        # the coefficients, so that gamma's expansion can be rebuilt from
        # candidate_series instead of through L.completion (see gamma_series)
        info["gamma_coeffs"] = list(sol)[:nc]
        info["gamma_const"] = const
        return beta, gamma, info

    def symplectic_basis(self, basis=None):
        """T with T * M * T^T the standard symplectic form, M the cup product.

        Balakrishnan-Dogra-Mueller-Tuitman-Vonk Algorithm 3.12 step (2) asks for
        an INTEGRAL symplectic basis, and integrality is a statement about our
        lattice: it exists exactly when M is unimodular on the H1X_basis, which
        the gate checks rather than assumes.
        """
        M = self.cup_product_matrix(basis=basis)
        den = lcm([QQ(c).denominator() for c in M.list()])
        MZ = matrix(ZZ, M * den)
        F, T = MZ.symplectic_form()
        return M, F, T, den

    # ------------------------------------- residues via Sage (INDEPENDENT)

    def residue_matrix_sage(self, places=None):
        """Matrix of omega |-> (res_P omega)_P over the places of D, computed
        with Sage's own function-field differentials.  This is NOT Tuitman's
        Proposition 3.12/3.13; it is the independent implementation the gate
        compares against, and for now it also supplies the residues at infinity.
        """
        C = self.C
        L, xL, yL = C.L, C.L(C.x), C.y
        rL = L(C.r)
        dx = xL.differential()
        if places is None:
            places = C.L(C.r).divisor().support()
        rows = []
        for (i, d) in self.E_basis:
            om = (xL**d * yL**i / rL) * dx
            row = []
            for pl in places:
                res = om.residue(pl)
                k = pl.residue_field()[0] if isinstance(pl.residue_field(), tuple) \
                    else pl.residue_field()
                row += self._to_QQ_list(res, pl)
            rows.append(row)
        return matrix(QQ, rows).transpose(), places

    @staticmethod
    def _to_QQ_list(res, pl):
        """Coordinates of a residue-field element over QQ."""
        try:
            lst = list(res.list())
        except AttributeError:
            lst = [res]
        deg = pl.degree()
        lst = [QQ(a) for a in lst]
        return lst + [QQ(0)] * (deg - len(lst))

    def H1X(self):
        """H^1_rig(X) = ker(res (+) res_inf) / d(B), Theorem 3.11.

        Returns (dim, dim of the residue image, list of places).
        """
        M, places = self.residue_matrix_sage()
        ker = M.right_kernel()
        dM = self.d_matrix()
        im = dM.column_space()
        if not im.is_subspace(ker):
            raise ArithmeticError("exact forms have nonzero residue: bug")
        return ker.dimension() - im.dimension(), M.rank(), places
