r"""
reductions --- E048 Phase 2 (E057), first part: the pole-order
reduction at the points over x = infinity, and the residue criterion there.

Source: J. Tuitman, *Counting points on curves using a map to P^1*,
Math. Comp. 85 (2016), 961--981 (arXiv:1402.6758v2).  Section
numbers refer to the arXiv v2.  The statements used, transcribed:

  Proposition 3.4.  For every w in Q_q[x,x^{-1}]^{dx} with ord_inf(w) <= -deg(r)
  there are u, v with ord_inf(u) > ord_inf(w) and

      (sum_i w_i b^inf_i) dx/r = d(sum_i v_i b^inf_i) + (sum_i u_i b^inf_i) dx/r.

  With t = 1/x and Ginf dx = (Ginf_{-1}/t + Ginf_0 + ...) dt, and with
  m = -ord_inf(w) - deg(r) + 1 >= 1, expand w dx/r = sum_{j >= -(m+1)} wbar_j t^j dt.
  Then (Ginf_{-1} - m I) vbar = wbar_{-(m+1)} has a unique solution and one takes
      v = vbar x^m,        u = w - r (Ginf v + dv/dx).

  Remark 3.5.  When ord_inf(w) <= ord_0(W^inf) - deg(r) + 1 one has
  ord_0(v) >= -ord_0(W^inf), so sum_i v_i b^inf_i has poles only over x = infinity:
  the reduction does not disturb the finite side.

  Proposition 3.13.  For omega = (sum_i u_i(x,1/x) b^inf_i) dx/r with
  ord_inf(u) > -deg(r), put v = (x^{1-deg(r)} u)|_{x=infinity}.  Then
      res_inf(omega) = 0  <=>  the projection of v onto V_0 vanishes,
  V_0 the generalised 0-eigenspace of Ginf_{-1}.

WHY A FIXED SCHEDULE.  Proposition 3.4 as stated is adaptive: m is read off from
ord_inf(w).  Run that way the reduction is homogeneous but not additive, because
a cancellation between two inputs changes the schedule.  We instead apply the
steps for m = mmax, mmax-1, ..., 1 unconditionally.  A step whose leading
coefficient wbar_{-(m+1)} vanishes has vbar = 0 and returns u = w, so it is the
identity; hence the fixed schedule computes the same thing as the adaptive loop
and is a LINEAR operator, which is what assembling a residue matrix needs.

  Proposition 3.3.  For all l in N and every w in Q_q[x]^{dx} there are u, v
  with deg(v) < deg(r) such that

      (sum_i w_i y^i) dx/(r^l r) = d((sum_i v_i y^i)/r^l)
                                 + (sum_i u_i y^i) dx/(r^{l-1} r),

  where v solves (M/r' - l I) v = w/r' over Q_q[x]/(r) -- uniquely, since l >= 1
  is not an exponent of G dx (Proposition 2.10) -- and
      u = (w - (M - l r' I) v)/r - dv/dx.

CONTENTS.  InfiniteReduction (Propositions 3.4 and 3.13, over Q, E057);
FiniteReductionPadic (Proposition 3.3, over Q_p, E059); InfiniteReductionPadic
(Proposition 3.4 again, over Q_p, E059).  The p-adic classes duplicate rather
than generalise the rational one on purpose: the rational one is exact and is
what the E057 calibration runs on, and keeping it untouched keeps that
calibration meaningful.
"""

from sage.all import (QQ, ZZ, matrix, vector, identity_matrix, zero_matrix,
                      LaurentSeriesRing, LaurentPolynomialRing, PolynomialRing,
                      Infinity)

from padic.auxpolys import _ord_at_infinity


def ord_infinity_vector(w):
    """ord_inf of a vector of rational functions (Definition 2.11)."""
    ords = [_ord_at_infinity(f) for f in w]
    finite = [o for o in ords if o is not Infinity]
    return min(finite) if finite else Infinity


class InfiniteReduction(object):
    """Proposition 3.4 and Proposition 3.13 for one TuitmanCurve."""

    def __init__(self, C):
        self.C = C
        self.A = C.Ginf_res                      # Ginf_{-1}, over QQ
        self.dx = C.dx
        self.degr = C.degr

    # ------------------------------------------------- Laurent side at infinity

    def _series_ring(self, prec):
        return LaurentSeriesRing(QQ, 't', default_prec=prec)

    def _sub_inv_t(self, f, Lt):
        """f(x) |-> f(1/t) as a Laurent series in t."""
        t = Lt.gen()
        num, den = f.numerator(), f.denominator()
        n = sum(Lt(c) * t**(-ZZ(k)) for k, c in enumerate(num.list()))
        d = sum(Lt(c) * t**(-ZZ(k)) for k, c in enumerate(den.list()))
        return n / d

    def _wbar(self, w, j, prec=None):
        """Coefficient wbar_j of t^j dt in w dx/r.

        dx = -dt/t^2, so w dx/r = -w(1/t)/(r(1/t) t^2) dt.
        """
        if prec is None:
            prec = 2 * abs(j) + 4 * self.degr + 20
        Lt = self._series_ring(prec)
        t = Lt.gen()
        rinv = self._sub_inv_t(self.C.K(self.C.r), Lt)
        out = []
        for wi in w:
            ser = -self._sub_inv_t(wi, Lt) / (rinv * t**2)
            out.append(QQ(ser[j]))
        return vector(QQ, out)

    # ------------------------------------------------------ Proposition 3.4

    def step(self, w, m):
        """One reduction step at level m.  Returns (u, v).

        No-op (u = w, v = 0) when the leading coefficient wbar_{-(m+1)} is zero,
        which is what makes the fixed schedule linear.
        """
        C = self.C
        K = C.K
        wbar = self._wbar(w, -(m + 1))
        if wbar == 0:
            return vector(K, list(w)), vector(K, [K.zero()] * self.dx)
        S = self.A - m * identity_matrix(QQ, self.dx)
        if S.determinant() == 0:
            raise ArithmeticError(
                "det(Ginf_{-1} - %d I) = 0: Proposition 2.10 violated" % m)
        vbar = S.solve_right(wbar)
        xm = K.gen()**m
        v = vector(K, [K(c) * xm for c in vbar])
        dv = vector(K, [e.derivative() for e in v])
        u = vector(K, list(w)) - K(C.r) * (C.Ginf * v + dv)
        return u, v

    def m_min_remark35(self):
        """The lowest level m at which Remark 3.5 still applies.

        Remark 3.5's hypothesis ord_inf(w) <= ord_0(W^inf) - deg(r) + 1 reads,
        in terms of m = -ord_inf(w) - deg(r) + 1, exactly as m >= -ord_0(W^inf).
        Steps at levels m below this are outside the remark: the v they produce
        is v_bar x^m with ord_0(v) = m < -ord_0(W^inf), so sum v_i b^inf_i may
        have a pole at x = 0 and the exact form subtracted need not lie in B_0.
        """
        return max(1, -int(self.C.ord0_Winf))

    def reduce(self, w, mmin=1, mmax=None):
        """Proposition 3.4 on the fixed schedule m = mmax, ..., mmin.

        INPUT: w a list/vector of dx elements of K = QQ(x) (Laurent polynomials
        in Tuitman's setting).

        OUTPUT: (u, v, steps) with
            (sum w_i b^inf_i) dx/r = d(sum v_i b^inf_i) + (sum u_i b^inf_i) dx/r
        and ord_inf(u) > -(mmin - 1) - deg(r), i.e.

            mmin = 1                  -> ord_inf(u) > -deg(r), the hypothesis of
                                         Proposition 3.13;
            mmin = m_min_remark35()   -> ord_inf(u) > ord_0(W^inf) - deg(r) + 1,
                                         the condition defining E_infinity in
                                         Theorem 3.6, every step inside Remark 3.5.

        ``steps`` lists (m, whether the step did anything, ord_0(v)) for the
        record.
        """
        C = self.C
        K = C.K
        u = vector(K, [K(e) for e in w])
        v_tot = vector(K, [K.zero()] * self.dx)
        steps = []
        if mmax is None:
            o = ord_infinity_vector(u)
            if o is Infinity:
                return u, v_tot, steps
            mmax = -o - self.degr + 1
        for m in range(int(mmax), int(mmin) - 1, -1):
            u, v = self.step(u, m)
            acted = (v != 0)
            steps.append((m, acted, m if acted else None))
            v_tot += v
        o = ord_infinity_vector(u)
        bound = -(int(mmin) - 1) - self.degr
        if o is not Infinity and o <= bound:
            raise ArithmeticError(
                "reduction did not terminate: ord_inf(u) = %s <= %s"
                % (o, bound))
        return u, v_tot, steps

    # ----------------------------------------------------- Proposition 3.13

    def v_at_infinity(self, u):
        """v = (x^{1-deg r} u)|_{x=infinity} of Proposition 3.13."""
        Lt = self._series_ring(4 * self.degr + 20)
        t = Lt.gen()
        out = []
        for ui in u:
            ser = self._sub_inv_t(ui, Lt) * t**(self.degr - 1)
            out.append(QQ(ser[0]))
        return vector(QQ, out)

    def V0_annihilator(self):
        """Matrix P with P v = 0 <=> the projection of v onto V_0 vanishes.

        Q^dx = ker(A^dx) (+) im(A^dx) = V_0 (+) (sum of the other generalised
        eigenspaces), so the projection onto V_0 vanishes exactly on im(A^dx),
        and P may be taken to be a basis of the left kernel of A^dx.
        """
        Adx = self.A**self.dx
        left = Adx.transpose().right_kernel().basis_matrix()
        return left

    def residue_infinity_row(self, w):
        """Proposition 3.13 applied to (sum w_i b^inf_i) dx/r, after 3.4.

        Returns the coordinates of the projection of v onto V_0 (a vector that
        vanishes exactly when res_inf of the form vanishes).

        Note that this runs the schedule down to m = 1, below Remark 3.5's
        range, so the exact form subtracted may have a pole at x = 0.  That is
        harmless HERE and only here: residues are invariants of the cohomology
        class, so subtracting any exact form leaves res_inf unchanged.  The
        pipeline that reduces F_p(omega) back to a basis must instead stop at
        m_min_remark35(), where the exact form stays in B_0.
        """
        u, _, _ = self.reduce(w, mmin=1)
        return self.V0_annihilator() * self.v_at_infinity(u)

    # ------------------------------------------------------------ diagnostics

    def eigenvalue_report(self):
        """Proposition 2.10 / the proof of 3.13: the eigenvalues of Ginf_{-1}
        lie in Q cap [0,1) and the matrix is diagonalisable."""
        cp = self.A.charpoly()
        eigs = []
        for lam, mult in cp.roots(QQ):
            eigs.append((lam, mult))
        rational = sum(m for _, m in eigs) == self.dx
        in_range = all(0 <= lam < 1 for lam, _ in eigs)
        diagble = self.A.is_diagonalizable()
        return {"charpoly": cp, "eigenvalues": eigs, "all_rational": rational,
                "in_[0,1)": in_range, "diagonalisable": diagble}


# ===========================================================================
#  E059: the same two propositions over Q_p, on r-adic elements
# ===========================================================================


class FiniteReductionPadic(object):
    """Proposition 3.3 over Q_p, acting on the r-adic elements of radic.py.

    A 1-form is carried as an element sum_j a_j/r^j of R, understood to be
    multiplied by dx.  Level l+1 of the r-adic expansion is Tuitman's
    (sum_i w_i y^i) dx/(r^l r); one step moves it to level l.  Running l
    downwards to 1 leaves an element supported in j <= 1, i.e. an element of
    E_0 = {(sum_i u_i(x) y^i) dx/r}.

    THIS IS WHERE PRECISION IS LOST (the plan's risk 3).  The system is solved
    over Q_p and det(M - l r' I) mod r need not be a p-adic unit; Proposition
    3.7 bounds the loss by p^{floor(log_p(l e))}.  The observed loss is recorded
    and compared with that bound rather than assumed to be within it.
    """

    def __init__(self, RR):
        self.RR = RR
        C = RR.C
        self.C = C
        self.dx = RR.dx
        self.degr = RR.degr
        self.base = RR.base
        self.Rx = RR.Rx
        self.Ry = RR.Ry
        self.r = RR.r
        self.rprime = RR.r.derivative()
        self.M = self._M_matrix()
        self._blocks_M = [[self._mult_block(self.M[i][j])
                           for j in range(self.dx)] for i in range(self.dx)]
        self._block_rprime = self._mult_block(self.rprime)
        self._sysmat = {}
        # Diagnostics rather than assertions.  With fixed-precision arithmetic
        # there is no per-step precision to test the division by r against; the
        # honest statements are how far the reduction divides by p, and how
        # close to N the (necessarily nonzero) remainders sit once that division
        # is accounted for.  A real bug moves the second number to near 0.
        self.max_step_loss = 0
        self.min_remainder_valuation = Infinity

    # ------------------------------------------------------------- setup

    def _M_matrix(self):
        """M = r G, with polynomial entries (Proposition 2.7), over Z_p[x]."""
        C = self.C
        out = []
        for i in range(self.dx):
            row = []
            for j in range(self.dx):
                e = C.K(C.r) * C.G0[i, j]
                if e.denominator().degree() > 0:
                    raise ArithmeticError(
                        "r*G is not polynomial: Proposition 2.7 violated")
                row.append(self.RR._poly_from_QQ(e.numerator()))
            out.append(row)
        return out

    def _mult_block(self, a):
        """Matrix of multiplication by a on Q_p[x]/(r), basis 1, x, ..."""
        cols = []
        for e in range(self.degr):
            c = (a * self.Rx.gen()**e) % self.r
            lst = c.list() + [self.base(0)] * (self.degr - len(c.list()))
            cols.append(lst[:self.degr])
        return matrix(self.base, self.degr, self.degr,
                      lambda i, j: cols[j][i])

    def _system_matrix(self, ell):
        """The matrix of v |-> (M - l r' I) v on (Q_p[x]/(r))^{dx}."""
        if ell in self._sysmat:
            return self._sysmat[ell]
        n = self.dx * self.degr
        A = zero_matrix(self.base, n, n)
        for i in range(self.dx):
            for j in range(self.dx):
                blk = self._blocks_M[i][j]
                if i == j:
                    blk = blk - ell * self._block_rprime
                A.set_block(i * self.degr, j * self.degr, blk)
        self._sysmat[ell] = A
        return A

    # -------------------------------------------------------------- vectors

    def _to_vector(self, a):
        """Ry-polynomial digit -> coordinate vector of length dx*deg r."""
        out = []
        coeffs = list(self.Ry(a).list())
        coeffs += [self.Rx.zero()] * (self.dx - len(coeffs))
        for c in coeffs:
            lst = c.list() + [self.base(0)] * (self.degr - len(c.list()))
            if len(lst) > self.degr:
                raise ArithmeticError("digit of degree >= deg r: not normalised")
            out += lst[:self.degr]
        return vector(self.base, out)

    @staticmethod
    def _minval(v):
        vals = [c.valuation() for c in v if c != 0]
        return min(vals) if vals else 0

    def _from_vector(self, v):
        """Inverse of _to_vector."""
        out = self.Ry.zero()
        for i in range(self.dx):
            c = self.Rx(list(v[i * self.degr:(i + 1) * self.degr]))
            out += c * self.Ry.gen()**i
        return out

    # ----------------------------------------------------------- one step

    def step(self, w, ell):
        """One application of Proposition 3.3 at level l = ell.

        INPUT: w the digit at level ell+1 (an Ry-polynomial with coefficients of
        degree < deg r).  OUTPUT: (u, v), u the Ry-polynomial to be added at
        level ell, v the polynomial vector of the exact form.
        """
        A = self._system_matrix(ell)
        rhs = self._to_vector(w)
        sol = A.solve_right(rhs)
        # How much this step divides by p: Proposition 3.7 bounds the
        # denominator of the WHOLE reduction from level l by p^floor(log_p(l e)),
        # so this per-step figure is a diagnostic, not a budget.
        loss = max(0, self._minval(rhs) - self._minval(sol))
        self.max_step_loss = max(self.max_step_loss, loss)
        v = self._from_vector(sol)
        # u = (w - (M - l r' I) v)/r - dv/dx, the division being exact
        Nv = self.Ry.zero()
        vc = list(v.list()) + [self.Rx.zero()] * (self.dx - len(v.list()))
        for i in range(self.dx):
            s = self.Rx.zero()
            for j in range(self.dx):
                s += self.M[i][j] * vc[j]
            s -= ell * self.rprime * vc[i]
            Nv += s * self.Ry.gen()**i
        num = self.Ry(w) - Nv
        u = self.Ry.zero()
        for i, c in enumerate(list(num.list())):
            q, rem = c.quo_rem(self.r)
            # The division is exact in exact arithmetic.  Here it can only be
            # exact TO THE PRECISION THE SOLVE LEFT: if det(M - l r' I) mod r
            # is not a unit, v is known to absolute precision prec < N and the
            # remainder is noise of valuation >= prec.  Anything of valuation
            # BELOW prec is a genuine error, not a precision effect, so that is
            # what is tested.  (This distinction is the whole of risk 3: a
            # tolerance of "small" would hide bugs, a demand of "exactly zero"
            # would reject correct arithmetic.)
            for cc in rem.list():
                if cc != 0:
                    self.min_remainder_valuation = min(
                        self.min_remainder_valuation, cc.valuation() - loss)
            u += q * self.Ry.gen()**i
        for i, c in enumerate(vc):
            u -= c.derivative() * self.Ry.gen()**i
        return self.RR._clean_A(u), v

    # ------------------------------------------------------- full reduction

    def reduce(self, elts, primitives=False):
        """Reduce a list of r-adic elements to E_0 (support in j <= 1).

        The levels are processed downwards and shared across the whole list, so
        the linear system at each level is built once.  Returns the reduced
        elements; the caller turns them into E_0 coefficient vectors.

        With primitives=True also returns, for each element, the function
        f_{i,0} = sum_l (sum_k v_{l,k} y^k)/r^l of Balakrishnan-Tuitman
        Algorithm 2.18(2) -- the exact form subtracted along the way, which
        Algorithm 3.7 evaluates at the endpoints.  It is accumulated here rather
        than recomputed because each v is a by-product of a step.
        """
        RR = self.RR
        elts = [dict(e) for e in elts]
        prims = [RR.zero() for _ in elts]
        maxJ = 0
        for e in elts:
            Jr = RR.J_range(e)
            if Jr is not None:
                maxJ = max(maxJ, Jr[1])
        self.max_level = max(getattr(self, "max_level", 0), maxJ)
        for ell in range(maxJ - 1, 0, -1):
            level = ell + 1
            if not any(level in e and e[level] != 0 for e in elts):
                continue
            for k, e in enumerate(elts):
                w = e.get(level, None)
                if w is None or w == 0:
                    continue
                u, v = self.step(w, ell)
                del e[level]
                elts[k] = RR.add(e, RR.normalize({ell: u}))
                e = elts[k]
                if primitives and v != 0:
                    prims[k] = RR.add(prims[k], RR.normalize({ell: v}))
        for e in elts:
            Jr = RR.J_range(e)
            if Jr is not None and Jr[1] > 1:
                raise ArithmeticError("finite reduction did not terminate")
        return (elts, prims) if primitives else elts

    def to_E0(self, e):
        """The reduced element as a vector u with (sum_i u_i y^i) dx/r."""
        RR = self.RR
        out = [self.Rx.zero()] * self.dx
        for j, a in e.items():
            if j > 1:
                raise ArithmeticError("not reduced: digit at j = %d" % j)
            f = self.r**(1 - j)
            coeffs = list(self.Ry(a).list())
            for i, c in enumerate(coeffs):
                out[i] += c * f
        return [self.RR._clean_poly(c) for c in out]


class InfiniteReductionPadic(object):
    """Proposition 3.4 over Q_p, on vectors of Laurent polynomials.

    Same fixed schedule as the rational InfiniteReduction, and same rule as
    E057: the schedule stops at m_min = -ord_0(W^inf), inside Remark 3.5, so
    that the exact form subtracted is d of a function in B_0: it has poles
    only above x = infinity (it is not in B_inf, and need not be).  Going
    below that is legitimate only when the output is a residue, which is not
    the case here.
    """

    def __init__(self, RR):
        self.RR = RR
        C = RR.C
        self.C = C
        self.dx = RR.dx
        self.degr = RR.degr
        self.base = RR.base
        # NB (Sage 10.7): coercing a p-adic scalar into LaurentPolynomialRing
        # raises TypeError ("'NoneType' object is not subscriptable"), so every
        # Laurent polynomial below is built with the DICT constructor and no
        # expression of the form c * x^k or L(c) is used.
        self.Lx = LaurentPolynomialRing(self.base, 'x')
        self.xl = self.Lx.gen()
        self.r = self._lx_from_poly(RR.r)
        self.A = self._coerce_matrix_QQ(C.Ginf_res)
        self.rGinf = self._coerce_matrix_laurent(C.K(C.r) * C.Ginf)
        self.Winf = self._coerce_matrix_laurent(C.Winf)
        self.Winf_inv = self._coerce_matrix_laurent(C.Winf.inverse())
        self.mmin = max(1, -int(C.ord0_Winf))
        self.max_step_loss = 0
        # r*(t) = t^{deg r} r(1/t), the reverse of r; monic r makes r*(0) = 1
        self.Lt = LaurentSeriesRing(self.base, 't',
                                    default_prec=8 * self.degr + 40)
        t = self.Lt.gen()
        self.rstar = sum(self.Lt(c) * t**(self.degr - k)
                         for k, c in enumerate(RR.r.list()))

    # ------------------------------------------------------------- coercion

    def _lx(self, d):
        """A Laurent polynomial from {exponent: coefficient}.

        Coefficients that are zero to their own p-adic precision are dropped;
        see the note in radic.py.  Without this the degree of a Laurent
        polynomial, and hence ord_inf and the whole reduction schedule, is
        governed by terms that are indistinguishable from 0.
        """
        d = {k: self.RR._trunc(c) for k, c in d.items()
             if not self.RR._coeff_is_zero(c)}
        return self.Lx(d) if d else self.Lx.zero()

    def _lx_from_poly(self, f):
        return self._lx({i: c for i, c in enumerate(f.list())})

    def clean(self, f):
        """Re-build a Laurent polynomial, dropping its precision-zero terms."""
        if f == 0:
            return self.Lx.zero()
        return self._lx({k: f[k] for k in range(f.valuation(), f.degree() + 1)})

    def _coerce_matrix_QQ(self, M):
        return matrix(self.base, M.nrows(), M.ncols(),
                      [self.RR._coerce_QQ(e) for e in M.list()])

    def _coerce_matrix_laurent(self, M):
        """A matrix over QQ(x) whose entries are Laurent polynomials."""
        out = []
        for e in M.list():
            num, den = e.numerator(), e.denominator()
            if den.degree() != den.valuation():
                raise ArithmeticError(
                    "entry %s is not a Laurent polynomial in x" % e)
            k = den.valuation()
            c = den.leading_coefficient()
            d = {}
            for i, a in enumerate(num.list()):
                if a != 0:
                    d[i - k] = self.RR._coerce_QQ(QQ(a) / QQ(c))
            out.append(self._lx(d))
        return matrix(self.Lx, M.nrows(), M.ncols(), out)

    # --------------------------------------------------------------- orders

    @staticmethod
    def ord_inf(f):
        return Infinity if f == 0 else -f.degree()

    def ord_inf_vec(self, w):
        ords = [self.ord_inf(f) for f in w]
        finite = [o for o in ords if o is not Infinity]
        return min(finite) if finite else Infinity

    # ----------------------------------------------------------- one step

    def _wbar(self, w, j):
        """Coefficient of t^j dt in w dx/r, i.e. of -w(1/t) t^{deg r - 2}/r*(t)."""
        t = self.Lt.gen()
        out = []
        for f in w:
            ser = self.Lt.zero()
            if f != 0:
                for k in range(f.valuation(), f.degree() + 1):
                    c = f[k]
                    if c != 0:
                        ser += self.Lt(c) * t**(-k)
            ser = -ser * t**(self.degr - 2) / self.rstar
            out.append(ser[j])
        return vector(self.base, out)

    def step(self, w, m):
        wbar = self._wbar(w, -(m + 1))
        if all(c == 0 for c in wbar):
            return list(w), [self.Lx.zero()] * self.dx
        S = self.A - m * identity_matrix(self.base, self.dx)
        vbar = S.solve_right(wbar)
        vals_in = [c.valuation() for c in wbar if c != 0]
        vals_out = [c.valuation() for c in vbar if c != 0]
        if vals_in and vals_out:
            self.max_step_loss = max(self.max_step_loss,
                                     min(vals_in) - min(vals_out))
        v = [self._lx({m: c}) for c in vbar]
        dv = [f.derivative() for f in v]
        u = []
        for i in range(self.dx):
            s = self.Lx.zero()
            for j in range(self.dx):
                s += self.rGinf[i, j] * v[j]
            u.append(self.clean(w[i] - s - self.r * dv[i]))
        return u, v

    def reduce(self, w, primitives=False):
        """Fixed schedule m = m_max, ..., m_min (Remark 3.5's lower end).

        With primitives=True also returns f_{i,inf} = sum_i v_i b^inf_i of
        Balakrishnan-Tuitman Algorithm 2.18(3), in the b^inf basis, accumulated
        over the steps.
        """
        u = [self.clean(f) for f in w]
        vtot = [self.Lx.zero()] * self.dx
        o = self.ord_inf_vec(u)
        if o is Infinity:
            return (u, vtot) if primitives else u
        mmax = -o - self.degr + 1
        self.max_m = max(getattr(self, "max_m", 0), int(mmax))
        for m in range(int(mmax), self.mmin - 1, -1):
            u, v = self.step(u, m)
            if primitives:
                vtot = [self.clean(vtot[i] + v[i]) for i in range(self.dx)]
        return (u, vtot) if primitives else u

    # --------------------------------------------------- basis conversions

    def to_binf(self, u):
        """Coefficients in powers of y -> coefficients in the b^inf basis."""
        v = vector(self.Lx, [self._lx_from_poly(c) for c in u])
        return [self.clean(f) for f in (self.Winf_inv * v)]

    def to_powers_of_y(self, w):
        v = vector(self.Lx, list(w))
        out = [self.clean(f) for f in (self.Winf * v)]
        for f in out:
            if f != 0 and f.valuation() < 0:
                raise ArithmeticError(
                    "reduced form is not in E_0: negative power of x")
        return out
