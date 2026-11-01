r"""
radic --- E048 Phase 2 (E057), second part: the ring
R = Z_q[x, y, 1/r]/(Q) in the r-adic representation of Tuitman's Section 4.2.

Source: J. Tuitman, *Counting points on curves using a map to P^1*,
Math. Comp. 85 (2016), 961--981 (arXiv:1402.6758v2).  Section 4.2
represents elements of R and S = Z_q[x, 1/r] as

    sum_{j in J} a_j(x, y) / r^j,     J subset Z finite,

with a_j of degree < d_x in y and every coefficient in x of degree < deg(r).
Negative j carry the polynomial part (r^{|j|} is a polynomial), so this ONE
representation covers all of Z_q[x, y, 1/r]/(Q); there is no separate polynomial
case.  Proposition 2.12 bounds |min J| and |max J| for the objects the algorithm
actually builds, which is why this normal form is the right one to carry: the
degree bounds of the paper are statements about these digits.

n = 1 ONLY.  This module works over Z_p (q = p, sigma = identity).  Tuitman's
algorithm is written for q = p^n and a Frobenius lift that is sigma-semilinear;
everything below that would need sigma is marked, but sigma is not implemented.
Our curves -- C_4 and the hyperelliptic calibration curves -- are curves over Q
reduced mod p, so n = 1 is what the project needs.  This is a gap in the port
and is recorded as such.

PRECISION.  The default base ring is Zp(p, N, 'capped-abs'): fixed modulus p^N
with Sage tracking the precision, which is what Tuitman's Magma code does by
hand.  Nothing in the Frobenius lift divides by p, so Z_p suffices here; the
reductions of Proposition 3.3/3.4 do divide, and E059 passes a Q_p base ring in.
"""

from sage.all import ZZ, QQ, Zp, PolynomialRing, ceil, log


class RAdicRing(object):
    """R = Z_p[x, y, 1/r]/(Q) in the r-adic normal form of Section 4.2.

    An element is a dict {j: a_j}, a_j a polynomial in y of degree < d_x whose
    coefficients are polynomials in x of degree < deg(r).  The dict is kept
    normalised: no zero digits.
    """

    def __init__(self, C, p, N, base=None):
        self.C = C
        self.p = ZZ(p)
        self.N = ZZ(N)
        self.base = base if base is not None else Zp(p, prec=N, type='capped-abs')
        self.Rx = PolynomialRing(self.base, 'x')
        self.Ry = PolynomialRing(self.Rx, 'y')
        self.x = self.Rx.gen()
        self.y = self.Ry.gen()
        self.dx = C.dx
        self.degr = C.degr

        self.r = self._poly_from_QQ(C.r)
        if not self.r.is_monic():
            raise ValueError("r must be monic (see auxpolys); got %s" % self.r)
        self.Qy = self._bivariate_to_Ry(C.Qxy)
        self.s = self._compute_s()
        self._xp_cache = {}

    # ------------------------------------------------------------ coercions

    def _coerce_QQ(self, c):
        c = QQ(c)
        if c.denominator() % self.p == 0:
            raise ArithmeticError(
                "coefficient %s is not p-integral for p = %s" % (c, self.p))
        return self.base(c)

    def _poly_from_QQ(self, f):
        return self.Rx([self._coerce_QQ(c) for c in f.list()])

    def _bivariate_to_Ry(self, Qxy):
        """The plane model as an element of Rx[y], monic of degree d_x."""
        xv, yv = self.C.xvar, self.C.yvar
        out = self.Ry.zero()
        for (ex, ey), c in Qxy.dict().items():
            out += self._coerce_QQ(c) * self.x**ZZ(ex) * self.y**ZZ(ey)
        return out

    def _compute_s(self):
        """s = r/(dQ/dy), an element of A by Proposition 2.4.

        Computed over Q in the function field, then checked to be polynomial in
        x (Proposition 2.4) and p-integral (which the monic normalisation of r
        does not guarantee a priori, so it is verified rather than assumed).
        """
        C = self.C
        L = C.L
        dQ = C.Qxy.derivative(C.yvar)
        num = L.zero()
        for (ex, ey), c in dQ.dict().items():
            num += QQ(c) * L(C.x)**ZZ(ex) * C.y**ZZ(ey)
        sQ = L(C.r) / num
        coeffs = list(sQ.list()) + [C.K.zero()] * (self.dx - len(sQ.list()))
        out = self.Ry.zero()
        for k, c in enumerate(coeffs):
            if c.denominator().degree() > 0:
                raise ArithmeticError(
                    "s = r/(dQ/dy) is not integral: Proposition 2.4 violated")
            out += self._poly_from_QQ(c.numerator()) * self.y**k
        return out

    # ------------------------------------------------------- normal form

    def _reduce_modQ(self, f):
        """Reduce a polynomial in y modulo Q (monic, so this is exact)."""
        return f % self.Qy if f.degree() >= self.dx else f

    # THE WORKING MODULUS MUST BE IMPOSED EXPLICITLY, AND ZERO IS A VALUATION
    # TEST, NOT is_zero().  Tuitman computes modulo p^N throughout.  Over
    # Zp(p, N, 'capped-abs') that is automatic: anything of valuation >= N *is*
    # zero.  Over Q_p -- which the reductions need, because they divide -- it is
    # not: p^N u is a perfectly good nonzero element, the tail terms of the
    # Newton iteration never die, and the r-adic support grows without bound
    # (measured: max J = 698 where Proposition 2.12 allows at most 77).
    #
    # Hence: a coefficient counts as zero exactly when its VALUATION is >= N.
    # Sage's is_zero() must not be used for this, because on capped-relative
    # elements it answers relative to the element's own tracked precision, and
    # that precision decays step by step through the reductions in a way the
    # mathematics does not (Proposition 3.7 bounds the denominator of the whole
    # composite reduction, not of each step).  Trusting it makes correct values
    # test as zero: at p = 5 on C_4 it drove Phi to the zero matrix.  The base
    # ring used by E059 is therefore Qp(p, N, 'floating-point'), fixed relative
    # precision with no decay, which is the arithmetic model the paper assumes.

    def _trunc(self, a):
        if a == 0:
            return a
        try:
            v = a.valuation()
        except AttributeError:
            return a
        return self.base.zero() if v >= self.N else a

    def _coeff_is_zero(self, a):
        if a == 0:
            return True
        try:
            return a.valuation() >= self.N
        except AttributeError:
            return False

    def _clean_poly(self, c):
        lst = [self._trunc(a) for a in self.Rx(c).list()]
        while lst and self._coeff_is_zero(lst[-1]):
            lst.pop()
        return self.Rx(lst)

    def _clean_A(self, a):
        lst = [self._clean_poly(c) for c in self.Ry(a).list()]
        while lst and lst[-1] == 0:
            lst.pop()
        return self.Ry(lst)

    def normalize(self, d):
        """Base-r expansion of every digit; drops zero digits."""
        out = {}
        for j, a in d.items():
            a = self._clean_A(self._reduce_modQ(self.Ry(a)))
            if a == 0:
                continue
            for k, c in enumerate(a.list()):
                c = self._clean_poly(c)
                i = 0
                while c != 0:
                    c, rem = c.quo_rem(self.r)
                    c = self._clean_poly(c)
                    rem = self._clean_poly(rem)
                    if rem != 0:
                        key = j - i
                        cur = out.get(key, self.Ry.zero())
                        out[key] = cur + rem * self.y**k
                    i += 1
        cleaned = {j: self._clean_A(a) for j, a in out.items()}
        return {j: a for j, a in cleaned.items() if a != 0}

    # ------------------------------------------------------------ elements

    def zero(self):
        return {}

    def one(self):
        return {0: self.Ry.one()}

    def from_A(self, a, j=0):
        """The element a(x,y)/r^j for a in Rx[y]."""
        return self.normalize({j: self.Ry(a)})

    def r_power(self, j):
        """1/r^j (j may be negative, giving the polynomial r^{|j|})."""
        return self.normalize({j: self.Ry.one()})

    def add(self, a, b):
        out = dict(a)
        for j, c in b.items():
            out[j] = self._clean_A(out.get(j, self.Ry.zero()) + c)
        return {j: c for j, c in out.items() if c != 0}

    def neg(self, a):
        return {j: -c for j, c in a.items()}

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def mul(self, a, b):
        out = {}
        for j, aj in a.items():
            for l, bl in b.items():
                prod = self._clean_A(self._reduce_modQ(aj * bl))
                if prod == 0:
                    continue
                out[j + l] = out.get(j + l, self.Ry.zero()) + prod
        return self.normalize(out)

    def scalar(self, c, a):
        out = {j: self._clean_A(c * v) for j, v in a.items()}
        return {j: v for j, v in out.items() if v != 0}

    def power(self, a, n):
        if n < 0:
            raise ValueError("no negative powers in R")
        out = self.one()
        base = a
        while n:
            if n & 1:
                out = self.mul(out, base)
            base = self.mul(base, base)
            n >>= 1
        return out

    def is_zero(self, a):
        return all(self._clean_A(c) == 0 for c in a.values())

    def equal(self, a, b):
        return self.is_zero(self.sub(a, b))

    def support(self):
        raise NotImplementedError

    @staticmethod
    def J_range(a):
        """(min J, max J) of the r-adic support, or None for 0."""
        keys = [j for j, c in a.items() if c != 0]
        if not keys:
            return None
        return (min(keys), max(keys))

    def max_coeff_degree(self, a):
        """Largest degree in x occurring in a digit (should be < deg r)."""
        best = -1
        for c in a.values():
            for cc in c.list():
                best = max(best, cc.degree())
        return best

    # ------------------------------------------------- the substitution x^p

    def subst_xp_poly(self, f):
        """f(x) |-> f(x^p), as a normalised element (digits at j <= 0)."""
        key = f
        if key in self._xp_cache:
            return self._xp_cache[key]
        g = self.Rx.zero()
        xp = self.x**self.p
        for k, c in enumerate(f.list()):
            if c != 0:
                g += c * xp**k
        out = self.normalize({0: self.Ry(g)})
        self._xp_cache[key] = out
        return out

    def subst_xp_A(self, a, beta):
        """a(x, y) |-> a^sigma(x^p, beta).  With n = 1, sigma is the identity."""
        out = self.zero()
        bpow = self.one()
        for k, c in enumerate(self.Ry(a).list()):
            if c != 0:
                out = self.add(out, self.mul(self.subst_xp_poly(c), bpow))
            bpow = self.mul(bpow, beta)
        return out

    def frobenius_apply(self, a, alpha, beta):
        """F_p(a) for a in R, given alpha = F_p(1/r) and beta = F_p(y).

        F_p(sum_j a_j/r^j) = sum_j a_j^sigma(x^p, beta) * F_p(1/r^j), and
        F_p(1/r^j) is alpha^j for j > 0 and r(x^p)^{-j} for j < 0.
        """
        rxp = self.subst_xp_poly(self.r)
        out = self.zero()
        for j, aj in a.items():
            t = self.subst_xp_A(aj, beta)
            if j > 0:
                t = self.mul(t, self.power(alpha, j))
            elif j < 0:
                t = self.mul(t, self.power(rxp, -j))
            out = self.add(out, t)
        return out

    # ------------------------------------------------------------ evaluation

    def evaluate(self, a, x0, y0, ring=None):
        """The value of sum_j a_j(x,y)/r^j at (x0, y0), optionally in an
        extension ring K = Q_p(p^{1/e}).

        THE CONVERGENCE CONDITION IS THE PAPER'S, NOT "r IS A UNIT".
        Balakrishnan-Tuitman Proposition 4.3 with Remark 4.4: the functions
        f_{i,0} converge exactly outside the closed disk ord_p(r(x)) >= 1/p.
        Every good point satisfies this with room to spare (ord_p(r) = 0), and
        so does a point of a bad disk that has been pushed far enough away from
        the very bad point -- which is the whole reason Algorithm 3.12 works in
        a ramified extension.  The condition is checked here rather than left
        to the caller; what is NOT claimed is the precision of the answer,
        which Propositions 4.5 and 4.6 bound and the caller reports.

        Over an Eisenstein extension valuation() counts powers of pi, so it is
        divided by e before being compared with 1/p.
        """
        R = ring if ring is not None else self.base
        e = ZZ(R(self.p).valuation())
        x0, y0 = R(x0), R(y0)
        rv = R(0)
        for k, c in enumerate(self.r.list()):
            rv += R(c) * x0**k
        if rv == 0 or QQ(rv.valuation()) / e >= QQ(1) / self.p:
            raise ArithmeticError(
                "ord_p(r(x)) >= 1/p at the point: the functions f_i need not "
                "converge there (BT Prop 4.3, Rmk 4.4).  In a bad disk, move "
                "to a point over Q_p(p^{1/e}) with e > p e_P first "
                "(Algorithm 3.12)")
        tot = R(0)
        rinv = R(1) / rv
        for j, aj in a.items():
            v = R(0)
            for i, c in enumerate(self.Ry(aj).list()):
                cv = R(0)
                for k, cc in enumerate(c.list()):
                    cv += R(cc) * x0**k
                v += cv * y0**i
            tot += v * rinv**j if j >= 0 else v * rv**(-j)
        return tot

    # --------------------------------------------------------------- report

    def summary(self):
        return ("R-adic ring for %s: p = %s, N = %s, base = %s, d_x = %d, "
                "deg r = %d" % (self.C.name, self.p, self.N, self.base,
                                self.dx, self.degr))
