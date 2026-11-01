r"""
auxpolys --- E048 Phase 1, first half: the auxiliary data of Tuitman's
algorithm for a curve given by a plane model.

Source: J. Tuitman, *Counting points on curves using a map to P^1*,
Math. Comp. 85 (2016), 961--981 (arXiv:1402.6758v2).  Section
numbers below refer to the arXiv v2.  Nothing here is written from memory; the
statements used are:

  Definition 2.2   Delta(x) = disc_y(Q),  r = Delta / gcd(Delta, dDelta/dx).
  Proposition 2.4  s = r / (dQ/dy) lies in A = Z_q[x,y]/(Q).
  Proposition 2.7  d(y^j) = sum_i G_{i+1,j+1} y^i dx  with  G = M/r,
                   M over Z_q[x].
  Assumption 2     the affine zero locus of Q is smooth; by the proof of
                   Prop. 2.4 this makes [1, y, ..., y^{dx-1}] an integral basis
                   for Q_q(x,y) over Q_q[x], i.e. W^0 = identity.  That is why
                   Theorem 3.6 writes E_0 and B_0 in powers of y.
  Assumption 3     a matrix W^inf in GL_{dx}(Z_q[x,x^{-1}]) whose associated
                   b^inf_j form an integral basis over Q_q[x^{-1}].
  Proposition 2.8  db^inf_j = sum_i Ginf_{i+1,j+1} b^inf_i dx, and Ginf dx has
                   at most a simple pole at x = infinity.
  Definition 2.11  ord_{x0} extended to matrices by the minimum over entries.

W^inf is *computed*, not assumed: Sage's function-field machinery returns an
integral basis at infinity, which is exactly what Assumption 3 asks for.  So
Assumption 3 is discharged by construction, as E055 anticipated.

NAMING.  Tuitman's (x, y) = (base, fibre).  For C_4 that is (t, w) of E037.
This module keeps Tuitman's names throughout.
"""

from sage.all import (QQ, FunctionField, PolynomialRing, matrix, vector,
                      identity_matrix, gcd, ZZ, Infinity)


def _ord_at_zero(f):
    """ord_{x=0} of a rational function in one variable (0 has ord +infinity)."""
    if f == 0:
        return Infinity
    num = f.numerator()
    den = f.denominator()
    return num.valuation() - den.valuation()


def _ord_at_infinity(f):
    """ord_{x=infinity}, i.e. the order in t = 1/x (0 has ord +infinity)."""
    if f == 0:
        return Infinity
    return f.denominator().degree() - f.numerator().degree()


def _matrix_ord(M, at):
    """Definition 2.11: extend an order to a matrix by the minimum over entries."""
    ords = [at(e) for e in M.list()]
    finite = [o for o in ords if o is not Infinity]
    return min(finite) if finite else Infinity


class TuitmanCurve(object):
    """All of Section 2's data for one plane model.

    INPUT: ``Qxy``, a polynomial in two variables over QQ, monic in the fibre
    variable, irreducible, of fibre-degree d_x >= 2.

    The constructor computes and stores: the function field and its genus,
    Delta and r, the finite and infinite integral bases W0 and Winf, the
    connection matrices G0 and Ginf, and the degree bounds Theorem 3.6 needs.
    It verifies, rather than assumes, the two facts the rest of the port leans
    on: that W0 is the identity (Assumption 2) and that Ginf dx has at most a
    simple pole at infinity (Proposition 2.8).
    """

    def __init__(self, Qxy, name="curve"):
        self.name = name
        P2 = Qxy.parent()
        self.xvar, self.yvar = P2.gens()
        self.Qxy = Qxy

        self.dx = Qxy.degree(self.yvar)     # degree of the map x, = deg_y Q
        self.dy = Qxy.degree(self.xvar)     # deg_x Q
        if self.dx < 2:
            raise ValueError("fibre degree d_x must be at least 2")
        if Qxy.coefficient({self.yvar: self.dx}) != 1:
            raise ValueError("Q must be monic in the fibre variable")

        # function field, genus
        self.K = FunctionField(QQ, 'x')
        self.x = self.K.gen()
        RY = PolynomialRing(self.K, 'y')
        Y = RY.gen()
        self.Qpol = self._to_Kpoly(RY, Y)
        self.L = self.K.extension(self.Qpol, 'y')
        self.y = self.L.gen()
        self.genus = ZZ(self.L.genus())

        # Definition 2.2
        Rx = PolynomialRing(QQ, 'x')
        self.Delta = Rx(self._disc_y())
        self.r = self.Delta // gcd(self.Delta, self.Delta.derivative())
        # Normalise r to be MONIC.  Definition 2.2 fixes r only up to a unit,
        # and every use of it -- omega = (...)dx/r, s = r/(dQ/dy), the ideal (r)
        # of Proposition 3.12, the expansions of Proposition 3.4 -- is either
        # invariant or scales uniformly, so this changes no dimension and no
        # kernel.  It is needed from Phase 2 on: division with remainder by r
        # over Z/p^N (the r-adic representation of Section 4.2) wants a monic
        # divisor.  The p-integrality of s under this choice is checked in
        # padic/radic.py rather than assumed.
        self.r = self.r / self.r.leading_coefficient()
        self.degr = self.r.degree()

        # integral bases: W0 (finite) and Winf (at infinity)
        self.W0 = self._basis_matrix(self.L.maximal_order().basis())
        self.Winf = self._basis_matrix(self.L.maximal_order_infinite().basis())
        self.W0_is_identity = (self.W0 == identity_matrix(self.K, self.dx))

        # connection matrices
        self.G0 = self._connection(self.W0)
        self.Ginf = self._connection(self.Winf)

        # Definition 2.11 quantities used by Theorem 3.6
        self.ord0_Winf = _matrix_ord(self.Winf, _ord_at_zero)
        self.ordinf_W0 = _matrix_ord(self.W0, _ord_at_infinity)

        # Proposition 2.8: x * Ginf must have a finite limit at infinity
        self.Ginf_res = self._residue_matrix_at_infinity()

    # ---------------------------------------------------------------- helpers

    def _to_Kpoly(self, RY, Y):
        """Move the bivariate Q into K[y], K = QQ(x)."""
        out = RY.zero()
        for (ex, ey), c in self.Qxy.dict().items():
            out += self.K(c) * self.x**ZZ(ex) * Y**ZZ(ey)
        return out

    def _disc_y(self):
        """Delta = disc_y(Q), as a polynomial in x."""
        Rx = PolynomialRing(QQ, 'x')
        RxY = PolynomialRing(Rx, 'y')
        Xg = Rx.gen()
        Yg = RxY.gen()
        q = RxY.zero()
        for (ex, ey), c in self.Qxy.dict().items():
            q += QQ(c) * Xg**ZZ(ex) * Yg**ZZ(ey)
        return q.discriminant()

    def _basis_matrix(self, bas):
        """Matrix W with b_j = sum_i W[i,j] y^i (Tuitman's convention)."""
        cols = []
        for b in bas:
            coords = b.list()
            coords = list(coords) + [self.K.zero()] * (self.dx - len(coords))
            cols.append([self.K(c) for c in coords])
        return matrix(self.K, self.dx, self.dx, lambda i, j: cols[j][i])

    def _connection(self, W):
        """G with d(b_j) = sum_i G[i,j] b_i dx, for the basis b encoded by W."""
        bas = [sum(W[i, j] * self.y**i for i in range(self.dx))
               for j in range(self.dx)]
        # derivative in the power basis, then change to the b basis
        D = []
        for b in bas:
            db = b.derivative()
            coords = list(db.list())
            coords = coords + [self.K.zero()] * (self.dx - len(coords))
            D.append([self.K(c) for c in coords])
        Dmat = matrix(self.K, self.dx, self.dx, lambda i, j: D[j][i])
        return W.inverse() * Dmat

    def _residue_matrix_at_infinity(self):
        """Ginf_{-1} of Proposition 3.13.

        With t = 1/x one has dx = -dt/t^2, so Ginf dx = -Ginf(1/t)/t^2 dt and
        the residue matrix is Ginf_{-1} = -lim_{x->infinity} x * Ginf(x).
        Proposition 2.8 guarantees the limit exists; this raises if it does not,
        which would mean the infinite basis is wrong.
        """
        M = self.x * self.Ginf
        out = []
        for e in M.list():
            num, den = e.numerator(), e.denominator()
            dn, dd = num.degree(), den.degree()
            if dn > dd:
                raise ArithmeticError(
                    "x*Ginf has a pole at infinity: Proposition 2.8 violated")
            out.append(QQ(num.leading_coefficient() / den.leading_coefficient())
                       if dn == dd else QQ(0))
        return -matrix(QQ, self.dx, self.dx, out)

    # ------------------------------------------------------------ Theorem 3.6

    def E_bounds(self):
        """Degree bounds cutting E_0 cap E_infinity out of E_0.

        A form in E_0 is (sum_i u_i(x) y^i) dx/r.  Writing the same function in
        the b^inf basis multiplies the i-th coefficient by the i-th column of
        W0 * Winf^{-1}; Theorem 3.6's condition on E_infinity is
        ord_inf(u~) > ord_0(W^inf) - deg(r) + 1.  Returns the list of maximal
        degrees for u_0, ..., u_{dx-1} (a negative entry means that coordinate
        is forced to be 0).
        """
        thresh = self.ord0_Winf - self.degr + 1     # ord_inf(u~) > thresh
        # u~ = Winf^{-1} * W0 * u, computed column by column on monomials
        T = self.Winf.inverse() * self.W0
        bounds = []
        for j in range(self.dx):
            # the j-th coordinate of u contributes column j of T
            col = [T[i, j] for i in range(self.dx)]
            shift = min([_ord_at_infinity(c) for c in col if c != 0])
            # ord_inf(x^d * col) = shift - d > thresh  <=>  d < shift - thresh
            bounds.append(shift - thresh - 1)
        return bounds

    def B_bounds(self):
        """Degree bounds cutting B_0 cap B_infinity out of B_0 (Theorem 3.6),
        where the condition is ord_inf(v~) > ord_0(W^inf)."""
        thresh = self.ord0_Winf
        T = self.Winf.inverse() * self.W0
        bounds = []
        for j in range(self.dx):
            col = [T[i, j] for i in range(self.dx)]
            shift = min([_ord_at_infinity(c) for c in col if c != 0])
            bounds.append(shift - thresh - 1)
        return bounds

    # ---------------------------------------------------------------- report

    def summary(self):
        lines = []
        lines.append("curve %s" % self.name)
        lines.append("  Q            = %s" % self.Qxy)
        lines.append("  d_x = %d, d_y = %d, genus = %d" % (self.dx, self.dy, self.genus))
        lines.append("  Delta        = %s" % self.Delta.factor())
        lines.append("  r            = %s  (degree %d)" % (self.r.factor(), self.degr))
        lines.append("  W0 = identity: %s   (Assumption 2)" % self.W0_is_identity)
        lines.append("  Winf         = %s" % self.Winf.list())
        lines.append("  ord_0(Winf)  = %s, ord_inf(W0) = %s" % (self.ord0_Winf, self.ordinf_W0))
        lines.append("  E bounds     = %s" % self.E_bounds())
        lines.append("  B bounds     = %s" % self.B_bounds())
        lines.append("  Ginf_{-1}    = %s" % self.Ginf_res.list())
        return "\n".join(lines)


def curve_from_bivariate(Qxy, name="curve"):
    return TuitmanCurve(Qxy, name=name)
