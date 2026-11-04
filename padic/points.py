r"""
points --- E048 Phase 3 (E060, E062): points of X(K), local
coordinates, and power series expansions.

Source: J. S. Balakrishnan and J. Tuitman, *Explicit Coleman integration for
curves*, Math. Comp. 89 (2020), 2965--2984 (arXiv:1710.01673v4).  Statements
used, transcribed:

  Section 3, on specifying a point.  Giving (x,y) need not determine a point,
  since several points of X may lie over a singular point of the plane model.
  A point is determined by the value of x (of 1/x if infinite) together with
  the values of the functions b^0 (b^inf if infinite).  A point is therefore
  stored as the triple (x, b, inf).

  Definition 2.10 / Remark 2.12.  A residue disk, and any point in it, is
  "bad" if it contains a very bad point; "very bad" points are those where
  r(x) = 0 or x = infinity.

  Proposition 3.2.  At a point P that is good or very bad, a local coordinate
  is  t = x - x(P)  when e_P = 1  (t = 1/x if P is infinite), and otherwise
  t = b^0_i - b^0_i(P) for some i (b^inf if P is infinite).

  Remark 3.14.  Points are taken over a totally ramified extension K of Q_p,
  so that the residue field stays F_p and Frobenius is the p-power lift.

SCOPE (E062).  FINITE points, good or very bad, over K = Q_p(p^{1/e}).  The
E060 scope (good finite points over Q_p) is the case e = 1 with r(x(P)) a unit.
Points at infinity -- t = 1/x, the b^inf basis -- are NOT implemented; they are
a gap in the port, recorded as such, and are not needed for the rational points
of C_4, whose four points at infinity are the roots of w^4 - 6w^2 + 27 and so
are not Q-rational.  The constructor refuses a point flagged as infinite, and
a point given by finite coordinates with ord_p(x(P)) < 0, which lies in an
infinite (hence bad) residue disk.  (Until 2026-11-04 the second kind was
accepted and classified as good.)

THE RAMIFIED CASE, AND THE TRAP IT CARRIES.  Over an Eisenstein extension K of
Q_p, Sage's ``valuation()`` counts powers of the uniformiser pi, not of p:
K(p).valuation() is e, not 1.  Every threshold in this module ("in the same
residue disk", "r is a unit", "zero to working precision") is a statement about
the p-adic valuation, so all of them go through ``vp()`` below, which divides
by e.  Comparing a raw valuation against 1 or N is a bug over K.
"""

from sage.all import ZZ, QQ, PowerSeriesRing, LaurentSeriesRing, ceil, log


def ramification_index(ring, p):
    """e for ring = Q_p(p^{1/e}); 1 for Q_p itself."""
    v = ring(p).valuation()
    return ZZ(v)


class CurvePoint(object):
    """A point of X(K), stored as (x, b, inf) in the sense of BT Section 3."""

    def __init__(self, RR, x, y=None, b=None, inf=False, ring=None):
        self.RR = RR
        self.C = RR.C
        self.ring = ring if ring is not None else RR.base
        self.base = self.ring                      # kept: E060's name for it
        self.e = ramification_index(self.ring, RR.p)
        self.inf = bool(inf)
        if self.inf:
            raise NotImplementedError(
                "infinite points need t = 1/x and the b^inf basis: not ported "
                "(see the SCOPE note in padic/points.py)")
        self.x = self.ring(x)
        if self.x != 0 and self.vp(self.x) < 0:
            raise NotImplementedError(
                "x(P) is not p-integral: P lies in an infinite residue disk, "
                "which needs t = 1/x and the b^inf basis: not ported "
                "(see the SCOPE note in padic/points.py)")
        if b is not None:
            self.b = [self.ring(c) for c in b]
        else:
            if y is None:
                raise ValueError("give either y or the vector b")
            yy = self.ring(y)
            # W^0 = I (Assumption 2, verified in auxpolys), so b^0_j = y^j
            self.b = [yy**j for j in range(RR.dx)]
        self.y = self.b[1] if RR.dx > 1 else self.ring(0)
        self.rval = self._r_at_x()

    # ------------------------------------------------------------- valuations

    def vp(self, a):
        """The p-adic valuation of a in K, as a rational number.

        THE POINT OF THIS METHOD: over an Eisenstein extension Sage's
        valuation() counts powers of pi, so it must be divided by e before it
        can be compared with 1 (same residue disk), 0 (unit) or N (zero to
        working precision).  Nothing in this module compares a raw valuation.
        """
        if a == 0:
            from sage.all import infinity
            return infinity
        return QQ(a.valuation()) / self.e

    def _r_at_x(self):
        v = self.ring(0)
        for k, c in enumerate(self.RR.r.list()):
            v += self.ring(c) * self.x**k
        return v

    # --------------------------------------------------------- classification

    def is_infinite(self):
        return self.inf

    def is_very_bad(self):
        """r(x(P)) = 0 or P infinite (Remark 2.12)."""
        return self.inf or self.rval == 0

    def is_bad(self):
        """In a bad residue disk: ord_p(r(x(P))) > 0, or P is infinite.

        x(P) is integral here: a point given by finite coordinates with
        ord_p(x(P)) < 0 lies in an infinite (hence bad) disk, which is out of
        scope, and the constructor refuses it (until 2026-11-04 it was
        accepted, and this test then called it good).

        The threshold is ord_p > 0 and NOT ord_p >= 1: the residue field of
        K = Q_p(p^{1/e}) is still F_p, so the residue disks are cut out by the
        maximal ideal (pi), and an element of p-adic valuation 1/e already
        reduces to zero.  Over Q_p the two readings agree, which is why E060
        could not tell them apart -- and why the E062 gate caught this at once
        as soon as a point of valuation 2/23 had to be recognised as lying in
        the disk of a very bad point.
        """
        if self.inf:
            return True
        if self.rval == 0:
            return True
        return self.vp(self.rval) > 0

    def is_good(self):
        return not self.is_bad()

    def dQ_dy_is_unit(self):
        """Whether x - x(P) is a local coordinate at P (Proposition 3.2).

        dQ/dy(P) a unit means the plane model is unramified over x = x(P) at P
        AND stays so mod p, which is what the Newton iteration for y(t) needs.
        At a good point this always holds (r(x(P)) a unit forces the fibre to
        stay separable).  At a very bad point it is exactly the case e_P = 1.
        The decision is made here, once, and every caller reads it from here.
        """
        d = self._dQ_dy()
        return d != 0 and self.vp(d) <= 0

    def _dQ_dy(self):
        v = self.ring(0)
        for (ex, ey), c in self.C.Qxy.dict().items():
            if ey > 0:
                v += self.ring(self.RR._coerce_QQ(c)) * ZZ(ey) \
                    * self.x**ZZ(ex) * self.y**(ZZ(ey) - 1)
        return v

    def _dQ_dx(self):
        v = self.ring(0)
        for (ex, ey), c in self.C.Qxy.dict().items():
            if ex > 0:
                v += self.ring(self.RR._coerce_QQ(c)) * ZZ(ex) \
                    * self.x**(ZZ(ex) - 1) * self.y**ZZ(ey)
        return v

    def on_curve(self):
        """Q(x(P), y(P)) = 0 to working precision."""
        v = self.ring(0)
        for (ex, ey), c in self.C.Qxy.dict().items():
            v += self.ring(self.RR._coerce_QQ(c)) * self.x**ZZ(ex) * self.y**ZZ(ey)
        return v == 0 or self.vp(v) >= self.RR.N

    def same_disk(self, other):
        """P and Q lie in the same residue disk (both finite here)."""
        if self.inf != other.inf:
            return False
        if self.vp(self.x - other.x) <= 0:
            return False
        return all(self.vp(a - b) > 0 for a, b in zip(self.b, other.b))

    def change_ring(self, ring):
        """The same point, its coordinates moved into a larger ring."""
        return CurvePoint(self.RR, ring(self.x), y=ring(self.y),
                          inf=self.inf, ring=ring)

    def __repr__(self):
        return "CurvePoint(x=%s, y=%s%s)" % (
            self.x, self.y, ", infinite" if self.inf else "")


def _eval_Q(RR, xv, yv, ring, dy=False):
    """Q(xv, yv), or dQ/dy there, in the given ring."""
    v = ring(0)
    for (ex, ey), c in RR.C.Qxy.dict().items():
        cc = ring(RR._coerce_QQ(c))
        if not dy:
            v += cc * xv**ZZ(ex) * yv**ZZ(ey)
        elif ey > 0:
            v += cc * ZZ(ey) * xv**ZZ(ex) * yv**(ZZ(ey) - 1)
    return v


def teichmuller_point(P, iterations=None):
    r"""The unique point of P's residue disk fixed by Tuitman's Frobenius lift.

    [BDM+19] \S5.2 evaluates the Frobenius structure at "the unique Teichmuller
    point in ]x[" and leaves it at that.  For Tuitman's lift there is nothing to
    solve: phi is given by phi^*x = x^p and phi^*y = beta with
    Q^sigma(x^p, beta) = 0 (Theorem 2.6, padic/froblift.py), so

      [T]  Let P be a GOOD point whose residue point lies in X(F_p) and at which
      dQ/dy is a unit.  Put a = lim_{k} x(P)^{p^k} (the Teichmuller lift of the
      residue of x(P)) and let b be the unique root of Q(a, -) reducing to the
      residue of y(P).  Then (a,b) is the unique phi-fixed point of ]P[.

      Proof.  The x-coordinate of a fixed point satisfies x^p = x, and in a
      residue disk of Z_p (residue field F_p) that equation has the single
      solution a; the iteration converges to it because x(P)^{p^k} = a mod
      p^{k+1} (for x(P) in Z_p; over a ramified K the valuation of the
      difference still grows without bound).  The fibre of the disk over x = a
      is the single point (a,b), since dQ/dy(P) a unit makes Q(a,-) have
      exactly one root in the disk (Hensel).  So there is at most one fixed
      point and it can only be (a,b).  It IS fixed: at a good point x(P) is
      integral and r(x(P)) a unit, so every element of R^dagger converges at
      P and evaluation is a ring homomorphism on R^dagger (cf. the proof of
      [BT] Prop 4.5), so applying it to the identity Q^sigma(x^p, beta) = 0
      gives Q(a^p, beta(a,b)) = Q(a, beta(a,b)) = 0;
      and beta = y^p mod p, so beta(a,b) = b^p = b in the residue field, the
      residue of b lying in F_p.  Hence beta(a,b) is a root of Q(a,-) in the
      disk, so equals b.  QED

    Nothing here calls phi, which is why the gate can afford to CHECK phi-
    fixedness afterwards as an independent statement rather than as a tautology.

    The hypotheses are enforced: a point of a bad disk, or one where dQ/dy is
    not a unit, is refused rather than approximated.  The residue point being
    F_p-rational is not checked directly -- it is implied for every point of
    X(Q_p), which is the only case Phase 4 needs -- but a failure would show up
    at once as x(P)^{p^k} leaving the disk, and that IS checked.
    """
    RR = P.RR
    K = P.ring
    if not P.is_good():
        raise ValueError(
            "%s is in a bad residue disk: the Teichmuller point of such a disk "
            "is not reached by this construction (and f, g, h need not converge "
            "there anyway)" % P)
    if not P.dQ_dy_is_unit():
        raise ValueError(
            "dQ/dy is not a unit at %s, so the fibre of the disk over x = a is "
            "not a single point" % P)
    k = ZZ(iterations) if iterations is not None else ZZ(RR.N) + 2
    a = K(P.x)
    for _ in range(k):
        anew = a**RR.p
        d = anew - a
        a = anew
        if d == 0 or QQ(d.valuation()) / P.e >= RR.N:
            break
    # In the disk of 0 the iteration produces x^(p^k), which is a legitimate
    # p-adic number of enormous valuation rather than the zero it converges to;
    # left as it stands it makes x_0 differ from the Teichmuller point by
    # something invisible to the working precision but visible to ==.
    if a != 0 and QQ(a.valuation()) / P.e >= RR.N:
        a = K(0)
    b = K(P.y)
    for _ in range(k):
        Qv = _eval_Q(RR, a, b, K)
        Dv = _eval_Q(RR, a, b, K, dy=True)
        if Dv == 0 or QQ(Dv.valuation()) / P.e > 0:
            raise ArithmeticError(
                "dQ/dy left the unit group during the Hensel iteration at %s" % P)
        b = b - Qv / Dv
    out = CurvePoint(RR, a, y=b, inf=False, ring=K)
    if not P.same_disk(out):
        raise ArithmeticError(
            "the Teichmuller iteration left the residue disk of %s: its residue "
            "point is not F_p-rational" % P)
    if not out.on_curve():
        raise ArithmeticError("the Teichmuller point is not on the curve")
    return out


class LocalExpansion(object):
    """A local coordinate t at a finite point P and the series x(t), b(t).

    Two cases, decided by CurvePoint.dQ_dy_is_unit() and never guessed:

      dQ/dy(P) a unit.  Proposition 3.2 gives t = x - x(P), so x(t) = x(P) + t
      and the work is y(t): the root of Q(x(P)+t, -) reducing to y(P), by
      Newton iteration.  This covers every GOOD point (E060's whole scope), and
      also those very bad points that are unramified.

      dQ/dy(P) not a unit.  Then e_P >= 2 (or the fibre degenerates mod p) and
      x - x(P) is not a uniformiser; Proposition 3.2 sends us to
      t = b^0_i - b^0_i(P), and with W^0 = I we take i = 1, i.e. t = y - y(P),
      solving for x(t) by Newton instead.  This is legitimate exactly when
      dQ/dx(P) is a unit: x is then an analytic function of y near P, so
      y - y(P) generates the maximal ideal.  The unit condition is CHECKED, not
      assumed, and a point where both partials fail is refused rather than
      guessed at.

    In the second case dx = x'(t) dt is not dt, so series_of_form multiplies by
    x'(t); in the first case x'(t) = 1 and the formula degenerates to E060's.

    ALGORITHM 3.4(1) IS ENFORCED, NOT ASSUMED: an expansion may be taken at a
    good point or at a very bad point, never at a bad-but-not-very-bad one.  In
    a bad disk the caller must first find the very bad point -- which is the
    whole content of that step, and silently expanding at the wrong point of a
    bad disk would lose precision without any symptom.

    The defining equation Q(x(t), y(t)) = 0 is verified by residual(), not
    assumed, in both cases.
    """

    def __init__(self, P, tprec, ring=None):
        RR = P.RR
        self.P = P if ring is None else P.change_ring(ring)
        self.RR = RR
        if self.P.is_bad() and not self.P.is_very_bad():
            raise ValueError(
                "%s is bad but not very bad: Algorithm 3.4(1) says to expand "
                "at the very bad point of its residue disk" % self.P)
        self.ring = self.P.ring
        self.base = self.ring                      # kept: E060's name for it
        self.e = self.P.e
        self.tprec = ZZ(tprec)
        self.S = PowerSeriesRing(self.ring, 't', default_prec=self.tprec + 1)
        self.L = LaurentSeriesRing(self.ring, 't', default_prec=self.tprec + 1)
        self.t = self.S.gen()
        self.x_is_coordinate = self.P.dQ_dy_is_unit()
        if self.x_is_coordinate:
            self.xt = self.S(self.P.x) + self.t
            self.yt = self._solve(self.xt, self.S(self.P.y), unknown='y')
        else:
            d = self.P._dQ_dx()
            if d == 0 or self.P.vp(d) > 0:
                raise ArithmeticError(
                    "neither partial of Q is a unit at %s: the reduction of "
                    "the plane model is singular there, which this port does "
                    "not handle" % self.P)
            self.yt = self.S(self.P.y) + self.t
            self.xt = self._solve(self.yt, self.S(self.P.x), unknown='x')
        self.bt = [self.yt**j for j in range(RR.dx)]
        self.dxdt = self.xt.derivative()

    # --------------------------------------------------------------- solving

    def _Q_and_deriv(self, xser, yser, unknown):
        """Q(xser, yser) and its partial in the unknown variable."""
        C = self.RR.C
        Qv = self.S.zero()
        Dv = self.S.zero()
        for (ex, ey), c in C.Qxy.dict().items():
            cc = self.ring(self.RR._coerce_QQ(c))
            Qv += cc * xser**ZZ(ex) * yser**ZZ(ey)
            if unknown == 'y' and ey > 0:
                Dv += cc * ZZ(ey) * xser**ZZ(ex) * yser**(ZZ(ey) - 1)
            if unknown == 'x' and ex > 0:
                Dv += cc * ZZ(ex) * xser**(ZZ(ex) - 1) * yser**ZZ(ey)
        return Qv, Dv

    def _solve(self, known, start, unknown):
        """Newton iteration for the unknown series, starting from a constant."""
        u = start
        steps = ZZ(ceil(log(float(max(self.tprec, 2)), 2))) + 2
        for _ in range(steps):
            if unknown == 'y':
                Qv, Dv = self._Q_and_deriv(known, u, 'y')
            else:
                Qv, Dv = self._Q_and_deriv(u, known, 'x')
            if Dv[0] == 0 or self.P.vp(Dv[0]) > 0:
                raise ArithmeticError(
                    "dQ/d%s is not a unit at %s: the local coordinate chosen "
                    "is wrong" % (unknown, self.P))
            u = u - Qv / Dv
            u = u.add_bigoh(self.tprec + 1)
        return u

    def residual(self):
        """The p-adic valuation of Q(x(t), y(t)) -- the check on the series."""
        Qv, _ = self._Q_and_deriv(self.xt, self.yt, 'y')
        vals = [self.P.vp(c) for c in Qv.list() if c != 0]
        return min(vals) if vals else self.RR.N

    # ------------------------------------------------------------ evaluation

    def t_of(self, Q):
        """The local coordinate of a point Q in the same residue disk."""
        Q = Q if Q.ring is self.ring else Q.change_ring(self.ring)
        if not self.P.same_disk(Q):
            raise ValueError("%s is not in the residue disk of %s" % (Q, self.P))
        return (Q.x - self.P.x) if self.x_is_coordinate else (Q.y - self.P.y)

    def point_at(self, tval):
        """The point of the residue disk with local coordinate t = tval.

        Built from the series, so it is only as good as they are -- but the
        resulting point is checked against Q(x,y) = 0 independently by
        CurvePoint.on_curve().
        """
        tval = self.ring(tval)
        if tval != 0 and self.P.vp(tval) <= 0:
            raise ValueError("t = %s is not inside the residue disk" % tval)
        return CurvePoint(self.RR, self.xt(tval), y=self.yt(tval),
                          inf=self.P.inf, ring=self.ring)

    def series_of_form(self, coeffs):
        """omega = (sum_i u_i(x) b^0_i) dx/r  as a Laurent series g(t) with
        omega = g(t) dt.

        ``coeffs`` is the list of u_i as polynomials over the Q_p base ring.
        Two things differ from E060: dx = x'(t) dt need not be dt, and r(x(t))
        may vanish at t = 0, so the quotient is taken in the Laurent series
        ring.  The pole order is reported by the caller through g.valuation().
        """
        num = self.S.zero()
        for i, u in enumerate(coeffs):
            if u == 0:
                continue
            us = self.S.zero()
            for k, c in enumerate(u.list()):
                if c != 0:
                    us += self.ring(c) * self.xt**k
            num += us * self.bt[i]
        den = self.S.zero()
        for k, c in enumerate(self.RR.r.list()):
            if c != 0:
                den += self.ring(c) * self.xt**k
        num = num * self.dxdt
        if den == 0:
            raise ArithmeticError("r(x(t)) is identically zero")
        return self.L(num) / self.L(den)
