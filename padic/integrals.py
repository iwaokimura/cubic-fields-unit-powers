r"""
integrals --- E048 Phase 3 (E060, E062): tiny integrals and
Coleman integrals, including endpoints in bad residue disks.

Source: J. S. Balakrishnan and J. Tuitman, *Explicit Coleman integration for
curves*, Math. Comp. 89 (2020), 2965--2984 (arXiv:1710.01673v4).

  Definition 3.3.  A tiny integral is a Coleman integral whose endpoints lie in
  the same residue disk.

  Algorithm 3.4.  If the disk is bad, find the very bad point P' in it;
  otherwise P' = P.  Compute a local coordinate t and the expansions x(t), b(t)
  at P'.  Then  int_P^Q omega = int_{t(P)}^{t(Q)} omega(t),  the Laurent
  expansion omega(t) being read off from x(t), b(t).  Since omega is of the
  second kind the coefficient of t^{-1} dt vanishes.

  Remark 3.5.  Tiny integrals do not use the action of Frobenius.  "This can be
  a useful consistency check for the integration algorithms that follow, which
  do use the computation of the action of Frobenius."  That is exactly the role
  they play here: E059's Phi and this module share no step.

  Proposition 4.1 and Remark 4.2 (precision).  With g accurate to p-adic
  precision N, truncated modulo t^l, and omega = g(t)dt with g having a pole of
  order k, the tiny integral is correct to precision min(nu1, nu2, nu3) with
      nu1 = 1/e + min_{i >= l} { i/e - floor(log_p(i+1)) },
      nu2 = N + min_{0 <= i <= l-1} { i/e - floor(log_p(i+1)) },
      nu3 = N - k max(ord_p t(P), ord_p t(Q)) - floor(log_p(k-1)).
  Since nu2 <= N always, l is taken minimal with nu1 >= N.

  Algorithm 3.7 (E061, class ColemanIntegrals).  For endpoints in different
  residue disks, with the functions f_i of Definition 2.17,
      sum_j (Phi - I)_ij int_P^Q omega_j
          = f_i(P) - f_i(Q) - int_P^{F_p(P)} omega_i - int_{F_p(Q)}^Q omega_i.
  Remark 3.11: this applies verbatim to points over Q_p(p^{1/e}).

  Algorithm 3.12 (E062, ColemanIntegrals.coleman_integrals_general).  When P
  or Q is bad, take P', Q' in their residue disks where f_1, ..., f_2g do
  converge, integrate between those by Algorithm 3.7, and correct by the tiny
  integrals int_P^{P'} and int_{Q'}^Q.  By Remark 4.4 the new points have to
  live over Q_p(p^{1/e}) with e > p e_P.

SCOPE: finite endpoints.  Points at infinity are not ported (see points.py).
"""

from sage.all import ZZ, QQ, Qp, PolynomialRing, floor, log, matrix, vector

from padic.points import CurvePoint, LocalExpansion, ramification_index


# --------------------------------------------------------------- precision

def _floorlog(n, p):
    """floor(log_p(n)) for an integer n >= 1, exactly.  (Until 2026-11-04 this
    was floor(log(float(n), float(p))), which is m - 1 at some exact powers
    n = p^m: log(3.0**5, 3.0) = 4.999...)"""
    n, p = ZZ(n), ZZ(p)
    m, q = ZZ(0), p
    while q <= n:
        m += 1
        q *= p
    return m


def _phi(i, e, p):
    """i/e - floor(log_p(i+1)), the summand of Proposition 4.1."""
    return QQ(i) / e - _floorlog(i + 1, p)


def _phi_min_from(l, e, p, mmax=200):
    """min_{i >= l} phi(i), computed exactly rather than by scanning.

    phi decreases only where floor(log_p(i+1)) jumps, i.e. at i + 1 = p^m,
    i = p^m - 1, and increases by 1/e at every other step; so the minimum over
    i >= l is attained at i = l or at one of those jump points, and
    phi(p^{m+1} - 1) - phi(p^m - 1) = p^m (p - 1)/e - 1 is >= 0 as soon as
    p^m (p - 1) >= e, and increasing in m from then on, so the scan stops at
    the first jump point beyond l with that property.  (Until 2026-11-04 this evaluated i = p^m, one step too late,
    which overstates the minimum by 1/e when it falls at a jump; at the
    parameters of the paper -- p = 13, e = 1 and e = 104, N = 12, ..., 22 --
    the truncation tprec_for() and nu1 were unaffected.)
    (E060's version scanned a fixed window of 4p+20 terms.  That is correct for
    e = 1 and WRONG for e = 23, where the next jump can lie hundreds of terms
    away -- the kind of silent under-estimate this port cannot afford.)
    """
    best = _phi(l, e, p)
    m = 1
    while m <= mmax:
        i = ZZ(p)**m - 1
        if i > l:
            v = _phi(i, e, p)
            if v < best:
                best = v
            if ZZ(p)**m * (p - 1) >= e:
                break
        m += 1
    return best


def tprec_for(p, N, e=1, lmax=100000):
    """Remark 4.2: the least t-adic truncation l with nu1 >= N."""
    p, N, e = ZZ(p), ZZ(N), ZZ(e)
    l = ZZ(1)
    while l < lmax:
        if QQ(1) / e + _phi_min_from(l, e, p) >= N:
            return l
        l += 1
    raise ArithmeticError("no t-adic precision below %d reaches N = %s"
                          % (lmax, N))


def prop41_precision(p, N, e, l, k, ordtP, ordtQ):
    """min(nu1, nu2, nu3) of Proposition 4.1, as a rational.

    nu3 is included only for k >= 2: for k <= 1 there are no terms with
    -k <= i <= -2 (the i = -1 coefficient vanishes, omega being of the second
    kind), so the third error source of the proof is empty and log_p(k-1) is
    not even defined.
    """
    p, N, e, l, k = ZZ(p), ZZ(N), ZZ(e), ZZ(l), ZZ(k)
    nu1 = QQ(1) / e + _phi_min_from(l, e, p)
    nu2 = N + min(_phi(i, e, p) for i in range(0, max(l, 1)))
    out = min(nu1, nu2)
    if k >= 2:
        nu3 = N - k * max(ordtP, ordtQ) - _floorlog(k - 1, p)
        out = min(out, nu3)
    return out


def prop46_precision(p, N, eps, kmax, e0):
    """Proposition 4.6: the precision of the computed f_i(P) at a FINITE BAD
    point P with eps = ord_p(r(x(P))) < 1/p, namely

        min_k { pi(k) - k eps },   pi(k) = max{N, floor(k/p) + 1 - floor(log_p(k e0))},

    e0 the largest e_P over the finite bad points.  The max in pi(k) is not a
    typo for a min: by (2) the coefficient c_ijk has valuation at least
    floor(k/p) + 1 - floor(log_p(k e0)), so for large k it is KNOWN to be
    smaller than p^N, and dividing by r(x(P))^k costs k eps digits against that
    better bound rather than against N.

    This is the term that dominates when P is pushed only just far enough out
    of a bad disk: with e = p e_P + 1 one has eps = e_P/e as close to 1/p as
    Remark 4.4 allows, and the loss is largest.  Raising e buys precision back,
    at the cost of arithmetic in a bigger extension -- the trade-off is real,
    and coleman_integrals_general takes e as a parameter for exactly that
    reason.

    Proposition 4.5 is the case eps = 0 (a good point): the minimum is then N,
    which is what this returns.

    N here is the precision the f_i ACTUALLY have, which for this port is
    E059's certified precision and not the nominal working precision; see
    ColemanIntegrals.value_precision_at for why the difference is not cosmetic.
    """
    p, N, kmax, e0 = ZZ(p), ZZ(N), ZZ(kmax), ZZ(e0)
    eps = QQ(eps)
    if eps == 0:
        return QQ(N)
    best = QQ(N)
    for k in range(1, kmax + 1):
        pik = max(QQ(N), QQ(floor(k / p) + 1 - floor(log(float(k * e0), float(p)))))
        v = pik - k * eps
        if v < best:
            best = v
    return best


# ------------------------------------------------------------------ integrals

class TinyIntegrals(object):
    """Algorithm 3.4 for one curve at one prime."""

    def __init__(self, RR, tprec=None, ring=None):
        self.RR = RR
        self.ring = ring if ring is not None else RR.base
        self.base = self.ring
        self.e = ramification_index(self.ring, RR.p)
        self.tprec = ZZ(tprec) if tprec is not None \
            else tprec_for(RR.p, RR.N, self.e)
        self.last_precision = None

    def over(self, ring):
        """The same machinery over a ramified extension (Remark 3.11)."""
        return TinyIntegrals(self.RR, ring=ring)

    # ------------------------------------------------- Algorithm 3.4, step 1

    def expansion_point(self, P, Q, at=None):
        """The point of Algorithm 3.4(1) at which to expand.

        If the disk is good, P.  If it is bad, the very bad point in it: either
        an endpoint IS that point, or the caller supplies it as ``at``.  It
        cannot be found here -- that would mean solving r = 0 inside the disk,
        and the caller who put the endpoints in a bad disk (Algorithm 3.12, or
        Algorithm 3.7 integrating to F_p(P')) already knows the answer.
        Expanding at the wrong point of a bad disk loses precision silently, so
        the case is refused rather than guessed.
        """
        if at is not None:
            at = at if at.ring is self.ring else at.change_ring(self.ring)
            if not at.is_very_bad():
                raise ValueError("%s is not a very bad point" % at)
            if not (at.same_disk(P) and at.same_disk(Q)):
                raise ValueError("%s is not in the residue disk of the "
                                 "endpoints" % at)
            return at
        if P.is_very_bad():
            return P
        if Q.is_very_bad():
            return Q
        if P.is_bad() or Q.is_bad():
            raise ValueError(
                "the residue disk is bad but neither endpoint is the very bad "
                "point in it; Algorithm 3.4(1) needs that point (pass it as "
                "at=...)")
        return P

    def expansion_at(self, P):
        return LocalExpansion(P, self.tprec, ring=self.ring)

    # ------------------------------------------------------- the integration

    def integrate_series(self, g, tQ, tP=None):
        """int_{tP}^{tQ} g(t) dt for a Laurent series g.

        The coefficient of t^{-1} must vanish (omega is of the second kind).
        That is a THEOREM about the input, so it is checked: a nonzero residue
        would mean the form fed in is not of the second kind, and the answer
        would be a branch of a logarithm rather than a Coleman integral.
        """
        R = self.ring
        tQ = R(tQ)
        tP = R(0) if tP is None else R(tP)
        res = g[-1]
        if res != 0 and QQ(res.valuation()) / self.e < self.RR.N - 1:
            raise ArithmeticError(
                "the form has a nonzero residue %s at the expansion point: it "
                "is not of the second kind" % res)
        tot = R(0)
        for i in g.exponents():
            if i == -1:
                continue
            a = g[i]
            if a == 0:
                continue
            tot += R(a) * (tQ**(i + 1) - tP**(i + 1)) / ZZ(i + 1)
        return tot

    def _certify(self, g, tP, tQ):
        """Record Proposition 4.1's bound for the integral just computed."""
        k = max(0, -g.valuation())
        vP = QQ(tP.valuation()) / self.e if tP != 0 else QQ(self.RR.N)
        vQ = QQ(tQ.valuation()) / self.e if tQ != 0 else QQ(self.RR.N)
        prec = prop41_precision(self.RR.p, self.RR.N, self.e, self.tprec,
                                k, vP, vQ)
        if self.last_precision is None or prec < self.last_precision:
            self.last_precision = prec
        return prec

    def tiny_integral(self, coeffs, P, Q, at=None):
        """int_P^Q (sum_i u_i(x) b^0_i) dx/r, P and Q in the same disk."""
        return self.tiny_integrals_on_basis([coeffs], P, Q, at=at)[0]

    def tiny_integrals_on_basis(self, forms, P, Q, at=None):
        """The same for a list of forms, sharing one local expansion.

        ``at`` is the very bad point of the residue disk, when there is one and
        neither endpoint is it (Algorithm 3.4(1)).
        """
        P = P if P.ring is self.ring else P.change_ring(self.ring)
        Q = Q if Q.ring is self.ring else Q.change_ring(self.ring)
        exp = self.expansion_at(self.expansion_point(P, Q, at=at))
        tP, tQ = exp.t_of(P), exp.t_of(Q)
        out = []
        for c in forms:
            g = exp.series_of_form(c)
            self._certify(g, tP, tQ)
            out.append(self.integrate_series(g, tQ, tP))
        return vector(self.ring, out)


class ColemanIntegrals(object):
    """Algorithms 3.7 and 3.12: Coleman integrals between points of X(K).

    Given the matrix Phi and the functions f_i of BT Definition 2.17,

        sum_j (Phi - I)_ij int_P^Q omega_j
             = f_i(P) - f_i(Q) - int_P^{F_p(P)} omega_i - int_{F_p(Q)}^Q omega_i,

    and Phi - I is invertible because the eigenvalues of Phi have complex
    absolute value p^{1/2} (Remark 3.8) -- checked per instance rather than
    assumed.  Phi and the f_i are computed once over Q_p; only their VALUES
    move into the ramified extension (Remark 3.11).
    """

    def __init__(self, FM, tiny=None):
        self.FM = FM
        self.RR = FM.RR
        self.base = FM.base
        self.tiny = tiny if tiny is not None else TinyIntegrals(FM.RR)
        if FM.Phi is None or not getattr(FM, "f", None):
            FM.compute(primitives=True)
        self.forms = [FM._form_coefficients(b) for b in FM.basis]
        # INDEX CONVENTION.  frobenius.py stores Phi with column i the image of
        # omega_i, i.e. Phi[j][i] is the coefficient of omega_j in F(omega_i);
        # BT Definition 2.17 writes F*(omega_i) = df_i + sum_j Phi_ij omega_j,
        # which is the TRANSPOSE.  The characteristic polynomial cannot see the
        # difference -- which is why E059 was right to leave it -- but
        # Algorithm 3.7 can, and does.
        self.Phi = FM.Phi.transpose()
        self.last_tiny = self.tiny
        self.PhiI = self.Phi - self.Phi.parent().one()
        if self.PhiI.determinant() == 0:
            raise ArithmeticError("Phi - I is singular: Remark 3.8 violated")
        self._ext_cache = {}

    # ------------------------------------------------------ ramified extension

    def extension(self, e):
        """K = Q_p(p^{1/e}).

        Built over Qp(p, N) and NOT over the 'floating-point' ring the rest of
        the port uses: Sage has no Eisenstein extension of a floating-point
        p-adic field (it raises KeyError).  Values therefore cross between the
        two rings by explicit coercion -- there is no automatic coercion, so
        every crossing in this module is written out.
        """
        e = ZZ(e)
        if e not in self._ext_cache:
            K0 = Qp(self.RR.p, self.RR.N)
            Rz = PolynomialRing(K0, 'z')
            z = Rz.gen()
            self._ext_cache[e] = K0.ext(z**e - self.RR.p, names='pi')
        return self._ext_cache[e]

    def f_converges_at(self, P):
        """BT Proposition 4.3 / Remark 4.4: ord_p(r(x(P))) < 1/p."""
        if P.rval == 0:
            return False
        return P.vp(P.rval) < QQ(1) / self.RR.p

    def value_precision_at(self, P):
        """Propositions 4.5 and 4.6: the precision of the computed f_i(P).

        N at a good point; strictly less at a point of a bad disk, by an amount
        governed by how close it still is to the very bad point.

        TWO PLACES WHERE THE PAPER'S HYPOTHESIS IS NOT OURS, AND BOTH MATTER:

        (a) Propositions 4.5 and 4.6 begin "suppose that f_{i,0}, f_{i,inf},
        f_{i,end} are accurate to precision N".  OURS ARE NOT.  They come out of
        the reductions of Propositions 3.3 and 3.4, whose loss Propositions 3.7
        and 3.8 bound -- E059 computes that as certified_precision(), strictly
        less than N.  Feeding Proposition 4.6 the nominal N overstates the
        answer by exactly that gap: measured on y^2 = x^5-1 at p = 11, N = 8,
        the nominal reading promised p^{74/23} while the computed values were
        good to p^{44/23} and the integral to p^{39/23} (established by running
        the same integral at N = 16 and N = 20 and comparing).  With the
        certified precision in place of N the bound is p^{28/23} and holds.

        (b) k's range is read off the r-adic support of the f_i we actually
        built, not from a generic bound -- and that support GROWS with N
        (55 digits at N = 8, 95 at N = 12, 175 at N = 20 for that curve), so
        raising N buys much less here than it does at a good point.  The lever
        that works is raising e, which shrinks eps = e_P/e directly.
        """
        kmax = ZZ(1)
        for fi in self.FM.f:
            kmax = max(kmax, ZZ(self.RR.J_range(fi)[1]))
        e0 = ZZ(getattr(self.FM, "e_finite", 1))
        Nf = ZZ(self.FM.certified_precision()[0])
        return prop46_precision(self.RR.p, Nf, P.vp(P.rval), kmax, e0)

    def certified_precision(self, P, Q):
        """What the theory guarantees for int_P^Q: the worst of Phi's own
        certificate (Propositions 3.7, 3.8 -- E059), Proposition 4.1 for the
        tiny integrals, and Propositions 4.5/4.6 for the values f_i(P), f_i(Q)
        at whatever points the algorithm actually evaluated them."""
        out = QQ(self.FM.certified_precision()[0])
        if self.last_tiny.last_precision is not None:
            out = min(out, QQ(self.last_tiny.last_precision))
        for R in (P, Q):
            if R is not None:
                out = min(out, self.value_precision_at(R))
        return out

    # ------------------------------------------------------------ Algorithm 3.7

    def frobenius_image(self, P):
        """F_p(P) = (x^p, beta(P)), which lies in the residue disk of P."""
        RR = self.RR
        xv = P.x**RR.p
        yv = RR.evaluate(self.FM.lift.beta, P.x, P.y, ring=P.ring)
        Fp = CurvePoint(RR, xv, y=yv, inf=P.inf, ring=P.ring)
        if not P.same_disk(Fp):
            raise ArithmeticError(
                "F_p(P) left the residue disk of P: the lift is wrong")
        return Fp

    def coleman_integrals_on_basis(self, P, Q, at_P=None, at_Q=None):
        """Algorithm 3.7: the vector of int_P^Q omega_i, assuming the f_i
        converge at both endpoints (true at every good point, and at points of
        a bad disk that are far enough from the very bad point).

        ``at_P``, ``at_Q`` are the very bad points of the endpoints' residue
        disks, needed by step (2): the tiny integrals to F_p(P) and from F_p(Q)
        stay inside those disks, so when an endpoint sits in a bad disk (which
        is exactly the situation Algorithm 3.12 creates) the expansion for them
        has to be taken at the very bad point, not at the endpoint.
        """
        if not (self.f_converges_at(P) and self.f_converges_at(Q)):
            raise NotImplementedError(
                "the f_i need not converge at these endpoints; use "
                "coleman_integrals_general (Algorithm 3.12)")
        if P.ring is not Q.ring:
            raise ValueError("endpoints live over different rings")
        tiny = self.tiny if P.ring is self.tiny.ring else self.tiny.over(P.ring)
        self.last_tiny = tiny
        self.last_eval_points = (P, Q)
        FP, FQ = self.frobenius_image(P), self.frobenius_image(Q)
        tiny_P = tiny.tiny_integrals_on_basis(self.forms, P, FP, at=at_P)
        tiny_Q = tiny.tiny_integrals_on_basis(self.forms, FQ, Q, at=at_Q)
        rhs = []
        for i in range(len(self.forms)):
            fP = self.RR.evaluate(self.FM.f[i], P.x, P.y, ring=P.ring)
            fQ = self.RR.evaluate(self.FM.f[i], Q.x, Q.y, ring=Q.ring)
            rhs.append(fP - fQ - tiny_P[i] - tiny_Q[i])
        # Explicit coercion, entry by entry: there is no coercion morphism from
        # the floating-point Q_p that carries Phi into the Eisenstein extension
        # (K(a) works, a + pi does not), so change_ring() is not available.
        n = self.PhiI.nrows()
        M = matrix(P.ring, n, n,
                   [P.ring(self.PhiI[i][j]) for i in range(n) for j in range(n)])
        return M.solve_right(vector(P.ring, rhs))

    # ----------------------------------------------------------- Algorithm 3.12

    def ramification_at(self, P):
        """e_P = ord_P(x - x(P)), read off the local expansion.

        Not assumed to be 2 for C_4's (0,0), and not bounded crudely by d_x:
        the t-adic valuation of x(t) - x(P) IS e_P by definition, and the
        expansion has already been computed.
        """
        if P.dQ_dy_is_unit():
            return ZZ(1)
        exp = TinyIntegrals(self.RR, ring=P.ring).expansion_at(P)
        return ZZ((exp.xt - exp.xt[0]).valuation())

    def push_out_of_bad_disk(self, P, e=None):
        """Step (1): a point P' of the residue disk of P where the f_i converge.

        Remark 4.4: with t a local coordinate at the very bad point of the disk,
        the f_{i,0} converge where ord_p(t) < 1/(p e_P), so a point over
        Q_p(p^{1/e}) with e > p e_P will do; we take t(P') = pi, of valuation
        1/e.  That P' really is far enough is not taken on trust -- the caller's
        next step evaluates f_i there, and radic.evaluate enforces Proposition
        4.3's condition ord_p(r(x)) < 1/p.
        """
        if not P.is_very_bad():
            raise ValueError("push_out_of_bad_disk expects the very bad point")
        if e is None:
            e = ZZ(self.RR.p) * self.ramification_at(P) + 1
        K = self.extension(e)
        exp = TinyIntegrals(self.RR, ring=K).expansion_at(P.change_ring(K))
        return exp.point_at(K.gen()), K, ZZ(e)

    def coleman_integrals_general(self, P, Q, e=None, at_P=None, at_Q=None):
        """Algorithm 3.12: int_P^Q omega_i with P or Q allowed to be bad.

        ``at_P``, ``at_Q`` are the very bad points of the endpoints' residue
        disks, needed when an endpoint lies in a bad disk without BEING the
        very bad point of it.  When an endpoint is itself very bad it is its
        own, and nothing has to be supplied.

        The good-good case falls through to Algorithm 3.7 unchanged, so this is
        safe to call always.  Returns the vector over the smallest ring the
        computation needed.
        """
        if self.f_converges_at(P) and self.f_converges_at(Q):
            return self.coleman_integrals_on_basis(P, Q)

        def very_bad_of(R, at):
            if self.f_converges_at(R):
                return None
            if R.is_very_bad():
                return R
            if at is None:
                raise ValueError(
                    "%s lies in a bad disk without being the very bad point "
                    "of it; pass that point as at_P/at_Q (Algorithm 3.12(1) "
                    "needs it)" % R)
            return at

        BP, BQ = very_bad_of(P, at_P), very_bad_of(Q, at_Q)

        # (1) replacement endpoints, over ONE common ring: the two bad
        # endpoints may have different e_P, and Algorithm 3.7 needs both new
        # points over the same field, so e is chosen from the worse of them.
        if e is None:
            e = max(ZZ(self.RR.p) * self.ramification_at(B) + 1
                    for B in (BP, BQ) if B is not None)
        K = self.extension(e)
        tinyK = TinyIntegrals(self.RR, ring=K)

        def replace(R, B):
            if B is None:
                return R.change_ring(K), None
            Rp, _, _ = self.push_out_of_bad_disk(B, e=e)
            return Rp, B.change_ring(K)

        Pp, Pbad = replace(P, BP)
        Qp_, Qbad = replace(Q, BQ)

        # (2) tiny corrections, (3) the integral between the new points.
        # Pbad and Qbad are the very bad points, so they are also what step (2)
        # of Algorithm 3.7 must expand at inside those same disks.
        n = len(self.forms)
        head = vector(K, [K(0)] * n)
        tail = vector(K, [K(0)] * n)
        if Pbad is not None:
            head = tinyK.tiny_integrals_on_basis(self.forms, P.change_ring(K),
                                                 Pp, at=Pbad)
        if Qbad is not None:
            tail = tinyK.tiny_integrals_on_basis(self.forms, Qp_,
                                                 Q.change_ring(K), at=Qbad)
        middle = self.coleman_integrals_on_basis(Pp, Qp_,
                                                 at_P=Pbad, at_Q=Qbad)
        if tinyK.last_precision is not None:
            self.last_tiny = tinyK

        # (4)
        return vector(K, [head[i] + middle[i] + tail[i] for i in range(n)])
