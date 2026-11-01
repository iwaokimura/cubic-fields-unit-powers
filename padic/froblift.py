r"""
froblift --- E048 Phase 2 (E057): the Frobenius lift of Theorem 2.6.

Source: J. Tuitman, *Counting points on curves using a map to P^1*,
Math. Comp. 85 (2016), 961--981 (arXiv:1402.6758v2).

  Theorem 2.6.  There is a Frobenius lift F_p : R^dagger -> R^dagger with
  F_p(x) = x^p.  Define
        alpha_0 = 1/r^p,                     beta_0 = y^p,
        alpha_{i+1} = alpha_i (2 - alpha_i r^sigma(x^p))      mod p^{2^{i+1}},
        beta_{i+1}  = beta_i - Q^sigma(x^p, beta_i) s^sigma(x^p, beta_i) alpha_i
                                                              mod p^{2^{i+1}},
  where s = r/(dQ/dy) lies in A (Proposition 2.4).  Then F_p(1/r) = lim alpha_i
  and F_p(y) = lim beta_i.

Two Newton iterations run side by side: alpha inverts r^sigma(x^p), and beta
solves Q^sigma(x^p, -) = 0 starting from y^p, with s alpha in place of the
derivative's inverse -- which is what makes the second iteration usable, since
1/(dQ/dy) is not in the ring but s/r is.

n = 1 ONLY: sigma is the identity here (see padic/radic.py).  Every place where
sigma would act is marked in the code.

PRECISION.  Tuitman halves the work by computing alpha_i, beta_i modulo
p^{2^{i+1}}.  This implementation runs every iteration at the full working
precision N and simply performs ceil(log2(N)) + 1 of them; that is correct (the
recursion converges p-adically) and slower, and it is the "make it work first"
choice recorded in E057 Section 3.4.  The convergence is
verified, not assumed: the gate checks the two defining identities to the full
working precision.
"""

from sage.all import ZZ, ceil, log


class FrobeniusLift(object):
    """alpha = F_p(1/r) and beta = F_p(y) for one RAdicRing."""

    def __init__(self, RR, iterations=None, verbose=False):
        self.RR = RR
        self.p = RR.p
        self.N = RR.N
        if iterations is None:
            iterations = ZZ(ceil(log(float(max(self.N, 2)), 2))) + 1
        self.iterations = ZZ(iterations)
        self.rxp = RR.subst_xp_poly(RR.r)          # r^sigma(x^p), sigma = id
        self.alpha, self.beta, self.history = self._run(verbose)

    # ---------------------------------------------------------------- Newton

    def _run(self, verbose):
        RR = self.RR
        alpha = RR.r_power(self.p)                    # alpha_0 = 1/r^p
        beta = RR.from_A(self._y_power(self.p))       # beta_0 = y^p
        hist = []
        two = RR.scalar(RR.base(2), RR.one())
        for i in range(self.iterations):
            # alpha_{i+1} = alpha_i (2 - alpha_i r(x^p))
            alpha = RR.mul(alpha, RR.sub(two, RR.mul(alpha, self.rxp)))
            # beta_{i+1} = beta_i - Q(x^p, beta_i) s(x^p, beta_i) alpha_i
            Qb = RR.subst_xp_A(RR.Qy, beta)
            sb = RR.subst_xp_A(RR.s, beta)
            beta = RR.sub(beta, RR.mul(RR.mul(Qb, sb), alpha))
            hist.append((i + 1, RR.J_range(alpha), RR.J_range(beta)))
            if verbose:
                print("    iteration %d: J(alpha) = %s, J(beta) = %s"
                      % (i + 1, RR.J_range(alpha), RR.J_range(beta)))
        return alpha, beta, hist

    def _y_power(self, n):
        """y^n reduced modulo Q, as an element of Rx[y]."""
        RR = self.RR
        out = RR.Ry.one()
        base = RR.y
        e = ZZ(n)
        while e:
            if e & 1:
                out = RR._reduce_modQ(out * base)
            base = RR._reduce_modQ(base * base)
            e >>= 1
        return out

    # ------------------------------------------------------------- identities

    def check_alpha(self):
        """alpha * r^sigma(x^p) == 1."""
        RR = self.RR
        return RR.equal(RR.mul(self.alpha, self.rxp), RR.one())

    def check_beta(self):
        """Q^sigma(x^p, beta) == 0."""
        RR = self.RR
        return RR.is_zero(RR.subst_xp_A(RR.Qy, self.beta))

    def check_mod_p(self):
        """beta == y^p and alpha * r^p == 1 modulo p (the definition of a
        Frobenius lift: it reduces to the p-th power map)."""
        RR = self.RR
        p = self.p
        diff_beta = RR.sub(self.beta, RR.from_A(self._y_power(p)))
        ok_beta = self._all_divisible_by_p(diff_beta)
        rp = RR.normalize({-p: RR.Ry.one()})       # r^p as an element
        ok_alpha = self._all_divisible_by_p(RR.sub(RR.mul(self.alpha, rp), RR.one()))
        return ok_beta, ok_alpha

    def _all_divisible_by_p(self, elt):
        for a in elt.values():
            for c in a.list():
                for cc in c.list():
                    if cc != 0 and cc.valuation() < 1:
                        return False
        return True

    def check_multiplicative(self, pairs):
        """F_p(fg) == F_p(f) F_p(g) on given pairs of elements of R.

        This is the real test of the r-adic arithmetic: F_p is *defined* by
        substitution, so a failure here is a bug in normalisation, in the
        reduction modulo Q, or in the carry between r-adic digits.
        """
        RR = self.RR
        bad = 0
        for f, g in pairs:
            lhs = RR.frobenius_apply(RR.mul(f, g), self.alpha, self.beta)
            rhs = RR.mul(RR.frobenius_apply(f, self.alpha, self.beta),
                         RR.frobenius_apply(g, self.alpha, self.beta))
            if not RR.equal(lhs, rhs):
                bad += 1
        return bad

    # ------------------------------------------------- Proposition 2.12 (2)

    def prop212_bounds(self):
        """The bounds Proposition 2.12 asserts for F_p(y^i), against reality.

        Returns a dict with the observed r-adic ranges and the paper's bounds:
        max J <= p(N-1) for F_p(y^i), and the digits away from j = 0 have
        degree < deg(r) by construction of the normal form.
        """
        RR = self.RR
        obs = []
        for i in range(RR.dx):
            fi = RR.frobenius_apply(RR.from_A(self._y_power(i)),
                                    self.alpha, self.beta)
            obs.append((i, RR.J_range(fi), RR.max_coeff_degree(fi)))
        return {"observed": obs,
                "maxJ_bound": self.p * (self.N - 1),
                "degree_bound": RR.degr - 1}
