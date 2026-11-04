r"""
frobenius --- E048 Phase 2 (E057), third part: the matrix of
Frobenius on H^1_rig(X) and the polynomial chi(T).

Source: J. Tuitman, *Counting points on curves using a map to P^1*,
Math. Comp. 85 (2016), 961--981 (arXiv:1402.6758v2), Sections
4.2--4.4:

  For omega_i = (sum_k u_k(x) y^k) dx/r,

      F_p(omega_i) = sum_k p x^{p-1} u_k^sigma(x^p) alpha beta^k dx + O(p^N),

  which is then reduced back to E_0 cap E_infinity by Propositions 3.3 and 3.4
  and expressed in the basis, giving Phi with F_p(omega_i) = sum_j Phi_{j,i}
  omega_j in H^1_rig(U).  Finally chi(T) = det(1 - F_p^n T | H^1_rig(X)) and
  Z(X,T) = chi(T)/((1-T)(1-qT)).  With n = 1, F_p^n = F_p and chi(T) =
  det(1 - Phi T).

THE PIPELINE, and the two places it can be checked without external data:

  1. basis of H^1_rig(X) inside E, over Q (exact, from E056/E057);
  2. F_p(omega_i) as an r-adic element (E058);
  3. Proposition 3.3 down to level 1  -> an element of E_0;
  4. change to the b^inf basis, Proposition 3.4 down to m = -ord_0(W^inf)
     -- NOT to m = 1, see E057 -- so the exact form stays in B_0 cap B_inf;
  5. back to powers of y; the result must lie in the span of the basis of
     H^1_rig(X) together with d(B).  THAT IS A CHECK: Frobenius preserves
     H^1_rig(X), so a reduction bug shows up as an unsolvable system;
  6. chi(T) must have integer coefficients satisfying the Weil bounds.  THAT
     IS A SECOND CHECK, and it is what turns a p-adic approximation into an
     exact answer.
"""

from sage.all import (QQ, ZZ, matrix, vector, PolynomialRing, Qp, identity_matrix)

from padic.radic import RAdicRing
from padic.froblift import FrobeniusLift
from padic.reductions import FiniteReductionPadic, InfiniteReductionPadic


class FrobeniusMatrix(object):
    """Phi and chi(T) for one curve at one prime."""

    def __init__(self, C, H, p, N, verbose=False):
        self.C = C
        self.H = H
        self.p = ZZ(p)
        self.N = ZZ(N)
        # Fixed relative precision, no decay: the arithmetic model of the paper
        # (compute modulo p^N, bound the loss by Propositions 3.7 and 3.8).
        # See the note in radic.py for why capped-relative is wrong here.
        self.base = Qp(p, prec=N, type='floating-point')
        self.RR = RAdicRing(C, p, N, base=self.base)
        self.lift = FrobeniusLift(self.RR)
        self.fin = FiniteReductionPadic(self.RR)
        self.inf = InfiniteReductionPadic(self.RR)
        # Both parts come out integral and together form a Z-basis of the
        # saturated lattice; see H1X_basis for why that matters here.
        self.basis, self.im_basis = H.H1X_basis()
        self.g = ZZ(C.genus)
        if len(self.basis) != 2 * self.g:
            raise ArithmeticError("H^1_rig(X) has dimension %d, expected 2g = %d"
                                  % (len(self.basis), 2 * self.g))
        self.verbose = verbose
        self.Phi = None
        self.e_finite, self.e_infinite = self._ramification()

    def _ramification(self):
        """e = max e_P over the finite branch points, e_inf over infinity.

        r is squarefree, so ord_P(r) = e_P at the points over its roots; and
        e_P = ord_P(1/x) at the points over infinity.  These are the constants
        in Propositions 3.7 and 3.8.
        """
        C = self.C
        e, einf = 1, 1
        for pl, m in C.L(C.r).divisor().list():
            if m > 0 and not pl.is_infinite_place():
                e = max(e, ZZ(m))
        for pl, m in C.L(C.x).divisor().list():
            if m < 0 and pl.is_infinite_place():
                einf = max(einf, ZZ(-m))
        return e, einf

    def certified_precision(self):
        """N minus the losses Propositions 3.7 and 3.8 allow.

        This is a theorem-backed statement about Phi, unlike anything the
        fixed-precision arithmetic could report about itself.  It is also the
        precision of chi(T) only if ord_p(Phi) >= 0, the standing assumption
        in the proof of Tuitman's Proposition 4.4 (arXiv v2 numbering), under
        which det(1 - Phi T) loses nothing.  Otherwise Remark 4.5 there
        subtracts a further -(2g-1) ord_p(Phi) (n = 1), and that valuation is
        not checked here.
        """
        from sage.all import floor, log
        p = self.p
        L = max(1, getattr(self.fin, "max_level", 1))
        m = max(1, getattr(self.inf, "max_m", 1))
        b1 = ZZ(floor(log(float(L * self.e_finite), float(p))))
        b2 = ZZ(floor(log(float(m * self.e_infinite), float(p))))
        return self.N - b1 - b2, b1, b2

    @staticmethod
    def _primitive(v):
        """Scale a rational vector to a primitive integral one."""
        den = ZZ(1)
        for c in v:
            den = den.lcm(QQ(c).denominator())
        w = [ZZ(QQ(c) * den) for c in v]
        g = ZZ(0)
        for c in w:
            g = g.gcd(c)
        if g == 0:
            return vector(QQ, w)
        return vector(QQ, [c / g for c in w])

    # ------------------------------------------------- forms and their images

    def _form_coefficients(self, vec):
        """E-coordinates -> the vector u with omega = (sum_i u_i y^i) dx/r."""
        Rx = self.RR.Rx
        out = [Rx.zero()] * self.C.dx
        for c, (i, d) in zip(vec, self.H.E_basis):
            if c != 0:
                out[i] += self.RR._coerce_QQ(c) * Rx.gen()**d
        return out

    def frobenius_of_form(self, u):
        """F_p(omega) as an r-adic element, by the formula of Section 4.2."""
        RR = self.RR
        p = self.p
        out = RR.zero()
        bpow = RR.one()
        for k in range(self.C.dx):
            if u[k] != 0:
                # p x^{p-1} u_k^sigma(x^p); sigma = id since n = 1
                fac = RR.mul(RR.normalize({0: RR.Ry(p * RR.Rx.gen()**(p - 1))}),
                             RR.subst_xp_poly(u[k]))
                out = RR.add(out, RR.mul(fac, bpow))
            bpow = RR.mul(bpow, self.lift.beta)
        return RR.mul(out, self.lift.alpha)

    # ------------------------------------------------------------ reduction

    def reduce_to_E(self, elt, primitives=False):
        """Steps 3--5: an r-adic element -> E-coordinates over Q_p.

        With primitives=True also returns f_0 + f_inf, the exact form subtracted
        by the two reductions, as an element of R in the r-adic representation
        (Balakrishnan-Tuitman Algorithm 2.18(2),(3)).  f_end is added by
        compute(), since it only appears when the class is written in the basis.
        """
        if not primitives:
            red = self.fin.reduce([elt])[0]
            u = self.fin.to_E0(red)              # powers of y, polynomial
            w = self.inf.to_binf(u)              # b^inf basis
            w = self.inf.reduce(w)               # Proposition 3.4
            u = self.inf.to_powers_of_y(w)       # back to powers of y
            return self._coords_in_E(u)
        reds, prims = self.fin.reduce([elt], primitives=True)
        u = self.fin.to_E0(reds[0])
        w = self.inf.to_binf(u)
        w, vinf = self.inf.reduce(w, primitives=True)
        u = self.inf.to_powers_of_y(w)
        # f_inf is given in the b^inf basis; move it to powers of y.  Remark 3.5
        # guarantees it has no finite pole, so the result must be polynomial --
        # which is checked, not assumed.
        finf_poly = self.inf.to_powers_of_y(vinf)
        f = prims[0]
        d0 = {}
        for i, g in enumerate(finf_poly):
            if g == 0:
                continue
            if g.valuation() < 0:
                raise ArithmeticError(
                    "f_inf has a pole at x = 0: Remark 3.5 violated")
            for k in range(g.valuation(), g.degree() + 1):
                c = g[k]
                if c != 0:
                    d0[(i, k)] = c
        if d0:
            acc = self.RR.Ry.zero()
            for (i, k), c in d0.items():
                acc += c * self.RR.Rx.gen()**k * self.RR.Ry.gen()**i
            f = self.RR.add(f, self.RR.normalize({0: acc}))
        return self._coords_in_E(u), f

    def _coords_in_E(self, u):
        idx = {m: k for k, m in enumerate(self.H.E_basis)}
        out = [self.base(0)] * self.H.dim_E
        for i, f in enumerate(u):
            if f == 0:
                continue
            for d in range(f.valuation(), f.degree() + 1):
                c = f[d]
                if c == 0:
                    continue
                if (i, d) not in idx:
                    raise ArithmeticError(
                        "reduced form leaves E: monomial x^%d y^%d" % (d, i))
                out[idx[(i, d)]] = c
        return vector(self.base, out)

    # --------------------------------------------------------------- matrix

    def _dB_preimages(self):
        """For each basis vector w of d(B), a z in B with d(z) = w.

        The matrix of d has the constants in its kernel, so z is not unique;
        any preimage does, since only d(z) enters.
        """
        dM = self.H.d_matrix()
        out = []
        for w in self.im_basis:
            out.append(dM.solve_right(vector(QQ, list(w))))
        return out

    def compute(self, primitives=False):
        """The matrix Phi, column by column.

        With primitives=True also stores self.f, the functions f_i with

            F_p^*(omega_i) = d f_i + sum_j Phi_{j,i} omega_j,

        which Algorithm 3.7 needs at the endpoints.

        INDEX CONVENTION, and it is NOT [BT] Definition 2.17's.  That
        definition, read in the arXiv LaTeX source, writes Frob_p^*(omega_i) =
        df_i + sum_j Phi_ij omega_j -- the ROW convention, so their Phi is our
        transpose, and it is also [BDM+19]'s F, which acts on the column of
        forms by phi^* omega = F omega + df.  Ours acts on COORDINATE vectors,
        which is what unit_root_subspace and the change of basis need; chi(T)
        cannot see the difference, and neither can the point counts that
        calibrate it, so the transpose has to be tracked by hand.  E071 depends
        on getting it right: condition (a) of [BDM+19] §4.4 reads
        F^T Z F = pZ with F = Phi^T.
        """
        n = self.H.dim_E
        cols = [vector(self.base, [self.base(QQ(c)) for c in b])
                for b in self.basis]
        dcols = [vector(self.base, [self.base(QQ(c)) for c in b])
                 for b in self.im_basis]
        A = matrix(self.base, n, len(cols) + len(dcols),
                   lambda i, j: (cols[j][i] if j < len(cols)
                                 else dcols[j - len(cols)][i]))
        out = []
        self.f = []
        self.min_solve_residual = None
        Bsol = self._dB_preimages() if primitives else None
        for i, b in enumerate(self.basis):
            u = self._form_coefficients(b)
            Fw = self.frobenius_of_form(u)
            if primitives:
                coords, fi = self.reduce_to_E(Fw, primitives=True)
            else:
                coords = self.reduce_to_E(Fw)
            sol = A.solve_right(coords)          # step 5: must be solvable
            res = A * sol - coords               # ... and this measures it
            vals = [c.valuation() for c in res if c != 0]
            v = min(vals) if vals else self.N
            self.min_solve_residual = v if self.min_solve_residual is None \
                else min(self.min_solve_residual, v)
            if primitives:
                # f_end: the d(B) part of the decomposition.  sol's tail gives
                # the coefficients on the basis of d(B); Bsol turns each of
                # those into the function in B_0 cap B_inf it is the d of.
                acc = self.RR.Ry.zero()
                for k in range(len(dcols)):
                    c = sol[len(cols) + k]
                    if c == 0:
                        continue
                    for m, z in enumerate(Bsol[k]):
                        if z != 0:
                            (bi, bd) = self.H.B_basis[m]
                            acc += (c * self.RR._coerce_QQ(z)
                                    * self.RR.Rx.gen()**bd
                                    * self.RR.Ry.gen()**bi)
                if acc != 0:
                    fi = self.RR.add(fi, self.RR.normalize({0: acc}))
                self.f.append(fi)
            out.append([sol[j] for j in range(len(cols))])
            if self.verbose:
                print("      column %d done" % i)
        self.Phi = matrix(self.base, 2 * self.g, 2 * self.g,
                          lambda i, j: out[j][i])
        return self.Phi

    # ------------------------------------------------------------- chi(T)

    def chi(self):
        """chi(T) = det(1 - Phi T), rounded to Z[T].

        Returns (chi over QQ with integer coefficients, the certified p-adic
        precision cert of its coefficients).  That precision -- NOT the
        distance from the rounded value, which is zero by construction -- is
        what says whether the rounding is determined.  It is the certified
        precision of Phi when ord_p(Phi) >= 0; otherwise the further loss
        (2g-1) (-ord_p(Phi)) of Tuitman's Remark 4.5 (arXiv v2 numbering,
        n = 1) is subtracted.  (Until 2026-11-04 that case was not checked.)
        As in Tuitman (arXiv v2, proof of Prop. 4.4), only
        the BOTTOM half c_0, ..., c_g is rounded: these satisfy
        |c_k| <= binomial(2g,k) p^{k/2} <= binomial(2g,g) p^{g/2}, so
        p^cert > 2 binomial(2g,g) p^{g/2} pins them.  The top half is then
        given by the functional equation c_{2g-k} = p^{g-k} c_k.  (The top
        coefficients themselves reach p^g = c_{2g}, so rounding them at the
        same precision would NOT be determined; until 2026-11-04 this method
        rounded all 2g+1 of them.)  Where cert does pin a top coefficient as
        well, its rounding is compared with the functional equation and a
        mismatch raises.

        Sign convention, and it is the one that bit E059: with
        cp(T) = det(T - Phi) = sum_j a_j T^j of degree d,

            det(1 - Phi T) = T^d cp(1/T) = sum_k a_{d-k} T^k,

        with NO factor of (-1)^k.  Inserting one replaces chi(T) by chi(-T),
        which is invisible on every curve whose odd coefficients vanish.
        """
        if self.Phi is None:
            self.compute()
        RT = PolynomialRing(QQ, 'T')
        cp = self.Phi.charpoly()
        coeffs = list(cp)
        from sage.all import binomial
        g, p = ZZ(self.g), ZZ(self.p)
        d = 2 * g
        cert = self.certified_precision()[0]
        vphi = min([c.valuation() for c in self.Phi.list() if c != 0])
        if vphi < 0:
            cert = cert - (d - 1) * (-vphi)
        if cert < 1:
            raise ArithmeticError(
                "chi: ord_p(Phi) = %s, so by Tuitman's Remark 4.5 the "
                "certified precision of chi(T) is p^%s; raise N" % (vphi, cert))
        out = [self._round(coeffs[d - k], cert) for k in range(g + 1)]
        for k in range(g + 1, d + 1):
            ck = p**(k - g) * out[d - k]
            # |c_k| <= binomial(2g,k) p^{k/2}; p^cert pins c_k when
            # p^{2 cert} > 4 binomial(2g,k)^2 p^k (exact, no square roots).
            if p**(2 * ZZ(cert)) > 4 * binomial(d, k)**2 * p**k:
                rk = self._round(coeffs[d - k], cert)
                if rk != ck:
                    raise ArithmeticError(
                        "chi: coefficient of T^%d rounds to %s but the "
                        "functional equation gives %s" % (k, rk, ck))
            out.append(ck)
        return RT(out), cert

    def chi_certified_precision(self):
        """The certified precision chi() will use: that of Phi, minus
        (2g-1)(-ord_p(Phi)) when ord_p(Phi) < 0 (Tuitman, Remark 4.5)."""
        if self.Phi is None:
            self.compute()
        cert = self.certified_precision()[0]
        vphi = min([c.valuation() for c in self.Phi.list() if c != 0])
        return cert - (2 * self.g - 1) * max(0, -vphi), vphi

    def weil_check(self, chi):
        """|c_k| <= binomial(2g,k) p^{k/2} for the coefficients of chi.

        A certificate that does not use point counts: the rounding of the
        coefficients is only legitimate if what comes out is a possible Weil
        polynomial, and a wrong digit at p^cert would break these bounds.
        """
        from sage.all import binomial, RR as RRfield
        g, p = self.g, self.p
        bad = []
        for k, c in enumerate(list(chi)):
            bound = binomial(2 * g, k) * RRfield(p)**(k / 2)
            if abs(QQ(c)) > bound:
                bad.append((k, c, bound))
        return bad

    def _round(self, c, cert):
        """Symmetric lift modulo p^cert, cert the CERTIFIED precision.

        Not p^N: the working precision is N but Propositions 3.7 and 3.8 only
        guarantee N minus the reduction losses, and the digits above that are
        arithmetic debris.  Reducing modulo p^N keeps the debris and produces
        integers like 156310 where the answer is 60 (C_4, p = 5, N = 8, where
        156310 - 60 = 2*5^7).
        """
        if c == 0:
            return ZZ(0)
        m = self.p**ZZ(cert)
        v = c.valuation()
        if v < 0:
            raise ArithmeticError(
                "coefficient of chi has negative valuation %d: the basis or "
                "the reduction is wrong, not the precision" % v)
        z = ZZ(c.lift() if hasattr(c, "lift") else c) % m
        if z > m // 2:
            z -= m
        return ZZ(z)

    # ---------------------------------------------------------- diagnostics

    def unit_root_subspace(self, n=None):
        """The unit root subspace of H^1_dR, as the columns of a 2g x g matrix.

        Balakrishnan-Dogra-Mueller-Tuitman-Vonk Remark 3.15: at a prime of
        ORDINARY reduction the splitting of the Hodge filtration that their §3.3
        needs -- symmetric and End(J)-equivariant -- is the unit root splitting,
        and given a basis whose first g members are holomorphic, a basis of the
        unit root eigenspace mod p^n is obtained by applying (phi^*)^n to the
        LAST g members.

        Both inputs come from earlier sections: the reordering that puts the
        holomorphic classes first is E064's adapted_change_of_basis (for C_4 a
        genuine change of basis, no permutation being able to do it), and phi is
        E059's Phi.  Ordinariness is not assumed here: E065(c) settles it per
        prime, and the caller is expected to have chosen p accordingly -- but
        the gate checks the outcome, since a non-ordinary p produces a subspace
        that fails to be complementary to Fil^1 rather than an error.
        """
        if self.Phi is None:
            self.compute()
        g = ZZ(self.C.genus)
        if n is None:
            n = ZZ(self.certified_precision()[0])
        S = self.H.adapted_change_of_basis()          # rows: first g holomorphic
        K = self.base
        cols = []
        for k in range(g, 2 * g):
            v = vector(K, [K(c) for c in S.row(k)])
            for _ in range(n):
                v = self.Phi * v
            cols.append(v)
        return matrix(K, cols).transpose()

    def precision_report(self):
        """What the reductions actually did to the p-adic size of things.

        finite_loss / infinite_loss: the largest number of digits a single
        reduction step divided away (Propositions 3.3 and 3.4).  Proposition
        3.7 bounds the loss of the whole finite reduction by floor(log_p(l e)),
        Proposition 3.8 the infinite one by floor(log_p(m e_inf)).
        remainder: how far from p^N the residues of the division by r sit, once
        the step's own loss is subtracted -- near N is healthy, near 0 is a bug.
        solve_residual: the valuation of the residual when the reduced class is
        written in the basis; the class must lie in the span, so this measures
        step 5 of the pipeline.
        """
        return {"finite_loss": self.fin.max_step_loss,
                "infinite_loss": self.inf.max_step_loss,
                "remainder": self.fin.min_remainder_valuation,
                "solve_residual": getattr(self, "min_solve_residual", None),
                "N": self.N}
