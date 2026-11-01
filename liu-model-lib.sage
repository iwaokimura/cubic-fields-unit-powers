# liu-model-lib.sage -- Liu's desingularisation of double covers of regular
# surfaces (Q. Liu, "Desingularization of double covers of regular surfaces",
# arXiv:2504.16808v3), implemented for the charts that arise from iterated
# blow-ups of P^1 over Z_ell and of the double covers built on top of them.
#
# E128.  Loaded by check-liu-examples.sage and check-c4-l2model.sage.
# Numbering follows the v3 PDF (checked against it 2026-10-31; until then
# these comments carried the numbers of an earlier version):
#   Def. 2.3          lambda_m(B) = sup_y min{2 ord(a), ord(b)}
#   Prop. 2.6         lambda <= ord(disc), with equality when char k != 2
#   Prop. 2.9         B regular over m  <=>  lambda_m(B) <= 1
#   Lemma 2.10        the algorithm for lambda when char(A/m) = 2
#   Prop. 3.1         blowing up a regular local ring at a maximal ideal;
#                     (3): nu_E = ord_m
#   Prop. 3.3         equation of Y_1: y1^2 + (a/s^r) y1 + b/s^{2r}, r=[lambda/2]
#   Thm. 3.4          Y_i -> Z_i is again a normal double cover of a regular surface
#   Lemma 3.6         the tree of E_i' in Z_N and their multiplicities m_i
#   Prop. 3.7         the components of Theta_i' = psi^{-1}(E_i') and their
#                     multiplicities in the closed fibre
#   Prop. 3.9         intersection numbers
#   Section 5.1/5.2/5.3   normalisation, finding singular points, the algorithm
#   Section 5.4       the chart normal form used here
#
# CHART NORMAL FORM (Section 5.4, Corollary).  Every chart obtained by blowing
# up rational points of the special fibre of Spec R[x] is of the form
#      A = O[S,T]/(f(S,T) - ell),      f in (S,T),
# with the point of interest at the origin m = (S,T).  This is closed under the
# two blow-up charts, and makes ord_m computable without a Groebner basis.

from sage.rings.infinity import infinity
from itertools import product as _iproduct


# ---------------------------------------------------------------------------
# 0.  The base ring O = W(F_{ell^n}) (unramified over Z_(ell))
# ---------------------------------------------------------------------------

class LiuBase:
    r"""O = Z_(ell)[th]/(h), h monic and irreducible mod ell; residue field
    k = F_{ell^n}.  n = 1 (h = th) gives O = Z_(ell), k = F_ell."""

    def __init__(self, ell, hpoly=None):
        self.ell = ZZ(ell)
        Zt = PolynomialRing(QQ, 'th')
        self.Zt = Zt
        if hpoly is None:
            hpoly = Zt.gen()
        self.h = Zt(hpoly)
        self.n = self.h.degree()
        self.O = Zt.quotient(self.h, 'a')
        self.R = PolynomialRing(self.O, 'S,T')
        self.S, self.T = self.R.gens()
        Fl = GF(self.ell)
        hbar = PolynomialRing(Fl, 'th')(self.h)
        if self.n == 1:
            self.k = Fl
            self.thbar = self.k(-hbar[0])
        else:
            self.k = GF(self.ell ** self.n, name='w', modulus=hbar)
            self.thbar = self.k.gen()
        self.G = PolynomialRing(self.k, 'sig,tau')
        self.sig, self.tau = self.G.gens()
        self.kT = PolynomialRing(self.k, 'X')
        self._lifts = None

    def __repr__(self):
        return "LiuBase(ell=%s, k=%s)" % (self.ell, self.k)

    def oval(self, c):
        """ell-adic valuation of c in O (unramified: min over coefficients)."""
        c = self.O(c)
        if c == 0:
            return infinity
        return min(QQ(co).valuation(self.ell) for co in c.lift().coefficients())

    def red(self, c):
        """image of c in k = O/ell.  Requires oval(c) >= 0."""
        L = self.O(c).lift()
        out = self.k(0)
        tb = self.thbar
        Fl = GF(self.ell)
        for i, co in enumerate(L.list()):
            q = QQ(co)
            assert q.valuation(self.ell) >= 0, "non-integral coefficient %s" % q
            out += self.k(Fl(q)) * tb ** i
        return out

    def lift_of(self, x):
        """a lift in O of x in k."""
        if self.n == 1:
            return self.O(ZZ(x))
        return self.O(self.Zt([ZZ(c) for c in x.polynomial().list()]))

    def lifts(self):
        if self._lifts is None:
            self._lifts = [self.lift_of(x) for x in self.k]
        return self._lifts

    def redpoly(self, p):
        """reduce p in O[S,T] to k[sig,tau]."""
        out = self.G(0)
        for (u, v), c in self.R(p).dict().items():
            out += self.red(c) * self.sig ** u * self.tau ** v
        return out


_BASE_EXT_CACHE = {}


def base_extension(base, m):
    r"""The unramified extension of ``base`` of degree m, with the embedding
    O -> O' of rings.  Towers are supported: O = Z_(ell)[th]/(h) with h monic
    and hbar irreducible of degree n, and O' = Z_(ell)[th']/(h') with h'
    monic and hbar' irreducible of degree nm, together with a root Theta of h
    in O'.

    Construction.  A monic lift g in O[X] of the minimal polynomial over
    k = F_{ell^n} of a generator w of k' = F_{ell^{nm}} defines the relative
    extension L = K[X]/(g) of K = Frac(O); the root alpha of g is an algebraic
    integer whose reduction generates k' over F_ell, so its minimal polynomial
    h' over Q is monic of degree nm with hbar' irreducible -- ell is inert in
    Q(alpha) and Z_(ell)[alpha] is the whole DVR.  Expressing th in the power
    basis of alpha gives Theta, and c |-> c(Theta) is the embedding."""
    ell, n = base.ell, base.n
    if m == 1:
        return base, (lambda c: base.O(c))
    key = (ell, tuple(base.h.list()), m)
    if key in _BASE_EXT_CACHE:
        return _BASE_EXT_CACHE[key]
    Fl = GF(ell)
    d = n * m
    kk = GF(ell ** d, name='w')
    hbar = base.h.change_ring(Fl)
    if n == 1:
        rho = kk(0) if hbar.degree() == 0 else kk(-hbar[0] / hbar[1])
    else:
        rho = hbar.change_ring(kk).roots()[0][0]
    w = kk.gen()
    Xk = PolynomialRing(kk, 'X').gen()
    gbar = prod([Xk - w ** (ell ** (n * i)) for i in range(m)])
    V = matrix(Fl, [(rho ** i).polynomial().padded_list(d) for i in range(n)])
    Zt = base.Zt
    K = NumberField(base.h, 'th')
    th = K.gen()
    cf = []
    for c in gbar.list():
        sol = V.solve_left(vector(Fl, c.polynomial().padded_list(d)))
        cf.append(sum([QQ(ZZ(sol[i])) * th ** i for i in range(n)]))
    g = PolynomialRing(K, 'X')(cf)
    assert g.is_monic() and g.degree() == m
    L = K.extension(g, 'aa')
    Labs = L.absolute_field('bb')
    to_L, from_L = Labs.structure()
    alpha = from_L(L.gen())
    hp = alpha.minpoly()
    assert hp.degree() == d and hp.is_monic()
    assert hp.change_ring(Fl).is_irreducible(), "ell is not inert in Q(alpha)"
    nb = LiuBase(ell, Zt(hp))
    Bm = matrix(QQ, [(alpha ** i).vector() for i in range(d)])
    sol = Bm.solve_left(vector(QQ, from_L(L(th)).vector()))
    Theta = nb.O(Zt(list(sol)))
    assert nb.O(base.h(Theta)) == 0, "the embedding is not a ring homomorphism"

    def emb(c, base=base, nb=nb, Theta=Theta):
        cl = base.O(c).lift().list()
        return sum([nb.O(QQ(cl[i])) * Theta ** i for i in range(len(cl))], nb.O(0))

    _BASE_EXT_CACHE[key] = (nb, emb)
    return nb, emb


def embed_k(base, nb, emb, x):
    """the image in nb.k of x in base.k under the embedding ``emb``."""
    return nb.red(emb(base.lift_of(x)))


def embed_kpoly(base, nb, emb, F):
    """the image in nb.kT of F in base.kT."""
    X = nb.kT.gen()
    return nb.kT(sum([embed_k(base, nb, emb, c) * X ** i
                      for i, c in enumerate(F.list())]))


def embed_poly(base, nb, emb, p):
    """the image in nb.R of p in base.R."""
    out = nb.R(0)
    for (u, v), c in base.R(p).dict().items():
        out += emb(c) * nb.S ** u * nb.T ** v
    return out


# ---------------------------------------------------------------------------
# 1.  A chart  A = O[S,T]/(f - ell),  m = (S,T)
# ---------------------------------------------------------------------------

class LiuChart:
    r"""A = O[S,T]/(f(S,T) - ell) with f in (S,T); m = (S,T) is the point of
    interest.  ``divs`` records for each coordinate divisor V(S), V(T) the
    label of the component of the special fibre it is, or None."""

    def __init__(self, base, f, divs=None, name='', expr=None, prec=None):
        self.base = base
        self.R = base.R
        self.expr = expr        # (S, T) as rational functions on Z_0, or None
        self.prec = prec        # f known modulo total degree >= prec
        self.f = strunc(base, f, prec) if prec is not None else self.R(f)
        assert self.f.constant_coefficient() == 0, "f must lie in (S,T)"
        self.divs = dict(divs) if divs else {'S': None, 'T': None}
        self.name = name
        fbar = base.redpoly(self.f)
        assert fbar != 0, "f == 0 mod ell: not a 2-dimensional regular chart"
        self.fbar = fbar
        self.d = min(mn.degree() for mn in fbar.monomials())     # = ord_m(ell)
        self.fbar_d = sum(c * mn for c, mn in zip(fbar.coefficients(), fbar.monomials())
                          if mn.degree() == self.d)
        # multiplicities of V(S), V(T) in the special fibre: fbar = S^i T^j * unit
        sig, tau = base.sig, base.tau
        self.mult_S = min(e[0] for e in fbar.exponents())
        self.mult_T = min(e[1] for e in fbar.exponents())
        cof = fbar // (sig ** self.mult_S * tau ** self.mult_T)
        self.fbar_unit = cof
        # normal crossings at the origin: fbar = S^i T^j * unit.  Charts built
        # only to read an initial form may fail this; the flag is asserted
        # wherever the crossing structure is actually used.
        self.nc = (cof.constant_coefficient() != 0)

    def __repr__(self):
        return "LiuChart(%s: f=%s, d=%s, mult=(%s,%s), divs=%s)" % (
            self.name, self.f, self.d, self.mult_S, self.mult_T, self.divs)

    def _fpow(self, e):
        if e == 0:
            return self.R(1)
        if not hasattr(self, '_fpc'):
            self._fpc = {0: self.R(1)}
        if e not in self._fpc:
            q = self._fpow(e - 1) * self.f
            if self.prec is not None:
                q = strunc(self.base, q, self.prec)
            self._fpc[e] = q
        return self._fpc[e]

    def rf(self, p):
        """the image of p in the function field of Z_0 (needs ``expr``)."""
        assert self.expr is not None, "chart has no function-field expression"
        S0, T0 = self.expr
        F = S0.parent()
        out = F(0)
        for (u, v), c in self.R(p).dict().items():
            out += F(QQ(self.base.O(c).lift().constant_coefficient())) * S0 ** u * T0 ** v
        return out

    # -- ord and initial forms -----------------------------------------------

    def _terms(self, z):
        B = self.base
        out = []
        for (u, v), c in self.R(z).dict().items():
            if c == 0:
                continue
            e = B.oval(c)
            out.append(((u, v), c, e, e * self.d + u + v))
        return out

    def initial(self, z, cap=60):
        """(ord_m(z), initial form in k[sig,tau]) for z in O[S,T]."""
        B = self.base
        z = self.R(z)
        if z == 0:
            return (infinity, B.G(0))
        for _ in range(cap):
            W = self._terms(z)
            if not W:
                return (infinity, B.G(0))
            w0 = min(t[3] for t in W)
            form = B.G(0)
            for (u, v), c, e, w in W:
                if w == w0:
                    form += (B.red(c / B.ell ** e) * self.fbar_d ** e
                             * B.sig ** u * B.tau ** v)
            if form != 0:
                return (w0, form)
            znew = self.R(0)
            for (u, v), c, e, w in W:
                znew += (c / B.ell ** e) * self._fpow(e) * B.S ** u * B.T ** v
            if self.prec is not None:
                znew = strunc(B, znew, self.prec)
            assert znew != z, "initial(): rewriting made no progress"
            z = znew
        raise RuntimeError("initial(): did not terminate")

    def ord(self, z):
        return self.initial(z)[0]

    def depurate(self, z, cap=60):
        """a representative of z mod (f - ell) all of whose coefficients are
        ell-units; its minimal total degree is then ord_m(z)."""
        B = self.base
        z = self.R(z)
        if z == 0:
            return z
        for _ in range(cap):
            W = self._terms(z)
            if all(t[2] == 0 for t in W):
                return z
            znew = self.R(0)
            for (u, v), c, e, w in W:
                znew += (c / B.ell ** e) * self._fpow(e) * B.S ** u * B.T ** v
            if self.prec is not None:
                znew = strunc(B, znew, self.prec)
            assert znew != z, "depurate(): no progress"
            z = znew
        raise RuntimeError("depurate(): did not terminate")

    def clean_below(self, z, idx, bound, cap=None):
        r"""E130.  A convergent replacement for depurate() where only part of
        the answer is needed.  ``idx`` selects what is being bounded: None for
        the total degree, 0 or 1 for the exponent of S or T.  Only the terms
        whose value is < ``bound`` are rewritten.

        WHY THIS TERMINATES AND depurate() DOES NOT.  depurate() rewrites
        ell^e -> f^e on every coefficient that is not an ell-adic unit, and
        the substitution puts back powers of ell whenever f's own coefficients
        are not units -- which a translation T -> T + theta produces through
        the binomial coefficients (E129 (l)).  Here a term is rewritten only
        while its value is below the bound, and one rewriting raises that
        value by at least 1:

          idx is None:  the total degree grows by at least e >= 1, since f
                        lies in (S,T) and so has no constant term;
          idx = 0, 1 :  the exponent grows by at least e*fmin, where fmin is
                        the least exponent of that variable in f ITSELF.

        Note that fmin is not the multiplicity of V(S) resp. V(T) in the closed
        fibre: that is read off fbar = f mod ell, and a monomial of f whose
        coefficient is divisible by ell disappears there.  When fmin = 0 the
        rewriting cannot raise the exponent at all, and the old unbounded
        rewriting of depurate() is used instead -- which is exactly what ran
        before E130, and converges wherever it was already being used."""
        B = self.base
        z = self.R(z)
        if bound is None or bound <= 0:
            return z
        step = 1
        if idx is not None:
            step = min(e[idx] for e in self.f.exponents())
            if step == 0:
                return self.depurate(z)

        def key(e):
            return (e[0] + e[1]) if idx is None else e[idx]

        for _ in range(cap or (ZZ(bound) // step + 2)):
            if not any(key(e) < bound and B.oval(c) > 0
                       for e, c in z.dict().items()):
                return z
            znew = self.R(0)
            for e, c in z.dict().items():
                mon = B.S ** e[0] * B.T ** e[1]
                ev = B.oval(c)
                if key(e) < bound and ev > 0:
                    znew += (c / B.ell ** ev) * self._fpow(ev) * mon
                else:
                    znew += c * mon
            if self.prec is not None:
                znew = strunc(B, znew, self.prec)
            assert znew != z, "clean_below(): no progress"
            z = znew
        raise RuntimeError("clean_below(): did not terminate")

    # -- Lemma 2.10: the multiplicity lambda ---------------------------------

    def _candidates(self, r):
        B = self.base
        mons = [B.S ** i * B.T ** (r - i) for i in range(r + 1)]
        for tup in _iproduct(B.lifts(), repeat=r + 1):
            yield sum(t * mn for t, mn in zip(tup, mons))

    def lam(self, a, b, verbose=False):
        """lambda_m(B) for B = A[y]/(y^2+ay+b), with an optimal generator.
        Returns (lambda, a, b, c) where the new generator is y + c and
        min{2 ord a, ord b} = lambda.
        ell odd: complete the square (Prop. 2.6(2)); ell = 2: Lemma 2.10."""
        B = self.base
        a, b = self.R(a), self.R(b)
        if B.ell != 2:
            c = a / 2
            b = b - a ** 2 / 4
            a = self.R(0)
            return (self.ord(b), a, b, c)
        ctot = self.R(0)
        for _ in range(40):
            oa, ob = self.ord(a), self.ord(b)
            # E128 Addendum (2026-09-01).
            # Lemma 2.10(1) is tested BEFORE b is required to be
            # non-zero.  Definition 2.3 asks only that B be reduced, so
            # y^2+ay+b may factor over A; the translation that Lemma 2.10(2b)
            # prescribes then lands on a root and makes b vanish, and the
            # lemma's own case (1) returns 2 ord(a) = ord(Delta).  Testing the
            # assertion first aborted on that input instead.  b = a = 0 is the
            # non-reduced case, where lambda = +infinity (Prop. 2.6(3)) and
            # Definition 2.3 does not apply.
            if oa != infinity and 2 * oa <= ob:
                return (2 * oa, a, b, ctot)
            assert ob != infinity, "a = b = 0: the double cover is not reduced"
            if ob % 2 == 1:
                return (ob, a, b, ctot)       # odd degree: not a square
            r = ZZ(ob // 2)
            found = None
            for c in self._candidates(r):
                if c == 0:
                    continue
                if self.ord(b + a * c + c ** 2) > ob:
                    found = c
                    break
            if found is None:
                return (ob, a, b, ctot)
            if verbose:
                print("      lam: y -> y + (%s)" % found)
            b = b + a * found + found ** 2
            a = a + 2 * found
            ctot = ctot + found
        raise RuntimeError("lam(): did not terminate")

    # -- reduction along a coordinate divisor --------------------------------

    def red_modS(self, z):
        """image of z in A/(S) = k[X]  (valid when mult_S >= 1)."""
        B = self.base
        out = B.kT(0)
        X = B.kT.gen()
        for (u, v), c in self.R(z).dict().items():
            if u == 0:
                out += B.red(c) * X ** v
        return out

    def red_modT(self, z):
        B = self.base
        out = B.kT(0)
        X = B.kT.gen()
        for (u, v), c in self.R(z).dict().items():
            if v == 0:
                out += B.red(c) * X ** u
        return out

    def red_modm(self, z):
        """image of z in A/m = k."""
        return self.base.red(self.R(z).constant_coefficient())

    # -- blow-up (Prop. 3.1 and Prop. 3.3) -----------------------------------

    def blowup(self, a, b, r, which, theta0=None, newlabel=None):
        """The normalized blow-up at m = (S,T).
        which='S': chart D_+(s~), new coordinates (S, T1-theta0) with
                   T_old = S*(T_new+theta0);
        which='T': chart D_+(t~) at the point s1 = 0, S_old = T*S_new.
        Returns a new LiuChart together with (a1, b1)."""
        B = self.base
        S, T = B.S, B.T
        # E130: only the terms below the degree that is divided out have to
        # be cleaned, and cleaning only those terminates.  If ord_m(a) >= r
        # then after clean_below no term of a has degree < r at all: a clean
        # term of degree D < r would be the whole initial form at weight D
        # (the rewritten ones sit at weight >= d + r > D), forcing ord_m(a)=D.
        a = self.clean_below(a, None, r)
        b = self.clean_below(b, None, 2 * r)
        if which == 'S':
            th = B.O(0) if theta0 is None else B.O(theta0)
            sub = {S: S, T: S * (T + th)}
            fn = self.f.subs(sub)
            an = a.subs(sub)
            bn = b.subs(sub)
            div = S ** r
            div2 = S ** (2 * r)
            newdivs = {'S': newlabel,
                       'T': (self.divs['T'] if th == 0 else None)}
        elif which == 'T':
            sub = {S: T * S, T: T}
            fn = self.f.subs(sub)
            an = a.subs(sub)
            bn = b.subs(sub)
            div = T ** r
            div2 = T ** (2 * r)
            newdivs = {'S': self.divs['S'], 'T': newlabel}
        else:
            raise ValueError(which)
        a1 = _exact_div(an, div)
        b1 = _exact_div(bn, div2)
        ex = None
        if self.expr is not None:
            S0, T0 = self.expr
            if which == 'S':
                ex = (S0, T0 / S0 - QQ(B.O(th).lift().constant_coefficient()))
            else:
                ex = (S0 / T0, T0)
        ch = LiuChart(B, fn, newdivs, expr=ex, prec=self.prec,
                      name=(self.name + '/' + which +
                            ('' if theta0 is None else str(theta0))))
        return ch, a1, b1

    def translate_T(self, a, b, theta0):
        """move the origin to the point (S, T-theta0) of the chart."""
        B = self.base
        S, T = B.S, B.T
        th = B.O(theta0)
        sub = {S: S, T: T + th}
        ex = None
        if self.expr is not None:
            S0, T0 = self.expr
            ex = (S0, T0 - QQ(B.O(th).lift().constant_coefficient()))
        ch = LiuChart(B, self.f.subs(sub),
                      {'S': self.divs['S'], 'T': (self.divs['T'] if th == 0 else None)},
                      expr=ex, prec=self.prec, name=self.name + '@' + str(theta0))
        return ch, a.subs(sub), b.subs(sub)

    def extend(self, a, b, m):
        """base change to the unramified extension of degree m.  Returns
        (chart, a, b, nb, emb) so that the caller can lift its own data."""
        nb, emb = base_extension(self.base, m)
        def lift(p):
            return embed_poly(self.base, nb, emb, p)
        ch = LiuChart(nb, lift(self.f), self.divs, expr=self.expr, prec=self.prec,
                      name=self.name + '^%s' % m)
        return ch, lift(a), lift(b), nb, emb


def _exact_div(p, q):
    r = p // q
    assert r * q == p, "not divisible: %s / %s" % (p, q)
    return r




# ---------------------------------------------------------------------------
# 2.  Tracking a section (a rational point) through the blow-ups
# ---------------------------------------------------------------------------

def evalpt(base, poly, s, t):
    """value at (S,T)=(s,t) in QQ of a polynomial over O.  A tracked section
    has rational coordinates, so this is only ever needed when every
    coefficient lies in Z_(ell) inside O."""
    out = QQ(0)
    for (u, v), c in base.R(poly).dict().items():
        cl = base.O(c).lift()
        assert cl.degree() <= 0, \
            "section tracking through a coefficient outside Z_(ell): %s" % cl
        out += QQ(cl.constant_coefficient()) * s ** u * t ** v
    return out


class Section:
    """a Z_ell-point of the model, in the coordinates of the current chart."""

    def __init__(self, name, s, t, y, ell, w=None):
        self.name = name
        self.s, self.t, self.y = QQ(s), QQ(t), QQ(y)
        self.ell = ell
        self.w = w              # the coordinate of the next double cover
        self.trace = []

    def __repr__(self):
        return "Section(%s: S=%s T=%s y=%s)" % (self.name, self.s, self.t, self.y)

    def v(self, x):
        return infinity if x == 0 else QQ(x).valuation(self.ell)

    def at_origin(self):
        return self.v(self.s) > 0 and self.v(self.t) > 0

    def copy(self):
        Q = Section(self.name, self.s, self.t, self.y, self.ell, self.w)
        Q.trace = list(self.trace)
        return Q

    def shift_y(self, c):
        self.y = self.y - c

    def which_chart(self):
        """'S' if the section stays in D_+(s~) after blowing up (S,T)."""
        return 'S' if self.v(self.t) >= self.v(self.s) and self.s != 0 else 'T'

    def blowup(self, r, which):
        Q = self.copy()
        if which == 'S':
            Q.t = self.t / self.s
            Q.y = self.y / self.s ** r
        else:
            assert self.t != 0
            Q.s = self.s / self.t
            Q.y = self.y / self.t ** r
        assert Q.v(Q.s) >= 0 and Q.v(Q.t) >= 0 and Q.v(Q.y) >= 0, \
            "section left the model: %s" % Q
        Q.trace.append((which, r))
        return Q

    def translate_T(self, th):
        Q = self.copy()
        Q.t = self.t - QQ(th)
        return Q

    def theta0(self, base):
        return base.k(GF(self.ell)(self.t))


# ---------------------------------------------------------------------------
# 3.  The desingularization algorithm (Section 5.3) with bookkeeping
# ---------------------------------------------------------------------------

def ucov_push(B, ucov, sub, mono, r):
    """transport u = (nu1*y+nu0)/den through a chart change (sub) followed by
    y_old = mono^r * y_new."""
    n1, n0, dn = ucov
    return (B.R(n1.subs(sub)) * mono ** r, B.R(n0.subs(sub)), B.R(dn.subs(sub)))


class Node:
    """one closed point of some Z_i, with the local equation of Y_i over it."""

    def __init__(self, chart, a, b, pts=None, tag='', yc=None, ymu=None,
                 ucov=None, tcov=None, abprec=None):
        self.chart, self.a, self.b = chart, chart.R(a), chart.R(b)
        # E129 (a).  ``abprec`` is the total degree below which a and b are
        # exact: None when they are polynomials, an integer when they came out
        # of the power-series change of coordinates of round 2.  Every order
        # and every residue read off a and b is asserted to be below it.
        self.abprec = abprec
        # u = (nu1 * y + nu0) / den, the cover coordinate of the NEXT round
        R = chart.R
        self.ucov = ((R(1), R(0), R(1)) if ucov is None
                     else tuple(R(z) for z in ucov))
        # t = tnum / tden, the coordinate of the base P^1
        self.tcov = ((R(0), R(1)) if tcov is None else tuple(R(z) for z in tcov))
        self.pts = list(pts) if pts else []
        self.tag = tag
        self.lam = None
        self.local = None
        self.children = []
        # chart's y  =  (y_original - yc) / ymu   in the function field
        if chart.expr is not None:
            F = chart.expr[0].parent()
            self.yc = F(0) if yc is None else F(yc)
            self.ymu = F(1) if ymu is None else F(ymu)
        else:
            self.yc = self.ymu = None

    def __repr__(self):
        return "Node(%s, lam=%s, divs=%s)" % (self.tag, self.lam, self.chart.divs)


class Resolution:
    r"""Lipman's sequence for a normal double cover Y -> Z of a regular
    surface, following Section 5.3."""

    def __init__(self, base, verbose=False, all_rational=False, point_degree=1,
                 next_cover=False):
        self.base = base
        self.verbose = verbose
        self.all_rational = all_rational
        self.point_degree = point_degree
        # E129 (b2): run Section 5.2 at the generic point of every component of
        # the closed fibre of Y, for the double cover w^2 = u of the NEXT round
        self.next_cover = next_cover
        self.divs = {}
        self.regular = []
        self.nodes = []          # every node processed, blown up or not
        self.nextlabel = 0
        self.log = []

    def new_label(self, m, ename='', e=None, nbranch=None):
        lab = self.nextlabel
        self.nextlabel += 1
        self.divs[lab] = {'label': lab, 'm': m, 'name': ename, 'adj': set(),
                          'e': e, 'nbranch': nbranch,
                          'mult': (None if e is None else e * m),
                          'field_deg': 1}
        return lab

    def say(self, s):
        self.log.append(s)
        if self.verbose:
            print(s)

    # -- Section 5.2 ---------------------------------------------------------

    @staticmethod
    def _sing_candidates(ch, a1, b1, lam_parent, prec=None):
        r"""Section 5.2, cases (1), (2.1), (2.3), on the exceptional divisor
        V(S) of the blow-up chart.  ``prec`` is the total degree below which
        the PARENT's a and b are exact (None: exact).

        E129 (a).  The residues used here are read off the parent's a and b at
        one single total degree: with r = [lambda/2] and the substitution
        T -> S(T+theta), a monomial S^u T^v of a becomes S^{u+v}(T+theta)^v, so
        the image of a_1 = a/S^r in A/(S) = k[X] is determined by the
        coefficients of a in total degree exactly r, that of b_1 = b/S^{2r} by
        those of b in total degree exactly 2r, and that of b_1/S by those in
        total degree 2r+1.  Hence

            prec > 2r+1 = lambda + 1   ==>   every candidate below is exact,

        and Prop. 3.1(5)(b) then bounds their degrees by r, 2r and 2r+1
        respectively -- which is asserted, so a truncation that had corrupted
        the residues would have to do so without raising the degree."""
        B = ch.base
        r = ZZ(lam_parent) // 2
        assert prec is None or prec > 2 * r + 1, (
            "the candidates of Section 5.2 are read at total degree %s, but a "
            "and b are only exact below %s" % (2 * r + 1, prec))
        abar, bbar = ch.red_modS(a1), ch.red_modS(b1)
        assert abar == 0 or abar.degree() <= r, \
            "deg(abar) = %s > r = %s (Prop. 3.1(5b))" % (abar.degree(), r)
        assert bbar == 0 or bbar.degree() <= 2 * r, \
            "deg(bbar) = %s > 2r = %s (Prop. 3.1(5b))" % (bbar.degree(), 2 * r)
        if lam_parent % 2 == 1:
            assert abar == 0 and bbar == 0, "lambda odd but (abar,bbar) != (0,0)"
            g = ch.red_modS(_exact_div(ch.clean_below(b1, 0, 1), B.S))
            assert g != 0, "S^2 | b1: Y_1 would not be normal"
            assert g.degree() <= 2 * r + 1, \
                "deg(b1/S) = %s > 2r+1 = %s (Prop. 3.1(5b))" % (g.degree(), 2 * r + 1)
            return [F for F, _ in g.factor()]
        Dbar = abar ** 2 - 4 * bbar
        if Dbar != 0:
            assert Dbar.degree() <= 2 * r, \
                "deg(Dbar) = %s > 2r = %s (Prop. 3.1(5b))" % (Dbar.degree(), 2 * r)
            return [F for F, e in Dbar.factor() if e >= 2]
        assert B.ell == 2 and abar == 0 and bbar != 0
        dv = bbar.derivative()
        assert dv != 0, "bbar is a square: the generator was not optimal"
        return [F for F, _ in dv.factor()]

    # -- the driver ----------------------------------------------------------

    def run(self, roots):
        stack = list(roots)
        guard = 0
        while stack:
            guard += 1
            assert guard < 3000, "too many points examined"
            self.process(stack.pop(), stack)
        return self

    def process(self, nd, stack):
        self.nodes.append(nd)
        ch = nd.chart
        B = ch.base          # NOT self.base: a chart may live over an
                             # unramified extension of the resolution's base
        lam, a, b, ctr = ch.lam(nd.a, nd.b)
        assert nd.abprec is None or lam < nd.abprec, (
            "lambda = %s was read off a and b that are only exact below total "
            "degree %s" % (lam, nd.abprec))
        nd.lam, nd.a, nd.b = lam, a, b
        for P in nd.pts:
            P.shift_y(evalpt(B, ctr, P.s, P.t))
        if nd.yc is not None:
            nd.yc = nd.yc + nd.ymu * ch.rf(ctr)
        n1, n0, dn = nd.ucov
        nd.ucov = (n1, n0 + n1 * ctr, dn)
        self.say("  %-34s d=%s mult=(%s,%s) divs=%s lambda=%s pts=%s"
                 % (nd.tag, ch.d, ch.mult_S, ch.mult_T, ch.divs, lam,
                    [P.name for P in nd.pts]))
        if lam <= 1:
            abar, bbar = ch.red_modm(a), ch.red_modm(b)
            Y = PolynomialRing(B.k, 'Y').gen()
            pol = Y ** 2 + abar * Y + bbar
            if lam == 1:
                nd.local = {'npts': 1, 'degs': [1]}
            elif pol.is_irreducible():
                nd.local = {'npts': 1, 'degs': [2]}
            else:
                rts = [r for r, _ in pol.roots()]
                nd.local = {'npts': len(rts), 'degs': [1] * len(rts), 'roots': rts}
            for P in nd.pts:
                P.final = {'node': nd,
                           'S': B.k(GF(B.ell)(P.s)),
                           'T': B.k(GF(B.ell)(P.t)),
                           'y': B.k(GF(B.ell)(P.y))}
            self.regular.append(nd)
            return
        r = ZZ(lam // 2)
        m_new = ch.d
        lab = self.new_label(m_new, ename=nd.tag)
        for other in (ch.divs['S'], ch.divs['T']):
            if other is not None:
                self.divs[lab]['adj'].add(other)
                self.divs[other]['adj'].add(lab)
        if ch.divs['S'] is not None and ch.divs['T'] is not None:
            # blowing up their intersection point separates them
            self.divs[ch.divs['S']]['adj'].discard(ch.divs['T'])
            self.divs[ch.divs['T']]['adj'].discard(ch.divs['S'])
        ch0, a1, b1 = ch.blowup(a, b, r, 'S', theta0=0, newlabel=lab)
        assert ch0.mult_S == m_new, "multiplicity mismatch"
        abar, bbar = ch0.red_modS(a1), ch0.red_modS(b1)
        self.divs[lab]['abar'], self.divs[lab]['bbar'] = abar, bbar
        if lam % 2 == 1:
            e, nbr = 2, 1
        else:
            e = 1
            KX = FractionField(B.kT)
            Yv = PolynomialRing(KX, 'Y').gen()
            pol = Yv ** 2 + KX(abar) * Yv + KX(bbar)
            nbr = 1 if pol.is_irreducible() else 2
        uc0 = ucov_push(B, nd.ucov, {B.S: B.S, B.T: B.S * B.T}, B.S, r)
        self.divs[lab].update({'e': e, 'nbranch': nbr, 'mult': e * m_new,
                               'lam_parent': lam, 'kbase': B,
                               'chart0': (ch0, a1, b1),
                               'coord0': 'S', 'ucov0': uc0})
        self.say("    -> E%s: m=%s e=%s branches=%s mult=%s  abar=%s bbar=%s"
                 % (lab, m_new, e, nbr, e * m_new, abar, bbar))
        # points of E_lab that must be examined.  Three exact finite sets and
        # one optional heuristic:
        #   (i)   Section 5.2 on E_lab itself (the singular points of THIS
        #         round's cover), Prop. 3.1(5b) bounding the degrees;
        #   (ii)  the zeros of the discriminant along E_lab: where Theta -> E
        #         ramifies (which the arithmetic genus of Theta is read from)
        #         and where the two branches of a split Theta meet;
        #   (iii) Section 5.2 at the generic point of every component of
        #         Theta, for the double cover of the NEXT round (E129 (b2));
        #   (iv)  all closed points of degree <= point_degree (a heuristic,
        #         kept only for cross-checking: (i)-(iii) are exact).
        finite = set(self._sing_candidates(ch0, a1, b1, lam, nd.abprec))
        X = B.kT.gen()
        if ch.divs['T'] is not None:
            finite.add(X)
        finite |= component_ram_points(B, abar, bbar)
        if self.next_cover:
            finite |= component_next_cover_points(ch0, 'S', a1, b1, uc0,
                                                  prec=nd.abprec)
        if self.all_rational:
            for dgr in range(1, self.point_degree + 1):
                for F in B.kT.polynomials(of_degree=dgr):
                    if F.is_monic() and F.is_irreducible():
                        finite.add(F)
        chprec = None if nd.abprec is None else nd.abprec - 2 * r
        newpts, toinf = [], []
        for P in nd.pts:
            if P.which_chart() == 'S':
                Q = P.blowup(r, 'S')
                newpts.append(Q)
                finite.add(X - B.kT(Q.theta0(B)))
            else:
                toinf.append(P.blowup(r, 'T'))
        muS = None if nd.ymu is None else nd.ymu * ch.rf(B.S) ** r
        muT = None if nd.ymu is None else nd.ymu * ch.rf(B.T) ** r
        for F in sorted(finite, key=lambda g: (g.degree(), str(g))):
            self.push_point(nd, ch0, a1, b1, F, newpts, stack, lab, muS, r,
                            abprec=chprec)
        chI, aI, bI = ch.blowup(a, b, r, 'T', newlabel=lab)
        subI = {B.S: B.T * B.S, B.T: B.T}
        ucI = ucov_push(B, nd.ucov, subI, B.T, r)
        tcI = (B.R(nd.tcov[0].subs(subI)), B.R(nd.tcov[1].subs(subI)))
        ndI = Node(chI, aI, bI, toinf, tag=nd.tag + "|E%s@oo" % lab,
                   yc=nd.yc, ymu=muT, ucov=ucI, tcov=tcI, abprec=chprec)
        nd.children.append(ndI)
        stack.append(ndI)

    def push_point(self, nd, ch0, a1, b1, F, newpts, stack, lab, mu=None, r=0,
                   abprec=None):
        B = ch0.base
        if F.degree() == 1:
            th = -F.constant_coefficient() / F.leading_coefficient()
            lt = B.lift_of(th)
            ch2, a2, b2 = ch0.translate_T(a1, b1, lt)
            pts = [P.translate_T(QQ(B.O(lt).lift().constant_coefficient()))
                   for P in newpts if P.theta0(B) == th]
            sub2 = {B.S: B.S, B.T: B.S * (B.T + lt)}
            uc2 = ucov_push(B, nd.ucov, sub2, B.S, r)
            tc2 = (B.R(nd.tcov[0].subs(sub2)), B.R(nd.tcov[1].subs(sub2)))
            nd2 = Node(ch2, a2, b2, pts, tag=nd.tag + "|E%s@%s" % (lab, th),
                       yc=nd.yc, ymu=mu, ucov=uc2, tcov=tc2, abprec=abprec)
        else:
            m = F.degree()
            self.divs[lab]['field_deg'] = max(self.divs[lab]['field_deg'], m)
            che, ae, be, nb, emb = ch0.extend(a1, b1, m)
            th = embed_kpoly(B, nb, emb, F).roots()[0][0]
            ch2, a2, b2 = che.translate_T(ae, be, nb.lift_of(th))
            assert not any(P.theta0(B) in [rr for rr, _ in F.roots()] for P in newpts)
            lt2 = nb.lift_of(th)
            sub2 = {nb.S: nb.S, nb.T: nb.S * (nb.T + lt2)}
            uc2 = ucov_push(nb, tuple(embed_poly(B, nb, emb, z) for z in nd.ucov),
                            sub2, nb.S, r)
            tc2 = tuple(nb.R(embed_poly(B, nb, emb, z).subs(sub2))
                        for z in nd.tcov)
            nd2 = Node(ch2, a2, b2, [], tag=nd.tag + "|E%s@[%s]" % (lab, F),
                       ucov=uc2, tcov=tc2, abprec=abprec)
        nd.children.append(nd2)
        stack.append(nd2)


# ---------------------------------------------------------------------------
# 4.  Set-up: a Weierstrass-style double cover of P^1 over Z_ell
# ---------------------------------------------------------------------------

def normalize_over_line(base, a, b, verbose=False):
    """Section 5.1 at t = ell, for A = O[s] (a, b univariate over O).
    Returns (a, b, c, r) with the new generator z = (y - c)/ell^r."""
    ell = base.ell
    Rs = a.parent()
    ctot = Rs(0)
    scale = 0
    def val(p):
        return infinity if p == 0 else min(base.oval(co) for co in p.coefficients())
    for _ in range(40):
        va, vb = val(a), val(b)
        mn = min(2 * va, vb)
        r = 0 if mn == infinity else ZZ(mn) // 2
        if r > 0:
            a = a / ell ** r
            b = b / ell ** (2 * r)
            ctot = ctot / ell ** r
            scale += r
            continue
        va, vb = val(a), val(b)
        if not (va > 0 and vb == 0 and ell == 2):
            return (a, b, ctot, scale)
        bb = _to_kpoly(base, b)
        c = _sqrt_kpoly(base, bb)
        if c is None:
            return (a, b, ctot, scale)
        cl = _lift_kpoly(base, c, Rs)
        if verbose:
            print("    normalize: y -> y - (%s)" % cl)
        b = b + a * cl + cl ** 2
        a = a + 2 * cl
        ctot = ctot + cl
    raise RuntimeError("normalize_over_line(): did not terminate")


def _to_kpoly(base, p):
    X = base.kT.gen()
    return base.kT(sum([base.red(c) * X ** i for i, c in enumerate(p.list())]))


def _sqrt_kpoly(base, g):
    """square root of g in k[X] (char 2, k perfect), or None."""
    if base.ell != 2:
        return None
    L = g.list()
    if any(L[i] != 0 for i in range(1, len(L), 2)):
        return None
    X = base.kT.gen()
    return base.kT(sum([sqrt(L[2 * i]) * X ** i for i in range((len(L) + 1) // 2)]))


def _lift_kpoly(base, g, Rs):
    S = Rs.gen()
    return Rs(sum([base.lift_of(c) * S ** i for i, c in enumerate(g.list())]))


def line_singular_points(base, a, b):
    """Section 5.2, first part: the closed points of A^1_k over which Y is
    singular, when the closed fibre of Y is non-reduced.  a, b in O[s], with
    ell | a, ell | b, ell^2 not dividing b."""
    ell = base.ell
    q = b / ell
    g = _to_kpoly(base, q)
    assert g != 0, "ell^2 divides b: Y is not normal"
    return [F for F, _ in g.factor()]


# ---------------------------------------------------------------------------
# 5.  The closed fibre of Y_N: components, multiplicities, intersections
#     (Lemma 3.6, Prop. 3.7, Prop. 3.9)
# ---------------------------------------------------------------------------

def crossing_points(res):
    """for each pair of adjacent components of the special fibre of Z_N, the
    regular Node at which they meet."""
    out = {}
    for nd in res.regular:
        i, j = nd.chart.divs['S'], nd.chart.divs['T']
        if i is None or j is None:
            continue
        key = frozenset((i, j))
        assert nd.chart.nc, "non-normal-crossing chart at %s" % nd.tag
        assert key not in out, "components %s meet twice" % sorted(key)
        assert res.divs[i]['m'] == nd.chart.mult_S, "multiplicity mismatch at %s" % nd.tag
        assert res.divs[j]['m'] == nd.chart.mult_T, "multiplicity mismatch at %s" % nd.tag
        out[key] = nd
    return out


def fibre_components(res):
    """the list of components of the closed fibre of Y_N, as (label, branch)."""
    comps = []
    for lab in sorted(res.divs):
        for al in range(res.divs[lab]['nbranch']):
            comps.append((lab, al))
    return comps


def branch_selfmeetings(res, P=10):
    """for each split Theta_i, the points where its two branches meet, with
    the local intersection number."""
    nbr = {lab: res.divs[lab]['nbranch'] for lab in res.divs}
    out = {}
    for nd in res.regular:
        if nd.lam != 1:
            continue
        for co in ('S', 'T'):
            lab = nd.chart.divs[co]
            if lab is None or nbr[lab] != 2:
                continue
            out.setdefault(lab, 0)
            out[lab] += branch_selfmeet(nd, co, nbr, P=P)
    return out


def intersection_matrices(res, verbose=False, P=10):
    """all intersection matrices compatible with Prop. 3.9; the labelling of
    the two branches of a split Theta_i is only determined up to a swap, so
    every choice is returned.  Each entry is (matching, M, mults)."""
    comps = fibre_components(res)
    idx = {c: i for i, c in enumerate(comps)}
    n = len(comps)
    mult = vector(ZZ, [res.divs[lab]['mult'] for (lab, al) in comps])
    cross = crossing_points(res)
    # pairs needing a matching choice
    ambiguous = [k for k in cross if all(res.divs[l]['nbranch'] == 2 for l in k)]
    selfm = branch_selfmeetings(res, P=P)
    out = []
    for choice in _iproduct([0, 1], repeat=len(ambiguous)):
        M = matrix(ZZ, n, n)
        ok = True
        for key, nd in cross.items():
            i, j = sorted(key)
            ni, nj = res.divs[i]['nbranch'], res.divs[j]['nbranch']
            ei, ej = res.divs[i]['e'], res.divs[j]['e']
            if ni == 2 and nj == 2:
                sw = choice[ambiguous.index(key)]
                for al in range(2):
                    be = (al + sw) % 2
                    M[idx[(i, al)], idx[(j, be)]] += 1
                    M[idx[(j, be)], idx[(i, al)]] += 1
            elif ni == 2 or nj == 2:
                if ni == 1:
                    i, j, ni, nj, ei, ej = j, i, nj, ni, ej, ei
                assert ej == 1, "a split Theta adjacent to a ramified one"
                for al in range(2):
                    M[idx[(i, al)], idx[(j, 0)]] += 1
                    M[idx[(j, 0)], idx[(i, al)]] += 1
            else:
                val = ZZ(2 / (ei * ej))
                M[idx[(i, 0)], idx[(j, 0)]] += val
                M[idx[(j, 0)], idx[(i, 0)]] += val
        for lb, ip in selfm.items():
            M[idx[(lb, 0)], idx[(lb, 1)]] += ip
            M[idx[(lb, 1)], idx[(lb, 0)]] += ip
        for i in range(n):
            srow = sum(M[i, j] * mult[j] for j in range(n) if j != i)
            if srow % mult[i] != 0:
                ok = False
                break
            M[i, i] = -srow / mult[i]
        if ok:
            out.append((choice, M, mult))
    return comps, out


def genus_of_fibre(M, mult, genus):
    """p_a of the closed fibre:  g - 1 = (1/2) sum m_i (2 p_a(Gamma_i) - 2 - Gamma_i^2).
    Independent of the resolution, so a check that no singular point was missed."""
    n = M.nrows()
    tot = sum(mult[i] * (2 * genus[i] - 2 - M[i, i]) for i in range(n))
    assert tot % 2 == 0, "odd K.F"
    return ZZ(tot / 2) + 1


def fibre_report(M, mult):
    """the standard battery: M*m = 0, kernel exactly Q*m, negative
    semidefinite, |det M^(i)| = |Phi| m_i^2, and Phi = Z^n/im(M)."""
    n = M.nrows()
    rep = {}
    rep['symmetric'] = (M == M.transpose())
    rep['Mm'] = (M * mult == 0)
    rep['rank'] = M.rank()
    K = M.right_kernel().basis_matrix()
    rep['kernel_is_m'] = (K.nrows() == 1 and
                          [c / K[0][0] * mult[0] for c in K[0]] == list(mult))
    cp = M.charpoly()
    rep['neg_semidef'] = all(c >= 0 for c in cp.coefficients(sparse=False))
    D = M.smith_form()[0]
    els = [D[i, i] for i in range(n)]
    tors = [e for e in els if e not in (0, 1, -1)]
    rep['elementary_divisors'] = els
    rep['Phi'] = tors
    rep['Phi_order'] = prod([abs(e) for e in tors]) if tors else 1
    dets = []
    for i in range(n):
        rows = [j for j in range(n) if j != i]
        dets.append(abs(M[rows, rows].determinant()))
    rep['minor_test'] = all(dets[i] == rep['Phi_order'] * mult[i] ** 2
                            for i in range(n))
    rep['minors'] = dets
    rep['connected'] = (rep['rank'] == n - 1)
    return rep


def different_exponent(base, abar, bbar):
    """The exponent of the different at X = 0 of k[[X]][Y]/(Y^2+abar Y+bbar),
    a separable quadratic extension.  Tame: 1 if the discriminant has odd
    valuation, else 0.  Wild (ell=2): writing Y = abar Z the extension is the
    Artin-Schreier one Z^2+Z = bbar/abar^2, whose different exponent at a pole
    of odd order n is n+1."""
    kT = base.kT
    abar, bbar = kT(abar), kT(bbar)
    if base.ell != 2:
        D = abar ** 2 - 4 * bbar
        assert D != 0, "inseparable in odd characteristic"
        return 1 if D.valuation() % 2 == 1 else 0
    assert abar != 0, "purely inseparable: no different"
    va = abar.valuation()
    for _ in range(40):
        vb = bbar.valuation() if bbar != 0 else +Infinity
        if vb >= 2 * va:
            return 0
        n = 2 * va - vb
        if n % 2 == 1:
            return n + 1
        # bbar has an even-order pole relative to abar^2: translate it away
        c = sqrt((bbar >> vb)[0]) * kT.gen() ** ZZ(vb / 2)
        nb = bbar + abar * c + c ** 2
        assert nb != bbar
        bbar = nb
    raise RuntimeError("different_exponent(): did not terminate")


def theta_genus(res, lab):
    r"""The arithmetic genus p_a = 1 - chi(O) over res.base.k of a component of
    the closed fibre lying over the component E_lab of the base.

    e = 2, or Theta_lab split: Theta is isomorphic to E_lab (or is two copies
    of it), so p_a is that of E_lab.  Otherwise Theta -> E_lab is a degree 2
    cover and Riemann-Hurwitz gives p_a(Theta) = 2 p_a(E_lab) - 1 + deg(d)/2,
    the different being read off the local equations at the closed points of
    E_lab that the resolution visited.  A purely inseparable cover has no
    different and is handled through its function field, which is well defined
    because the local equations differ from chart to chart only by squares."""
    D = res.divs[lab]
    base_pa = D.get('base_pa', 0)
    if D['e'] == 2 or D['nbranch'] == 2:
        return base_pa
    ab, bb = D.get('abar'), D.get('bbar')
    if ab is None:
        return D.get('genus', base_pa)
    Bk = D.get('kbase', res.base)
    if Bk.ell == 2 and ab == 0:
        K = FunctionField(Bk.k, 'X')
        Yv = PolynomialRing(K, 'Y').gen()
        L = K.extension(Yv ** 2 + K(ab) * Yv + K(bb), 'Y')
        return L.genus()
    d = 0
    seen = 0
    for nd in res.regular:
        for co in ('S', 'T'):
            if nd.chart.divs[co] != lab:
                continue
            seen += 1
            deg = ZZ(nd.chart.base.n / res.base.n)
            red = nd.chart.red_modS if co == 'S' else nd.chart.red_modT
            d += different_exponent(nd.chart.base, red(nd.a), red(nd.b)) * deg
    assert seen > 0, "no visited point on E%s" % lab
    assert d % 2 == 0, (
        "odd different degree on E%s: the ramification count is incomplete, "
        "so some closed point of E%s was not visited -- run with "
        "all_rational=True and a large enough point_degree" % (lab, lab))
    return 2 * base_pa - 1 + ZZ(d / 2)


def contract_minus_ones(M, mult, genus, labels=None, verbose=False):
    """Castelnuovo: contract components with self-intersection -1 and
    arithmetic genus 0, until none is left."""
    M = matrix(ZZ, M)
    mult = list(mult)
    genus = list(genus)
    labels = list(labels) if labels is not None else list(range(M.nrows()))
    contracted = []
    while True:
        n = M.nrows()
        pick = None
        for i in range(n):
            if M[i, i] == -1 and genus[i] == 0:
                pick = i
                break
        if pick is None:
            return M, mult, genus, labels, contracted
        contracted.append(labels[pick])
        if verbose:
            print("    contract", labels[pick])
        keep = [j for j in range(n) if j != pick]
        N = matrix(ZZ, len(keep), len(keep))
        for x, j in enumerate(keep):
            for y, kk in enumerate(keep):
                N[x, y] = M[j, kk] + M[j, pick] * M[pick, kk]
        M = N
        mult = [mult[j] for j in keep]
        genus = [genus[j] for j in keep]
        labels = [labels[j] for j in keep]


KODAIRA_FIBRE = {
    'I0': ([1], []), 'I1': ([1], []), 'II': ([1], []),
    'III': ([1, 1], [2]), 'IV': ([1, 1, 1], [3]),
    'I0*': ([1, 1, 1, 1, 2], [2, 2]),
    'IV*': ([1, 1, 1, 2, 2, 2, 3], [3]),
    'III*': ([1, 1, 2, 2, 2, 3, 3, 4], [2]),
    'II*': ([1, 2, 2, 3, 3, 4, 4, 5, 6], []),
}


def kodaira_expected(code):
    """(sorted multiplicities, elementary divisors of Phi) for a PARI Kodaira
    code as returned by elllocalred (1=I0, 2=II, 3=III, 4=IV, 4+n -> I_n,
    -1 = I0*, -4-n -> I_n*, -2..-5 as in the PARI manual)."""
    if code == 1:
        return ([1], [])
    if code == 2:
        return KODAIRA_FIBRE['II']
    if code == 3:
        return KODAIRA_FIBRE['III']
    if code == 4:
        return KODAIRA_FIBRE['IV']
    if code >= 5:
        n = code - 4
        return (sorted([1] * n), [n] if n > 1 else [])
    if code == -1:
        return KODAIRA_FIBRE['I0*']
    if code == -2:
        return KODAIRA_FIBRE['II*']
    if code == -3:
        return KODAIRA_FIBRE['III*']
    if code == -4:
        return KODAIRA_FIBRE['IV*']
    n = -code - 4
    mults = sorted([1, 1, 1, 1] + [2] * (n + 1))
    phi = [2, 2] if n % 2 == 0 else [4]
    return (mults, phi)


# ---------------------------------------------------------------------------
# 6.  Round 1: a double cover of P^1 over Z_ell given by y^2 + a(s)y + b(s)
# ---------------------------------------------------------------------------

def _line_candidates(base, a, b):
    """Section 5.2 (first part) for A = O[s]: closed points of A^1_k over
    which Y may be singular.  Assumes Y normal."""
    ell = base.ell
    abar, bbar = _to_kpoly(base, a), _to_kpoly(base, b)
    Dbar = abar ** 2 - 4 * bbar
    if Dbar != 0:
        return [F for F, e in Dbar.factor() if e >= 2]
    assert ell == 2 and abar == 0
    c = _sqrt_kpoly(base, bbar)
    if c is not None:
        # non-reduced fibre: normalisation has already made ell | a, ell | b
        assert bbar == 0, "fibre non-reduced but b is a unit: not normalised"
        return line_singular_points(base, a, b)
    dv = bbar.derivative()
    assert dv != 0
    return [F for F, _ in dv.factor()]


class LineCover:
    """Y: y^2 + a(s) y + b(s) = 0 over Z_ell, a double cover of P^1 of genus g."""

    def __init__(self, base, a, b, g, sections=None, verbose=False,
                 all_rational=False, point_degree=1, next_cover=False):
        self.base = base
        self.g = g
        self.all_rational = all_rational
        self.point_degree = point_degree
        self.next_cover = next_cover
        Rs = PolynomialRing(base.O, 's')
        a, b = Rs(a), Rs(b)
        self.Rs = Rs
        self.Fs = FractionField(Rs)
        self.sections = list(sections) if sections else []   # (name, s0 or None, y0)
        self.verbose = verbose
        # affine chart
        self.a, self.b, self.c0, self.sc0 = normalize_over_line(base, a, b, verbose)
        # chart at infinity: x = 1/s, z = y/s^(g+1)
        ai = Rs(sum([a.list()[i] * Rs.gen() ** (g + 1 - i) for i in range(len(a.list()))]))
        bi = Rs(sum([b.list()[i] * Rs.gen() ** (2 * g + 2 - i) for i in range(len(b.list()))]))
        assert ai.degree() <= g + 1 and bi.degree() <= 2 * g + 2
        self.ai, self.bi, self.ci, self.sci = normalize_over_line(base, ai, bi, verbose)

    def _emb(self, p, sh):
        """p(s) with s = S + sh, as an element of O[S,T]."""
        B = self.base
        return B.R(sum([B.O(co) * (B.S + B.O(sh)) ** i
                        for i, co in enumerate(p.list())]))

    def _qval(self, p, x):
        """p(x) for a rational x; only used for tracked sections, whose
        coordinates are rational, so the coefficients must be too."""
        B = self.base
        out = QQ(0)
        for i, co in enumerate(p.list()):
            cl = B.O(co).lift()
            assert cl.degree() <= 0, "section tracking outside Z_(ell)"
            out += QQ(cl.constant_coefficient()) * QQ(x) ** i
        return out

    def resolution(self, extra_points=()):
        B = self.base
        sv = self.Fs.gen()
        res = Resolution(B, verbose=self.verbose, all_rational=self.all_rational,
                         point_degree=self.point_degree,
                         next_cover=self.next_cover)
        # E_0: the special fibre of Z_0
        abar, bbar = _to_kpoly(B, self.a), _to_kpoly(B, self.b)
        Yv = PolynomialRing(FractionField(B.kT), 'Y').gen()
        pol = Yv ** 2 + Yv * FractionField(B.kT)(abar) + FractionField(B.kT)(bbar)
        if abar == 0 and bbar == 0:
            e0, n0 = 2, 1
        else:
            e0, n0 = 1, (1 if pol.is_irreducible() else 2)
        lab0 = res.new_label(1, 'E0', e=e0, nbranch=n0)
        res.divs[lab0]['abar'], res.divs[lab0]['bbar'] = abar, bbar
        # which points of A^1_k to examine.  As in Resolution.process:
        # Section 5.2 on E_0 itself, the zeros of the discriminant along E_0,
        # and Section 5.2 at the generic point of every component of Theta_0
        # for the cover of the next round.  E_0 = V(ell) of the chart
        # A = O[s] with f = T, so the component is V(T) and X = S = s.
        finite = set(_line_candidates(B, self.a, self.b))
        X = B.kT.gen()
        ch0e = LiuChart(B, B.T, {'S': None, 'T': lab0}, name='E0')
        a0e, b0e = self._emb(self.a, 0), self._emb(self.b, 0)
        uc0e = (B.R(B.ell ** self.sc0), self._emb(self.c0, 0), B.R(1))
        res.divs[lab0].update({'chart0': (ch0e, a0e, b0e), 'coord0': 'T',
                               'ucov0': uc0e, 'lam_parent': None})
        finite |= component_ram_points(B, abar, bbar)
        if self.next_cover:
            finite |= component_next_cover_points(ch0e, 'T', a0e, b0e, uc0e)
        if self.all_rational:
            for dgr in range(1, self.point_degree + 1):
                for F in B.kT.polynomials(of_degree=dgr):
                    if F.is_monic() and F.is_irreducible():
                        finite.add(F)
        for F in extra_points:
            finite.add(B.kT(F))
        secs_fin, secs_inf = [], []
        for sec in self.sections:
            nm, s0, y0 = sec[0], sec[1], sec[2]
            w0 = sec[3] if len(sec) > 3 else None
            if s0 is None or QQ(s0).valuation(B.ell) < 0:
                x0 = 0 if s0 is None else 1 / QQ(s0)
                z0 = (QQ(y0) * x0 ** (self.g + 1) - self._qval(self.ci, x0)) / B.ell ** self.sci
                secs_inf.append(Section(nm, x0, QQ(B.ell), z0, B.ell, w=w0))
                assert QQ(x0).valuation(B.ell) > 0
            else:
                yy = (QQ(y0) - self._qval(self.c0, s0)) / B.ell ** self.sc0
                secs_fin.append((QQ(s0),
                                 Section(nm, QQ(s0), QQ(B.ell), yy, B.ell, w=w0)))
                finite.add(X - B.kT(B.k(GF(B.ell)(QQ(s0)))))
        roots = []
        for F in sorted(finite, key=lambda gg: (gg.degree(), str(gg))):
            if F.degree() == 1:
                th = -F.constant_coefficient() / F.leading_coefficient()
                s0 = B.O(B.lift_of(th))
                ch = LiuChart(B, B.T, {'S': None, 'T': lab0},
                              expr=(sv - s0, self.Fs(B.ell)), name="s=%s" % th)
                pts = [P.translate_T(0) for (v, P) in secs_fin
                       if B.k(GF(B.ell)(v)) == th]
                if pts:
                    assert s0.lift().degree() <= 0, \
                        "a rational section over a non-rational point"
                    for P in pts:
                        P.s = P.s - QQ(s0.lift().constant_coefficient())
                roots.append(Node(ch, self._emb(self.a, s0), self._emb(self.b, s0),
                                  pts, tag="s=%s" % th,
                                  ucov=(B.R(B.ell ** self.sc0),
                                        self._emb(self.c0, s0), B.R(1)),
                                  tcov=(B.S + s0, B.R(1))))
            else:
                # a closed point of A^1_k of degree > 1: base-change and move
                # one of its geometric points to the origin
                nb, emb = base_extension(B, F.degree())
                th = embed_kpoly(B, nb, emb, F).roots()[0][0]
                lt = nb.lift_of(th)
                assert not any(B.k(GF(B.ell)(v)) in [r for r, _ in F.roots()]
                               for (v, P) in secs_fin)
                chn = LiuChart(nb, nb.T, {'S': None, 'T': lab0},
                               expr=(sv, self.Fs(B.ell)), name="s=[%s]" % F)
                sub = {nb.S: nb.S + lt, nb.T: nb.T}
                aa = embed_poly(B, nb, emb, self._emb(self.a, 0)).subs(sub)
                bb = embed_poly(B, nb, emb, self._emb(self.b, 0)).subs(sub)
                roots.append(Node(chn, aa, bb, [], tag="s=[%s]" % F,
                                  ucov=(nb.R(B.ell ** self.sc0),
                                        embed_poly(B, nb, emb,
                                                   self._emb(self.c0, 0)).subs(sub),
                                        nb.R(1)),
                                  tcov=(nb.S + lt, nb.R(1))))
        ch = LiuChart(B, B.T, {'S': None, 'T': lab0},
                      expr=(1 / sv, self.Fs(B.ell)), name="s=oo")
        roots.append(Node(ch, self._emb(self.ai, 0), self._emb(self.bi, 0),
                          secs_inf, tag="s=oo", ymu=sv ** (self.g + 1),
                          ucov=(B.R(B.ell ** self.sci), self._emb(self.ci, 0),
                                B.S ** (self.g + 1)),
                          tcov=(B.R(1), B.S)))
        res.run(roots)
        return res


def analyse(res, verbose=False, P=10):
    """assemble the closed fibre; returns the list of valid (choice, M, mult,
    genus, comps) with M negative semidefinite, connected, kernel = Q m."""
    comps, Ms = intersection_matrices(res, P=P)
    gen = [theta_genus(res, lab) for (lab, al) in comps]
    good = []
    for (choice, M, mult) in Ms:
        rep = fibre_report(M, mult)
        if rep['connected'] and rep['neg_semidef'] and rep['kernel_is_m'] \
                and rep['minor_test']:
            good.append((choice, M, mult, gen, comps, rep))
    return comps, Ms, good


# ---------------------------------------------------------------------------
# 7.  Round 2: charts of the regular model Y_N produced by round 1
#
# At a closed point p of Y_N lying over the closed point q of Z_N (the origin
# of a chart A = O[S,T]/(f-ell)), the completed local ring of Y_N is again of
# the normal form O'[[S2,T2]]/(f2-ell):
#   lambda_q = 0 (etale, Prop. 2.9(1)):  (S2,T2) = (S,T) and f2 = f, while the
#       cover coordinate y is a Hensel root of Y^2+aY+b over the point;
#   lambda_q = 1 (ramified):  ord_m(b) = 1, so b is part of a regular system of
#       parameters (b,c) of A downstairs and (y,c) is one of B upstairs
#       (Prop. 2.9(2)); the remaining old coordinate is solved for by Newton's
#       method and f2 is f composed with that solution.
# ---------------------------------------------------------------------------

def strunc(base, p, P):
    out = base.R(0)
    for (u, v), c in base.R(p).dict().items():
        if u + v < P:
            out += c * base.S ** u * base.T ** v
    return out


def oinv(base, c):
    c = base.O(c)
    assert base.oval(c) == 0, "not a unit: %s" % c
    inv = base.O(1) / c
    assert base.oval(inv) == 0
    return inv


def homog_part(base, p, d):
    out = base.R(0)
    for (u, v), c in base.R(p).dict().items():
        if u + v == d:
            out += c * base.S ** u * base.T ** v
    return out


def solve_series_deg(base, Gfun, alpha, P):
    """solve G(X) = 0 in O[[S,T]] degree by degree, given that G(0) has no
    constant term and dG/dX(0,0) = alpha is a unit."""
    ainv = oinv(base, alpha)
    X = base.R(0)
    for d in range(1, P):
        G = strunc(base, Gfun(X), d + 1)
        Gd = homog_part(base, G, d)
        if Gd != 0:
            X = X - ainv * Gd
    assert strunc(base, Gfun(X), P) == 0, "solve_series_deg: residual"
    return X


def lift_form(chart, form, o):
    """a polynomial sum c_ij S^i T^j of degree o whose initial form is
    ``form`` in k[sig,tau]_o."""
    B = chart.base
    out = B.R(0)
    for c, mn in zip(form.coefficients(), form.monomials()):
        e = mn.exponents()[0]
        assert e[0] + e[1] == o, "inhomogeneous initial form"
        out += B.lift_of(c) * B.S ** e[0] * B.T ** e[1]
    return out


def solve_in_chart(chart, Gfun, alpha, N):
    """solve G(X) = 0 in A = O[[S,T]]/(f-ell) order by order (ord_m), given
    ord(G(X0)) >= 1 and dG/dX(m) = alpha a unit."""
    B = chart.base
    abar = B.red(alpha)
    assert abar != 0
    X = B.R(0)
    for _ in range(N + 2):
        o, form = chart.initial(Gfun(X))
        if o >= N:
            return X
        X = X - lift_form(chart, form / abar, o)
    raise RuntimeError("solve_in_chart(): did not converge")


class EPoint:
    """a closed point of the regular model produced by round 1, with a chart
    in normal form and the cover coordinate u of the next double cover."""

    def __init__(self, node, chart2, a2, b2, divs2, resfield_deg, rho, tag):
        self.node, self.chart2 = node, chart2
        self.a2, self.b2 = a2, b2
        self.divs2 = divs2                 # {'S': (lab,br) or None, 'T': ...}
        self.resfield_deg = resfield_deg
        self.rho = rho
        self.tag = tag
        self.pts = []

    def __repr__(self):
        return "EPoint(%s, divs=%s)" % (self.tag, self.divs2)


def epoints_over(node, nbranch=None, P=16, verbose=False):
    """the closed points of Y_N over the origin of ``node``'s chart, each with
    a normal-form chart and the transported cover data (nu1*y+nu0)/den."""
    ch = node.chart
    B = ch.base
    S, T = B.S, B.T
    a, b = node.a, node.b
    nu1, nu0, den = node.ucov
    out = []
    if node.lam == 1:
        bd = ch.clean_below(b, None, 2)
        ad = ch.clean_below(a, None, 2)
        alpha, beta = B.O(0), B.O(0)
        for (u, v), c in bd.dict().items():
            if (u, v) == (1, 0):
                alpha = c
            elif (u, v) == (0, 1):
                beta = c
        # (b, c) is a regular system of parameters of A downstairs for
        # c = T (if the S-coefficient of b is a unit) or c = S (if the
        # T-coefficient is), and then (y, c) is one of B upstairs
        # (Prop. 2.9(2)).  When both are available, keep as a coordinate the old
        # one that cuts out a component of the closed fibre: otherwise the
        # component is not a coordinate axis, the chart is not
        # normal-crossing, and Section 5.1 below would normalise at the wrong
        # primes -- which loses normality and makes Lipman's sequence run for
        # ever.
        def solve_keep_T():
            # (S2,T2) = (y, T_old); solve S_old = Sigma(y,T)
            def val(X):
                return strunc(B, bd.subs({S: X, T: T}) + S ** 2
                              + ad.subs({S: X, T: T}) * S, P)
            Sig = solve_series_deg(B, val, alpha, P)
            return {S: Sig, T: T}, False
        def solve_keep_S():
            # (S2,T2) = (y, S_old); solve T_old = Tau(y,S)
            def val(X):
                return strunc(B, bd.subs({S: T, T: X}) + S ** 2
                              + ad.subs({S: T, T: X}) * S, P)
            Tau = solve_series_deg(B, val, beta, P)
            return {S: T, T: Tau}, True
        okS = (B.oval(alpha) == 0)      # can solve for S_old, keeping T_old
        okT = (B.oval(beta) == 0)       # can solve for T_old, keeping S_old
        assert okS or okT, "ord(b) = 1 but b has no unit linear term"
        order = []
        if ch.divs['S'] is not None and okT:
            order.append(solve_keep_S)   # keep S_old: it is a component
        if ch.divs['T'] is not None and okS:
            order.append(solve_keep_T)   # keep T_old: it is a component
        if okS:
            order.append(solve_keep_T)
        if okT:
            order.append(solve_keep_S)
        sub = swap = f2 = None
        first = None
        for solver in order:
            sub_c, swap_c = solver()
            f2_c = strunc(B, ch.f.subs(sub_c), P)
            if first is None:
                first = (sub_c, swap_c, f2_c)
            if LiuChart(B, f2_c, prec=P).nc:
                sub, swap, f2 = sub_c, swap_c, f2_c
                break
        if sub is None:
            # no choice is normal-crossing; callers that need that structure
            # (make_epoints) check chart2.nc themselves, callers that only read
            # an initial form (branch_selfmeet) do not care
            sub, swap, f2 = first
        ysub = S
        n1 = strunc(B, nu1.subs(sub), P)
        n0 = strunc(B, nu0.subs(sub), P)
        dn = strunc(B, den.subs(sub), P)
        num = strunc(B, n1 * ysub + n0, P)
        b2 = -strunc(B, num * dn, P)
        dS = ch.divs['S'] if not swap else ch.divs['T']
        dT = ch.divs['T'] if not swap else ch.divs['S']
        # V(S2) = V(y) lies over the divisor solved away; V(T2) over the other
        def brr(dd):
            # at a ramified point both branches of a split Theta pass through
            return None if (nbranch is not None and nbranch[dd] == 2) else 0
        divs2 = {'S': (dS, brr(dS)) if dS is not None else None,
                 'T': (dT, brr(dT)) if dT is not None else None}
        ch2 = LiuChart(B, f2, {'S': None, 'T': None}, prec=P,
                       expr=ch.expr, name=node.tag + "^ram")
        epx = EPoint(node, ch2, B.R(0), b2, divs2, 1, None, node.tag + "^ram")
        epx.ucov2 = (num, dn)
        epx.tcov2 = (strunc(B, node.tcov[0].subs(sub), P),
                     strunc(B, node.tcov[1].subs(sub), P))
        epx.sub, epx.swap = sub, swap
        epx.old_S = B.R(sub[S])
        epx.old_T = B.R(sub[T])
        for Pt in node.pts:
            Q = (Section(Pt.name, Pt.y, Pt.t, 0, B.ell) if not swap
                 else Section(Pt.name, Pt.y, Pt.s, 0, B.ell))
            Q.w = Pt.w
            Q.y = Q.w * evalpt(B, dn, Q.s, Q.t)
            epx.pts.append(Q)
        out.append(epx)
        return out
    assert node.lam == 0
    tcov = node.tcov
    abar, bbar = ch.red_modm(a), ch.red_modm(b)
    Yv = PolynomialRing(B.k, 'Y').gen()
    pol = Yv ** 2 + abar * Yv + bbar
    assert B.ell != 2 or abar != 0, \
        "lambda = 0 with abar = 0 over a perfect residue field"
    roots = [r for r, _ in pol.roots()]
    rdeg = 1
    if not roots:
        # the point of Y_N has residue degree 2: base-change and take one root
        Bold = B
        ch, a, b, nb, emb = ch.extend(a, b, 2)
        B = ch.base
        S, T = B.S, B.T
        nu1 = embed_poly(Bold, nb, emb, nu1)
        nu0 = embed_poly(Bold, nb, emb, nu0)
        den = embed_poly(Bold, nb, emb, den)
        tcov = tuple(embed_poly(Bold, nb, emb, z) for z in node.tcov)
        Yv = PolynomialRing(B.k, 'Y').gen()
        pol = Yv ** 2 + ch.red_modm(a) * Yv + ch.red_modm(b)
        roots = [r for r, _ in pol.roots()][:1]
        rdeg = 2
    for i, rho in enumerate(roots):
        rl = B.lift_of(rho)
        def val(X, a=a, b=b, rl=rl):
            return (X + rl) ** 2 + a * (X + rl) + b
        Y = rl + solve_in_chart(ch, val, 2 * rl + a.constant_coefficient(), P)
        num = strunc(B, nu1 * Y + nu0, P)
        b2 = -strunc(B, num * den, P)
        def br(lab):
            return 0 if (nbranch is None or nbranch[lab] == 1) else i
        divs2 = {'S': (ch.divs['S'], br(ch.divs['S'])) if ch.divs['S'] is not None else None,
                 'T': (ch.divs['T'], br(ch.divs['T'])) if ch.divs['T'] is not None else None}
        ch2 = LiuChart(B, ch.f, {'S': None, 'T': None}, expr=ch.expr, prec=P,
                       name=node.tag + "^et%s" % i)
        epx = EPoint(node, ch2, B.R(0), b2, divs2, rdeg, rho,
                     node.tag + "^et%s" % i)
        epx.ucov2 = (num, den)
        epx.tcov2 = tcov
        epx.sub, epx.swap = {S: S, T: T}, False
        epx.old_S, epx.old_T = S, T
        for Pt in node.pts:
            if B.k(GF(B.ell)(Pt.y)) != rho:
                continue
            Q = Section(Pt.name, Pt.s, Pt.t, 0, B.ell)
            Q.w = Pt.w
            Q.y = Q.w * evalpt(B, den, Q.s, Q.t)
            epx.pts.append(Q)
        out.append(epx)
    return out


def local_split(base, abar, bbar):
    """Is Y^2 + abar Y + bbar reducible over k[[X]]?  (k perfect.)"""
    kT = base.kT
    abar, bbar = kT(abar), kT(bbar)
    if base.ell != 2:
        D = abar ** 2 - 4 * bbar
        if D == 0:
            return None
        v = D.valuation()
        if v % 2 == 1:
            return False
        return (D >> v)[0].is_square()
    if abar == 0:
        return _sqrt_kpoly(base, bbar) is not None
    va = abar.valuation()
    if bbar == 0:
        return True
    vb = bbar.valuation()
    if vb < 2 * va:
        return False
    if vb > 2 * va:
        return True
    c = (bbar >> vb)[0] / ((abar >> va)[0]) ** 2
    return c.trace() == 0


def normalize_chart(chart, a, b, coords=('S', 'T'), verbose=False, secs=(),
                    ucov=None, shift=None):
    """Section 5.1 in a normal-form chart, at the coordinate divisors.
    ``shift`` (a list, E129 (a)) collects the exponents r of the divisions
    y -> y/coord^r: b loses 2r degrees of precision at each of them."""
    B = chart.base
    a, b = chart.R(a), chart.R(b)
    for _ in range(30):
        changed = False
        for co in coords:
            g = B.S if co == 'S' else B.T
            co_i = 0 if co == 'S' else 1
            mult = chart.mult_S if co == 'S' else chart.mult_T
            va, vb = _coordval(chart, a, g), _coordval(chart, b, g)
            mn = min(2 * va, vb)
            r = 0 if mn == infinity else ZZ(mn) // 2
            if r > 0:
                a = _exact_div(chart.clean_below(a, co_i, r), g ** r)
                b = _exact_div(chart.clean_below(b, co_i, 2 * r), g ** (2 * r))
                for P in secs:
                    P.y = P.y / ((P.s if co == 'S' else P.t) ** r)
                if ucov is not None:
                    ucov = (ucov[0] * g ** r, ucov[1], ucov[2])
                changed = True
                if shift is not None:
                    shift.append(r)
                if verbose:
                    print("      normalize: y -> y/%s^%s" % (co, r))
                continue
            if mult == 0 or B.ell != 2:
                continue
            va, vb = _coordval(chart, a, g), _coordval(chart, b, g)
            if not (va > 0 and vb == 0):
                continue
            bb = chart.red_modS(b) if co == 'S' else chart.red_modT(b)
            c = _sqrt_kpoly(B, bb)
            if c is None:
                continue
            other = B.T if co == 'S' else B.S
            cl = B.R(sum([B.lift_of(cc) * other ** i
                          for i, cc in enumerate(c.list())]))
            for P in secs:
                P.y = P.y - evalpt(B, cl, P.s, P.t)
            if ucov is not None:
                ucov = (ucov[0], ucov[1] + ucov[0] * cl, ucov[2])
            b = b + a * cl + cl ** 2
            a = a + 2 * cl
            changed = True
            if verbose:
                print("      normalize: y -> y - (%s)" % cl)
        if not changed:
            return (a, b) if ucov is None else (a, b, ucov)
    raise RuntimeError("normalize_chart(): did not terminate")


def _coordval(chart, z, g):
    r"""the g-adic valuation in A of z (g = S or T).

    E130.  Once every term whose g-exponent is at most the least g-exponent of
    a term with unit coefficient has been cleaned, that least exponent IS the
    valuation: the terms with a non-unit coefficient then contribute
    nu_g >= their exponent > it, and the unit ones of exactly that exponent
    give a non-zero residue in A/(g) = k[X], distinct monomials not being able
    to cancel.  Cleaning only those terms terminates (LiuChart.clean_below),
    which the full depurate() need not."""
    B = chart.base
    z = chart.R(z)
    if z == 0:
        return infinity
    i = 0 if g == B.S else 1
    mult = chart.mult_S if i == 0 else chart.mult_T
    if mult == 0:
        # V(g) is not a component of the closed fibre; the rewriting cannot
        # raise the g-exponent, so fall back to rewriting every term.
        return min(e[i] for e in chart.depurate(z).exponents())
    for _ in range(60):
        clean = [e[i] for e, c in z.dict().items() if B.oval(c) == 0]
        dirty = [e[i] for e, c in z.dict().items() if B.oval(c) > 0]
        if not dirty:
            return min(clean)
        if clean and min(dirty) > min(clean):
            return min(clean)
        z = chart.clean_below(z, i, (min(clean) if clean else min(dirty)) + 1)
    raise RuntimeError("_coordval(): did not terminate")


# ---------------------------------------------------------------------------
# 8.  Round 2: the double cover w^2 = u of the model built in round 1
# ---------------------------------------------------------------------------

def make_epoints(res1, P=10, verbose=False):
    """all closed points of the round-1 model Y_N, with normalised round-2
    cover data w^2 = u, and a chart-independent fingerprint for the component
    of the closed fibre each coordinate divisor is."""
    nbr = {lab: res1.divs[lab]['nbranch'] for lab in res1.divs}
    out = []
    for nd in res1.regular:
        for ep in epoints_over(nd, nbranch=nbr, P=P, verbose=verbose):
            ch2 = ep.chart2
            R2 = ch2.R
            shift = []
            a2, b2, wc = normalize_chart(ch2, ep.a2, ep.b2, verbose=verbose,
                                         secs=ep.pts, shift=shift,
                                         ucov=(R2(1), R2(0), R2(ep.ucov2[1])))
            ep.abprec = P - 2 * sum(shift)
            ep.wcov = wc
            ep.a2, ep.b2 = a2, b2
            ep.ucov2n = ep.ucov2
            assert ep.chart2.nc, \
                "the chart of Y_N at %s is not normal-crossing: the components " \
                "of the closed fibre are not the coordinate axes there, and " \
                "Section 5.1 would normalise at the wrong primes" % ep.tag
            for co in ('S', 'T'):
                assert ep.divs2[co] is None or ep.divs2[co][1] is not None, \
                    "a split component of the round-1 fibre passes through a " \
                    "ramified point of Y_N -> Z_N (%s)" % ep.tag
            out.append(ep)
    return out


def branch_selfmeet(node, coord, nbranch, P=10):
    """At a regular point p of Y where the two branches of a split
    psi^{-1}(Gamma) meet (Gamma = V(coord) of the chart), the local
    intersection number of the two branches: ord_p(varpi_Gamma) is 2 and the
    two branches are the two factors of its initial form."""
    eps = epoints_over(node, nbranch=nbranch, P=P)
    assert len(eps) == 1, "the branches do not meet at this point"
    ep = eps[0]
    g = ep.old_S if coord == 'S' else ep.old_T
    o, form = ep.chart2.initial(g)
    assert o == 2, "ord of the component equation is %s, not 2" % o
    fac = form.factor()
    assert all(e == 1 for _, e in fac) and len(fac) == 2, \
        "branches are tangent (initial form %s): not implemented" % form
    return 1


def ucov_valuations(ep, kappas=(0, 1, -1, 2, -2, 3, -3),
                    ldegs=(0, 1, 2, 3, 4), tdegs=(0, 1, 2)):
    r"""The fingerprint (nu_Gamma(u - kappa * ell^j * t^i))_{kappa,j,i} of each
    coordinate divisor Gamma of the chart.  Each entry is a valuation of K(Z)
    evaluated on a function of K(Z), so it is independent of the chart and
    identifies the component -- in particular it tells the two branches of a
    split Theta apart, which the local branch index does not.

    Powers of ell are essential.  On an exceptional divisor E_i created over a
    point s = s_0 of the base, the function t is constant (= s_0) along E_i,
    so a family kappa*t^i alone takes the same value on both branches; ell is
    what varies along E_i."""
    ch, B = ep.chart2, ep.chart2.base
    num, den = ep.ucov2
    tn, td = ep.tcov2
    fp = {}
    for co, g in (('S', B.S), ('T', B.T)):
        if ep.divs2[co] is None:
            continue
        vd = _coordval(ch, den, g)
        vtd = _coordval(ch, td, g)
        vals = []
        for i in tdegs:
            for j in ldegs:
                for kp in kappas:
                    # u - kappa ell^j t^i
                    #   = (num*td^i - kappa*ell^j*den*tn^i) / (den*td^i)
                    z = num * td ** i - B.O(kp) * B.ell ** j * den * tn ** i
                    vals.append(_coordval(ch, z, g) - vd - i * vtd)
        fp[co] = tuple(vals)
    return fp


def branch_gluings(res1, eps):
    """Split components of the round-1 fibre carry a local branch index at
    each point, assigned chart by chart.  Fix them by the fingerprint
    nu_Gamma(u - kappa t^j) where it separates the two branches, and report
    the remaining freedom: one Z/2 per node beyond the first, per component."""
    for ep in eps:
        if not hasattr(ep, 'fp'):
            ep.fp = ucov_valuations(ep)
        if not hasattr(ep, 'locbr'):
            ep.locbr = {co: (None if ep.divs2[co] is None else ep.divs2[co][1])
                        for co in ('S', 'T')}
    fps, nodes = {}, {}
    for ep in eps:
        for co in ('S', 'T'):
            if ep.divs2[co] is None:
                continue
            l = ep.divs2[co][0]
            fps.setdefault(l, set()).add(ep.fp[co])
            nodes.setdefault(l, set()).add(ep.node.tag)
    free = {}
    fixed = {}
    for l in sorted(fps):
        nbr = res1.divs[l]['nbranch']
        if nbr == 1:
            continue
        if len(fps[l]) == nbr:
            fixed[l] = {f: i for i, f in enumerate(sorted(fps[l]))}
        else:
            free[l] = sorted(nodes[l])
    return fixed, free


def apply_gluing(res1, eps, flips):
    """set ep.divs2 branch indices from the fingerprint (where it separates)
    or from the supplied per-node flips."""
    fixed, free = branch_gluings(res1, eps)
    for ep in eps:
        for co in ('S', 'T'):
            if ep.divs2[co] is None:
                continue
            l, i = ep.divs2[co][0], ep.locbr[co]
            if res1.divs[l]['nbranch'] == 1:
                ep.divs2[co] = (l, 0)
            elif l in fixed:
                ep.divs2[co] = (l, fixed[l][ep.fp[co]])
            else:
                ep.divs2[co] = (l, (i + flips.get((l, ep.node.tag), 0)) % 2)


def round2(res1, P=10, verbose=False, flips=None, eps=None):
    """Liu's algorithm for the double cover w^2 = u of the model built by
    round 1.  Returns (res2, labels) where ``labels`` maps a component
    (lab, branch) of the round-1 closed fibre to the round-2 divisor label."""
    B = res1.base
    flips = flips or {}
    if eps is None:
        eps = make_epoints(res1, P=P, verbose=verbose)
    comps1 = fibre_components(res1)
    # The local branch index of a split component of the round-1 fibre is
    # assigned chart by chart and need not be consistent.  Identify the
    # branches by nu_Gamma(u - kappa), a valuation on K(Z) and so independent
    # of the chart; then relabel.
    apply_gluing(res1, eps, flips)
    lab = {c: i for i, c in enumerate(comps1)}
    res2 = Resolution(B, verbose=verbose)
    for c in comps1:
        res2.new_label(res1.divs[c[0]]['mult'], ename=str(c))
        res2.nextlabel = lab[c] + 1
    # e and nbranch of the round-2 cover along each component
    info = {}
    for ep in eps:
        ch = ep.chart2
        Bx = ch.base
        for co, g in (('S', Bx.S), ('T', Bx.T)):
            if ep.divs2[co] is None:
                continue
            c = ep.divs2[co]
            red = ch.red_modS if co == 'S' else ch.red_modT
            ab, bb = red(ep.a2), red(ep.b2)
            va, vb = _coordval(ch, ep.a2, g), _coordval(ch, ep.b2, g)
            mn = min(2 * va, vb)
            assert mn <= 1, "the cover is not normalised along %s" % (c,)
            if mn == 1:
                e, nbr = 2, 1
            else:
                e = 1
                nbr = 2 if local_split(Bx, ab, bb) else 1
            if c in info:
                assert info[c][0] == e, \
                    "inconsistent ramification along %s: %s vs %s (%s)" % (
                        c, info[c][0], e, ep.tag)
                # a component is irreducible as soon as it is so at one point
                info[c] = (e, min(info[c][1], nbr), info[c][2], info[c][3],
                           info[c][4])
            else:
                info[c] = (e, nbr, ab, bb, Bx)
    for c in comps1:
        assert c in info, "no chart sees the component %s" % (c,)
        e, nbr, ab, bb, kb = info[c]
        d = res2.divs[lab[c]]
        d['e'], d['nbranch'], d['mult'] = e, nbr, e * d['m']
        d['abar'], d['bbar'], d['kbase'] = ab, bb, kb
        d['base_pa'] = theta_genus(res1, c[0])
    # adjacency of the initial divisors, from the round-1 crossings
    for ep in eps:
        if ep.divs2['S'] is not None and ep.divs2['T'] is not None:
            i, j = lab[ep.divs2['S']], lab[ep.divs2['T']]
            res2.divs[i]['adj'].add(j)
            res2.divs[j]['adj'].add(i)
    roots = []
    for ep in eps:
        ch = ep.chart2
        ch.divs = {'S': lab[ep.divs2['S']] if ep.divs2['S'] else None,
                   'T': lab[ep.divs2['T']] if ep.divs2['T'] else None}
        roots.append(Node(ch, ep.a2, ep.b2, pts=ep.pts, tag=ep.tag,
                          ucov=ep.wcov, tcov=ep.tcov2,
                          abprec=getattr(ep, 'abprec', None)))
    res2.run(roots)
    return res2, lab, eps


def local_pairing(M, mult, classes, base):
    """Gross's vertical local pairing: for each class c solve M a = -(e_c-e_b)
    and return Lambda_{c,k} = a^{(c)} . (e_k - e_b)."""
    n = M.nrows()
    idx = list(classes)
    L = matrix(QQ, len(idx), len(idx))
    for i, c in enumerate(idx):
        d = vector(QQ, [0] * n)
        d[c] += 1
        d[base] -= 1
        assert sum(d[j] * mult[j] for j in range(n)) == 0, "d is not orthogonal to m"
        a = M.change_ring(QQ).solve_right(-d)
        for j, k in enumerate(idx):
            ek = vector(QQ, [0] * n)
            ek[k] += 1
            ek[base] -= 1
            L[i, j] = a * ek
    return L


def point_components(res2, comps2, P=10):
    """For each tracked section, the component of the closed fibre it meets.
    On a split Theta the branch is fixed by the fingerprint of the branch's own
    valuation (ucov_valuations applied to the points of the next cover), so
    that sections at different closed points of the same Theta are compared
    consistently -- the local root order is not consistent by itself."""
    nbr = {lab: res2.divs[lab]['nbranch'] for lab in res2.divs}
    fpid = {}
    out = {}
    for nd in res2.regular:
        if not nd.pts:
            continue
        k = nd.chart.base.k
        ell = nd.chart.base.ell
        hit = []
        for co in ('S', 'T'):
            lab = nd.chart.divs[co]
            if lab is None:
                continue
            val = nd.pts[0].s if co == 'S' else nd.pts[0].t
            if k(GF(ell)(val)) == 0:
                hit.append(lab)
        assert len(hit) == 1, "a section meets %s components at %s" % (len(hit), nd.tag)
        lab = hit[0]
        if nbr[lab] == 1:
            for Pt in nd.pts:
                out[Pt.name] = {'comp': comps2.index((lab, 0)), 'node': nd.tag,
                                'red': (k(GF(ell)(Pt.s)), k(GF(ell)(Pt.t)),
                                        k(GF(ell)(Pt.y))),
                                'mult': res2.divs[lab]['mult']}
            continue
        # split: identify the branch through each section by its fingerprint
        brs = epoints_over(nd, nbranch=nbr, P=P)
        for ep in brs:
            fp = ucov_valuations(ep)
            key = fp['S'] if ep.divs2['S'] is not None else fp['T']
            fpid.setdefault(lab, [])
            if key not in fpid[lab]:
                fpid[lab].append(key)
            al = fpid[lab].index(key)
            for Pt in nd.pts:
                if k(GF(ell)(Pt.y)) != ep.rho:
                    continue
                out[Pt.name] = {'comp': comps2.index((lab, al)), 'node': nd.tag,
                                'red': (k(GF(ell)(Pt.s)), k(GF(ell)(Pt.t)),
                                        k(GF(ell)(Pt.y))),
                                'mult': res2.divs[lab]['mult']}
    for lab in fpid:
        assert len(fpid[lab]) <= 2, "more than two branches on E%s" % lab
    return out


def round2_search(res1, g, P=10, verbose=False):
    """Run round 2 over all gluings of the branch labels that the fingerprint
    does not fix, and keep the models that pass the standard battery and have
    the right arithmetic genus."""
    eps = make_epoints(res1, P=P, verbose=verbose)
    fixed, free = branch_gluings(res1, eps)
    keys = []
    for l in sorted(free):
        for nd in free[l][1:]:          # the first node fixes the labelling
            keys.append((l, nd))
    good = []
    for bits in _iproduct([0, 1], repeat=len(keys)):
        flips = dict(zip(keys, bits))
        try:
            res2, lab, _ = round2(res1, P=P, flips=flips, eps=eps)
            comps2, Ms2, ok = analyse(res2, P=P)
        except AssertionError as ex:
            if verbose:
                print("   gluing %s rejected: %s" % (bits, ex))
            continue
        for (choice, M, mu, gen, cps, rep) in ok:
            pa = genus_of_fibre(M, mu, gen)
            if pa == g:
                good.append((flips, res2, M, mu, gen, cps, rep))
    return eps, keys, good


# ---------------------------------------------------------------------------
# 9.  E129: Section 5.2 at the GENERIC point of a component
#
# E128 looked for the singular points of the next double cover among the closed
# points of degree <= 2 of each component of the closed fibre.  That is a
# heuristic, and it is what the [GAP] of E128 (i) recorded.  Section 5.2 is
# however a prescription for an EXACT finite candidate set, and it can be run
# at the generic point of a component Gamma of psi^{-1}(E): the candidates are
# then the zeros of an explicit element of k(Gamma) -- a divisor, not a bound.
# Pushing them down along Gamma -> E (a norm, the extension having degree <= 2)
# describes them by polynomials in k[X], which is what the resolution knows how
# to visit, at any degree.
#
# What is returned is a SUPERSET of the singular points.  That is deliberate:
# every candidate is visited and its lambda computed exactly, so a regular
# candidate costs time and nothing else, while a superset removes the two
# places where the intrinsic locus would otherwise be cut out by a
# chart-dependent function.  Both are repaired by adding zeros:
#   * Section 5.1 divides by a power of a uniformizer of Gamma, which is a
#     choice; the residues then live in k(Gamma) with denominators, and the
#     zeros of those denominators are added;
#   * Section 5.2 (2.3) reads a differential against dX, whose divisor on
#     Gamma is the different of Gamma -> E; its support is added.
#
# Three cases, following Prop. 3.7 and Lemma 3.2, for B = A[y]/(y^2+a_1y+b_1)
# localised at the generic point of a component of psi^{-1}(V(g)):
#
#   'ram'    abar = bbar = 0, and normality forces nu_E(b_1) = 1.  Then y is a
#            uniformizer, e_Gamma = 2 and k(Gamma) = k(X).  For z = z0 + z1 y,
#            nu_Gamma(z0) = 2 nu_E(z0) and nu_Gamma(z1 y) = 2 nu_E(z1) + 1 have
#            different parities, so no cancellation is possible and both
#            nu_Gamma and the residue are closed formulas.
#   'inert'  Y^2 + abar Y + bbar irreducible over k(X).  Then 1 and Y are a
#            k(X)-basis of k(Gamma), so a residue vanishes only when both of
#            its coordinates do: again no cancellation, and nu_Gamma is the
#            minimum of two valuations of A.
#   'split'  reducible.  This is the only case where cancellation can occur --
#            the residues of z0 and z1 y can cancel against each other -- and
#            it is dealt with by Hensel-lifting the branch rho to a root
#            rho~ = p/q of y^2+a_1y+b_1 in the localisation of A, far enough
#            that nu_Gamma(y - rho~) exceeds every order that is read off.
#            Then nu_Gamma(z0 + z1 y) = nu_E(z0 q + z1 p) - nu_E(q), which is
#            an inequality the code asserts and, if it fails, repairs by one
#            more Newton step.
# ---------------------------------------------------------------------------


def component_ram_points(base, abar, bbar):
    r"""The closed points of a component E of the closed fibre over which
    psi^{-1}(E) -> E ramifies, or over which the two branches of a split
    psi^{-1}(E) meet: the zeros of the discriminant abar^2 - 4 bbar (in
    characteristic 2 the zeros of abar).  Both are needed even when no point
    there is singular -- the first because the arithmetic genus of the
    component is read off the different at the visited points, the second
    because the self-intersection of a split Theta is.

    An identically vanishing discriminant returns the empty set: then either
    abar = bbar = 0, so e = 2 and Theta = E, or char = 2 and Theta -> E is
    purely inseparable; in both cases there is no different and no pair of
    branches."""
    D = abar ** 2 - 4 * bbar
    if D == 0:
        return set()
    return set(F.monic() for F, _ in D.factor() if F.degree() >= 1)


def _kf_sqrt(base, x):
    """a square root of x in k(X) (char 2, k perfect), or None."""
    KX = FractionField(base.kT)
    x = KX(x)
    if x == 0:
        return KX(0)
    N, D = x.numerator(), x.denominator()
    r = _sqrt_kpoly(base, N * D)
    if r is None:
        return None
    return KX(r) / KX(D)


def _kf_zeros(base, x):
    """the monic irreducible factors of the numerator and of the denominator
    of a non-zero x in k(X)."""
    KX = FractionField(base.kT)
    x = KX(x)
    assert x != 0, "the zero function has no zero divisor"
    out = set()
    for g in (x.numerator(), x.denominator()):
        if g.degree() < 1:
            continue
        for F, _ in g.factor():
            out.add(F.monic())
    return out


def _gb_mul(a1, b1, u, v):
    """(u0 + u1 y)(v0 + v1 y) modulo y^2 + a1 y + b1."""
    t = u[1] * v[1]
    return (u[0] * v[0] - t * b1, u[0] * v[1] + u[1] * v[0] - t * a1)


class GenericComponent:
    r"""The discrete valuation nu_Gamma at the generic point of one component
    Gamma of psi^{-1}(E), E = V(g) being a component of the closed fibre of
    ``chart`` (g = S or T) and X the remaining coordinate."""

    def __init__(self, chart, coord, a1, b1, kind, root=None):
        B = chart.base
        self.chart, self.coord, self.B, self.R = chart, coord, B, chart.R
        self.g = B.S if coord == 'S' else B.T
        self.gi = 0 if coord == 'S' else 1
        self.other = B.T if coord == 'S' else B.S
        self.redc = chart.red_modS if coord == 'S' else chart.red_modT
        self.a1, self.b1 = self.R(a1), self.R(b1)
        self.KX = FractionField(B.kT)
        self.abar, self.bbar = self.redc(self.a1), self.redc(self.b1)
        self.kind = kind
        mult = chart.mult_S if coord == 'S' else chart.mult_T
        assert mult >= 1, "V(%s) is not a component of the closed fibre" % coord
        if kind == 'ram':
            assert self.abar == 0 and self.bbar == 0
            assert self.val(self.b1) == 1, \
                "nu_E(b_1) = %s: the cover is not normal along the component" \
                % self.val(self.b1)
            self.e = 2
            # y^2 = g * w with w = -(a_1/g) y - b_1/g, and nu_Gamma of the
            # first term is >= 1, so res_Gamma(y^2/g) = -res_E(b_1/g) =: c
            self.c = self.KX(-self.resid(self.b1, 1))
            assert self.c != 0
        elif kind == 'split':
            self.e = 1
            self._set_root(root)
        else:
            self.e = 1
            assert not (B.ell == 2 and self.abar == 0), \
                "a purely inseparable component: not implemented"

    def __repr__(self):
        return "GenericComponent(%s, V(%s), %s)" % (self.chart.name, self.coord,
                                                    self.kind)

    # -- the base ring A ----------------------------------------------------

    def val(self, z):
        """nu_E(z) = the g-adic valuation in A."""
        z = self.R(z)
        return infinity if z == 0 else _coordval(self.chart, z, self.g)

    def resid(self, z, n):
        """the image of z/g^n in A/(g) = k[X]; 0 when nu_E(z) > n.
        E130: cleaning only the terms of g-exponent < n terminates, and if
        nu_E(z) >= n it leaves no term below n at all."""
        z = self.chart.clean_below(self.R(z), self.gi, n + 1)
        if z == 0:
            return self.B.kT(0)
        v = min(e[self.gi] for e in z.exponents())
        if v > n:
            return self.B.kT(0)
        assert v == n, "a residue was asked below the valuation (%s < %s)" % (v, n)
        return self.redc(_exact_div(z, self.g ** n))

    def klift_poly(self, gpoly):
        """a lift of gpoly in k[X] to O[X] inside R."""
        B = self.B
        return sum([B.lift_of(c) * self.other ** i
                    for i, c in enumerate(B.kT(gpoly).list())], self.R(0))

    def _trunc_g(self, z, N):
        """drop the monomials of z whose g-exponent is >= N (they change the
        element of A by something of nu_E >= N)."""
        out = self.R(0)
        for e, c in self.R(z).dict().items():
            if e[self.gi] < N:
                out += c * self.B.S ** e[0] * self.B.T ** e[1]
        return out

    # -- the split case: Hensel lift of the branch --------------------------

    def _set_root(self, r):
        r = self.KX(r)
        self.p = self.klift_poly(r.numerator())
        self.q = self.klift_poly(r.denominator())
        self._root_data()

    def _root_data(self):
        assert self.val(self.q) == 0, "the branch is not integral"
        e = self.p ** 2 + self.a1 * self.p * self.q + self.b1 * self.q ** 2
        self.vroot = self.val(e)
        assert self.vroot >= 1, "the two branches are not distinct mod g"

    def refine(self):
        """one Newton step for the branch: p/q -> (p^2-b_1q^2)/(q(2p+a_1q)),
        which doubles nu_Gamma(y - p/q)."""
        p, q = self.p, self.q
        N = 2 * self.vroot + 2
        self.p = self._trunc_g(p ** 2 - self.b1 * q ** 2, N)
        self.q = self._trunc_g(q * (2 * p + self.a1 * q), N)
        old = self.vroot
        self._root_data()
        assert self.vroot > old, "the Newton step made no progress"

    # -- nu_Gamma and the residue in k(Gamma) -------------------------------

    def vr(self, z0, z1):
        """(nu_Gamma(z), res_Gamma(z/pi^nu)) for z = z0 + z1 y in B."""
        z0, z1 = self.R(z0), self.R(z1)
        if z0 == 0 and z1 == 0:
            return (infinity, None)
        if self.kind == 'ram':
            v0, v1 = self.val(z0), self.val(z1)
            n0 = infinity if v0 is infinity else 2 * v0
            n1 = infinity if v1 is infinity else 2 * v1 + 1
            if n0 < n1:
                return (n0, self.KX(self.resid(z0, v0)) / self.c ** v0)
            return (n1, self.KX(self.resid(z1, v1)) / self.c ** v1)
        if self.kind == 'inert':
            v0, v1 = self.val(z0), self.val(z1)
            n = min(v0, v1)
            return (n, (self.KX(self.resid(z0, n)), self.KX(self.resid(z1, n))))
        # split
        vz1 = self.val(z1)
        for _ in range(10):
            Z = z0 * self.q + z1 * self.p
            n = self.val(Z)
            if n is not infinity and self.vroot + vz1 > n:
                return (n, self.KX(self.resid(Z, n)))
            self.refine()
        raise RuntimeError("vr(): the branch could not be lifted far enough")

    # -- arithmetic in k(Gamma) ---------------------------------------------

    def kzero(self):
        return (self.KX(0), self.KX(0)) if self.kind == 'inert' else self.KX(0)

    def kis_zero(self, x):
        if self.kind == 'inert':
            return x[0] == 0 and x[1] == 0
        return x == 0

    def kmul(self, x, y):
        if self.kind != 'inert':
            return x * y
        ab, bb = self.KX(self.abar), self.KX(self.bbar)
        t = x[1] * y[1]
        return (x[0] * y[0] - t * bb, x[0] * y[1] + x[1] * y[0] - t * ab)

    def ksub(self, x, y):
        if self.kind != 'inert':
            return x - y
        return (x[0] - y[0], x[1] - y[1])

    def kscal(self, x, c):
        if self.kind != 'inert':
            return x * c
        return (x[0] * c, x[1] * c)

    def knorm(self, x):
        """N_{k(Gamma)/k(X)}(x)."""
        if self.kind != 'inert':
            return self.KX(x)
        ab, bb = self.KX(self.abar), self.KX(self.bbar)
        return x[0] ** 2 - ab * x[0] * x[1] + bb * x[1] ** 2

    def kinv(self, x):
        if self.kind != 'inert':
            return 1 / x
        N = self.knorm(x)
        assert N != 0
        ab = self.KX(self.abar)
        return ((x[0] - x[1] * ab) / N, -x[1] / N)

    def ksqrt(self, x):
        """a square root of x in k(Gamma) (char 2), or None.  With Y^2 = abar Y
        + bbar, (g0+g1Y)^2 = (g0^2 + g1^2 bbar) + g1^2 abar Y."""
        B = self.B
        assert B.ell == 2
        if self.kind != 'inert':
            return _kf_sqrt(B, x)
        ab, bb = self.KX(self.abar), self.KX(self.bbar)
        assert ab != 0
        g1 = _kf_sqrt(B, x[1] / ab)
        if g1 is None:
            return None
        g0 = _kf_sqrt(B, x[0] + g1 ** 2 * bb)
        if g0 is None:
            return None
        return (g0, g1)

    def kderiv(self, x):
        """d/dX on k(Gamma).  Y' is obtained from 2YY' + abar'Y + abar Y' +
        bbar' = 0."""
        if self.kind != 'inert':
            return self.KX(x).derivative()
        ab, bb = self.KX(self.abar), self.KX(self.bbar)
        num = (-bb.derivative(), -ab.derivative())          # -(abar' Y + bbar')
        den = (ab, self.KX(2))                              # 2Y + abar
        Yp = self.kmul(num, self.kinv(den))
        return self.ksub((x[0].derivative(), x[1].derivative()),
                         self.kscal(Yp, -x[1]))

    def klift(self, x):
        """(P0, P1, Q) in R^3 with (P0 + P1 y)/Q of residue x and nu_Gamma 0."""
        if self.kind != 'inert':
            x = self.KX(x)
            return (self.klift_poly(x.numerator()), self.R(0),
                    self.klift_poly(x.denominator()))
        D = x[0].denominator().lcm(x[1].denominator())
        return (self.klift_poly((x[0] * D).numerator()),
                self.klift_poly((x[1] * D).numerator()),
                self.klift_poly(D))

    def pi_pow(self, m):
        """pi^m as (z0, z1) in B; pi = y when e_Gamma = 2, else g."""
        R = self.R
        if self.kind == 'ram':
            out = (R(1), R(0))
            for _ in range(m):
                out = _gb_mul(self.a1, self.b1, out, (R(0), R(1)))
            return out
        return (self.g ** m, R(0))

    # -- fractions (z0 + z1 y)/d --------------------------------------------

    def fmul(self, x, y):
        w = _gb_mul(self.a1, self.b1, (x[0], x[1]), (y[0], y[1]))
        return (w[0], w[1], x[2] * y[2])

    def fadd(self, x, y):
        return (x[0] * y[2] + y[0] * x[2], x[1] * y[2] + y[1] * x[2], x[2] * y[2])

    def fnu(self, x):
        n1, r1 = self.vr(x[0], x[1])
        if n1 is infinity:
            return (infinity, None)
        n2, r2 = self.vr(x[2], self.R(0))
        assert n2 is not infinity, "zero denominator"
        return (n1 - n2, self.kmul(r1, self.kinv(r2)))

    # -- Section 5.1 and Section 5.2 at the generic point -------------------

    def normalise_next(self, ucov, cap=40):
        r"""Section 5.1 along Gamma for the double cover of the next round.
        w^2 = u = (nu1 y + nu0)/den is cleared to W^2 + A W + B = 0 with
        W = w * den, A = 0, B = -(nu1 y + nu0) * den, and then normalised.

        The division y -> y/pi^r of Section 5.1 is not carried out: the
        exponent rho is carried instead, so that the pair actually normalised
        is (A/pi^rho, B/pi^{2rho}).  That keeps every element in B (no
        uniformizer is ever inverted) and makes the residues read off at the
        top level the residues of the normalised pair.

        Returns (nA, resA, nB, resB): the orders of the normalised A and B
        along Gamma and their leading residues in k(Gamma)."""
        R = self.R
        nu1, nu0, den = [R(z) for z in ucov]
        A = (R(0), R(0), R(1))
        Bb = (-nu0 * den, -nu1 * den, R(1))
        rho = 0
        for _ in range(cap):
            nA, rA = self.fnu(A)
            nB, rB = self.fnu(Bb)
            if nA is not infinity:
                nA = nA - rho
            if nB is not infinity:
                nB = nB - 2 * rho
            assert nA is infinity or nA >= 0, "A is not integral along Gamma"
            assert nB is infinity or nB >= 0, "B is not integral along Gamma"
            mn = min(2 * nA, nB) if nA is not infinity else nB
            assert mn is not infinity, "B = 0: the next cover is not reduced"
            r = ZZ(mn) // 2
            if r > 0:
                rho += r
                continue
            if self.B.ell == 2 and nA > 0 and nB == 0:
                c = self.ksqrt(rB)
                if c is not None:
                    P0, P1, Q = self.klift(c)
                    pw = self.pi_pow(rho)
                    C = self.fmul((P0, P1, Q), (pw[0], pw[1], R(1)))
                    Bb = self.fadd(self.fadd(Bb, self.fmul(A, C)),
                                   self.fmul(C, C))
                    A = self.fadd(A, (2 * C[0], 2 * C[1], C[2]))
                    continue
            return (nA, rA, nB, rB)
        raise RuntimeError("normalise_next(): Section 5.1 did not terminate")

    def next_cover_candidates(self, ucov, verbose=False):
        r"""Section 5.2 at the generic point of Gamma: the closed points of E
        below the points of Gamma over which the next double cover can fail to
        be regular.  Exact and finite."""
        nA, rA, nB, rB = self.normalise_next(ucov)
        a0 = rA if nA == 0 else self.kzero()
        out = set()
        # The uniformizer pi of Gamma is a choice, and the residues below are
        # read against it.  Two choices differ by a unit u at the generic point
        # of Gamma, and the criteria of Section 5.2 are then multiplied by a
        # power of the restriction ubar; a point where ubar has a zero or a
        # pole could be lost.  Those points are exactly where pi fails to be a
        # local equation of Gamma, i.e. where div(pi) - Gamma meets Gamma:
        #   e = 1:  pi = g, and div_Y(g) is Gamma when Theta is irreducible and
        #           Gamma + Gamma' when it is split, so the meeting points are
        #           the zeros of the discriminant -- which the caller adds
        #           through component_ram_points;
        #   e = 2:  pi = y, and 2 div(y) = div(g) + div(w) = 2 Gamma + div(w)
        #           with w = -(a_1/g) y - b_1/g regular and of residue c, so
        #           div(y) - Gamma is supported on the zeros of c.
        if self.kind == 'ram' and self.c.denominator().degree() + \
                self.c.numerator().degree() > 0:
            out |= _kf_zeros(self.B, self.c)
        if nB % 2 == 1:
            # Section 5.2 (2.1): pi | A, pi | B, pi^2 does not divide B
            assert nB == 1
            kind, wit = '(2.1)', rB
            out |= self.kzeros(rB)
        else:
            b0 = rB if nB == 0 else self.kzero()
            Dbar = self.ksub(self.kmul(a0, a0), self.kscal(b0, 4))
            if not self.kis_zero(Dbar):
                # Section 5.2 (1): the multiple factors of the discriminant.
                # All of its factors are kept: the simple ones are where the
                # next cover ramifies, which its arithmetic genus needs.
                kind, wit = '(1)', Dbar
                out |= self.kzeros(Dbar)
            else:
                # Section 5.2 (2.3): char 2, bbar not a square; the candidates
                # are the zeros of the differential d(bbar).  Read against dX,
                # whose divisor on Gamma is the different of Gamma -> E, so
                # that support is added.
                assert self.B.ell == 2 and self.kis_zero(a0)
                assert self.ksqrt(b0) is None, \
                    "bbar is a square: Section 5.1 was not driven to the end"
                kind, wit = '(2.3)', self.kderiv(b0)
                out |= self.kzeros(wit)
                out |= component_ram_points(self.B, self.abar, self.bbar)
        self.case = kind          # which branch of Section 5.2 was taken
        self.orders = (nA, nB)
        if verbose:
            print("      generic %s: nA=%s nB=%s -> Section 5.2 %s, %s points"
                  % (self, nA, nB, kind, len(out)))
        return out

    def kzeros(self, x):
        """the closed points of E below the zeros of x in k(Gamma): the
        factors of the numerator and of the denominator of the norm."""
        assert not self.kis_zero(x)
        return _kf_zeros(self.B, self.knorm(x))


def component_next_cover_points(chart, coord, a1, b1, ucov, prec=None,
                                verbose=False):
    r"""Section 5.2 at the generic point of every component of psi^{-1}(E),
    E = V(coord) of ``chart``, for the double cover w^2 = u of the next round
    given by ucov = (nu1, nu0, den).  Returns a set of monic irreducible
    polynomials in k[X]: the closed points of E below the candidates.

    ``prec`` is the total degree below which a1 and b1 are exact; the residues
    used here are read at level 0 and 1 along the component, so it is only
    asserted to be at least 2."""
    assert prec is None or prec >= 2, \
        "a_1 and b_1 are exact only below total degree %s" % prec
    gcs = component_generic_objects(chart, coord, a1, b1)
    out = set()
    for gc in gcs:
        out |= gc.next_cover_candidates(ucov, verbose=verbose)
    return out


def component_generic_objects(chart, coord, a1, b1):
    r"""The components of psi^{-1}(E), E = V(coord), as GenericComponent
    objects: one 'ram' when abar = bbar = 0, one 'inert' when Y^2+abar Y+bbar
    is irreducible over k(X), two 'split' otherwise (Prop. 3.7)."""
    B = chart.base
    red = chart.red_modS if coord == 'S' else chart.red_modT
    abar, bbar = red(chart.R(a1)), red(chart.R(b1))
    KX = FractionField(B.kT)
    if abar == 0 and bbar == 0:
        return [GenericComponent(chart, coord, a1, b1, 'ram')]
    Yv = PolynomialRing(KX, 'Y').gen()
    pol = Yv ** 2 + KX(abar) * Yv + KX(bbar)
    assert all(e == 1 for _, e in pol.factor()), \
        "the cover is not reduced along the component: %s" % pol
    if pol.is_irreducible():
        return [GenericComponent(chart, coord, a1, b1, 'inert')]
    gcs = [GenericComponent(chart, coord, a1, b1, 'split', root=r)
           for r, _ in pol.roots()]
    assert len(gcs) == 2, "a split component with %s branches" % len(gcs)
    return gcs
