# cg-height-lib.sage --- E134: the Coleman--Gross p-adic height on an elliptic
# curve, computed from cited statements rather than read off SageMath.
#
# Everything here is derived in check-cg-height.sage, which is the gate for this
# file; this is the same code factored out so the production scripts can read
# OUR height instead of SageMath's padic_height.  The numbers are identical --
# check-cg-height.sage group (C) shows the difference is identically zero on the
# production input -- so nothing downstream moves.
#
# THE TWO CITED STATEMENTS.
#
#   Mazur--Stein--Tate, "Computation of p-adic heights and log convergence",
#   Doc. Math. Extra Vol. Coates (2006), 577--614 (MR2290599):
#
#     Algorithm 3.1, steps 3-4:  wp(z) = x + (a1^2 + 4 a2)/12  and
#        sigma(z) = z exp( int int ( 1/z^2 - wp(z) + e2/12 ) dz dz ),
#     z the formal logarithm, i.e.  D(D log sigma) + x + c = 0  with
#     D = d/dz = (1/f) d/dt, omega = f(t) dt = dz, c = (a1^2 + 4a2 - E2)/12.
#
#     (1.1):  h_p(P) = (1/p) log_p( sigma(P) / d(P) ).
#
#     Section 3.2, p.591: on y^2 = 4x^3 - g_2 x - g_3 with omega = dx/y and
#     eta = x dx/y, writing F^n(eta) = a_n omega + b_n eta, the unit root
#     subspace is the span of F^n(eta) and E2(E,omega) = -12 a_n/b_n (mod p^n).
#
#   Coleman--Gross, "p-adic heights on curves", Adv. Stud. Pure Math. 17 (1989),
#   73-81 (Zbl 0758.14009): at good
#   ordinary reduction the unit root space may be taken as the splitting W, and
#   the resulting pairing is Schneider's and Mazur--Tate's.
#
# OUR NORMALISATION.  cg_height below returns
#     h((P)-(O)) = -2/n^2 log_p( sigma(t(nP)) / d(nP) )  =  -2p * h_p^MST(P),
# the constant -2p being exactly the change of idele class character to
# chi_p = log_p, chi_q(q) = -log_p(q), which E086(c) shows is FORCED by the
# product formula.  This is the height that enters B (E094, E096, E120).
#
# THE CONSTANT c.  Supply it explicitly.  Two suppliers:
#   c_from_cm_qi(E, p)     -- 0, DERIVED, for a curve with CM by Z[i] at a split
#                             ordinary p; see check-cg-height.sage group (E).
#                             This is the production case (y^2 = x^3 - 36x).
#   c_from_padic_E2(E,p,N) -- SageMath's padic_E2.  THIRD PARTY.  Named so that
#                             every use of it is visible in the caller.

def minimal_pair(E, p):
    """(E_min, iso) with E_min minimal at p; MST's sigma needs a minimal model."""
    Em = E.minimal_model()
    return Em, E.isomorphism_to(Em)


_minimal_pair = minimal_pair          # kept: earlier callers used the private name


def c_from_cm_qi(E, p, verbose=False):
    """c = (a1^2 + 4a2 - E2)/12 = 0, DERIVED, when E has CM by Z[i] and p splits.

    [i](x,y) = (-x, iy) is an endomorphism defined over Z_p once i is in Z_p; on
    H^1_dR it sends omega = dx/2y to i omega and eta = x dx/2y to -i eta, two
    DISTINCT eigenvalues, so the only [i]-stable lines are <omega> and <eta>.
    Frobenius commutes with [i], so the unit root line is one of them, and it is
    not <omega> (the Hodge line).  Hence the unit root line is <eta>, so a_n = 0
    and E2 = -12 a_n/b_n = 0 by MST 3.2.  With a1 = a2 = 0, c = 0."""
    assert E.has_cm() and E.cm_discriminant() == -4, \
        "c_from_cm_qi: E has no CM by Z[i] (cm_discriminant = %s)" % \
        (E.cm_discriminant() if E.has_cm() else None)
    assert p % 4 == 1, "c_from_cm_qi: i is not in Z_%s (p = %s mod 4)" % (p, p % 4)
    assert E.has_good_reduction(p) and E.is_ordinary(p), \
        "c_from_cm_qi: E is not good ordinary at %s" % p
    assert E.a1() == 0 and E.a2() == 0 and E.a3() == 0, \
        "c_from_cm_qi: c = (a1^2+4a2-E2)/12 needs a1 = a2 = 0 here"
    assert E.is_minimal(), "c_from_cm_qi: pass a model minimal at p"
    if verbose:
        print("       -- c = 0, derived: CM by Z[i], %s splits, unit root line "
              "= <eta> (MST 3.2)" % p)
    return QQ(0)


def c_from_padic_E2(E, p, N):
    """c from SageMath's padic_E2.  THIRD PARTY -- use only where no derivation
    is available.

    Used for E101's two calibration curves.  There it is an ANSWER KEY, not a
    step in a derivation: E101 tests the port against an independent reference
    on a curve it has never seen, and E120 turned E101 from a measurement into
    a confirmed prediction, so Theorem D does not pass through it.

    Only ONE of those two curves genuinely lacks CM.  (An earlier version of
    this docstring said both did; that was wrong.)
      E_-  = 128a2, j = 10976 : no CM, and c is a nonzero 11-adic number.
      E_+  = 256a1, j =  8000 : CM by Z[sqrt(-2)], disc -8.  At p = 11, which
             splits there, padic_E2 returns exactly a1^2 + 4 a2, i.e. c = 0.
    So c_from_cm_qi's argument plausibly extends to E_+, but NOT verbatim:
    [i](x,y) = (-x, iy) is diagonal, so eta is itself an eigenvector, whereas
    [sqrt(-2)] has degree 2 and eta is an eigenvector only modulo omega.  The
    vanishing above is [E: 1 case], not a derivation; writing one would remove
    half of the last third-party constant and change nothing downstream."""
    return (QQ(E.a1()) ** 2 + 4 * QQ(E.a2()) - E.padic_E2(p, N)) / 12


def cg_sigma(E, p, prec, c, M=None):
    """Mazur--Stein--Tate's sigma, solved from Algorithm 3.1 steps 3-4.

    log sigma = log t + u makes the equation LINEAR: A := D log sigma satisfies
    A' = -f (x+c), one termwise integration, and sigma'/sigma = A f gives u by a
    second.  E must be minimal at p."""
    if M is None:
        M = prec + 10
    K = Qp(p, prec + 12)
    PS = PowerSeriesRing(K, 't', default_prec=M + 4)
    t = PS.gen()
    fgx = E.formal_group().x(M + 4)
    fgf = E.formal_group().differential(M + 4)
    xs = {k: K(QQ(a)) for k, a in zip(range(fgx.valuation(), fgx.prec()),
                                      fgx.list())}
    fp = PS([K(QQ(a)) for a in fgf.list()]).add_bigoh(M + 4)
    xnum = PS([xs.get(k - 2, K(0)) for k in range(M + 4)]).add_bigoh(M + 4) \
        + K(c) * t ** 2
    g = -(fp * xnum)                      # = t^2 * A'
    Ac = {}
    for k in range(M + 2):
        e = k - 2
        if e == -1:
            assert g[k] == 0, "cg_sigma: a log term appeared in A"
            continue
        Ac[e + 1] = g[k] / K(e + 1)
    Aser = PS([Ac.get(k - 1, K(0)) for k in range(M + 2)]).add_bigoh(M + 2)
    S = Aser * fp                         # = t * sigma'/sigma
    u = PS([K(0)] + [S[k] / K(k) for k in range(1, M + 1)]).add_bigoh(M + 1)
    return t * u.exp(), K, M


def _kill_n(E, p):
    return lcm(ZZ(E.change_ring(GF(p)).cardinality()),
               lcm(E.tamagawa_numbers()) if E.is_minimal() else ZZ(1))


def cg_height(E, p, P, prec, c, sigma=None, cap=None):
    """-2/n^2 log_p( sigma(t(nP)) / d(nP) ), on a model MINIMAL AT p.

    Returns the height in the character chi_p = log_p, chi_q(q) = -log_p(q)
    (E086(c)); this is -2p times MST (1.1)."""
    if sigma is None:
        sigma, K, M = cg_sigma(E, p, prec, c)
    else:
        sigma, K, M = sigma
    n = _kill_n(E, p)
    Q = n * P
    t0 = K(-QQ(Q[0]) / QQ(Q[1]))
    d = ZZ(QQ(Q[0]).denominator()).sqrt()
    sv = sum((sigma[k] * t0 ** k for k in range(1, M) if sigma[k] != 0), K(0))
    ratio = sv / K(d)
    assert ratio.valuation() == 0, \
        "cg_height: sigma(t(nP))/d(nP) is not a unit, so a branch of log_p " \
        "would have to be chosen (valuation %s)" % ratio.valuation()
    h = -2 * ratio.log() / K(n ** 2)
    # The series is solved to prec + 12 digits, so h carries MORE precision than
    # SageMath's padic_height(p, prec) does.  Capping at prec makes the swap in
    # the production scripts a byte-for-byte no-op; pass cap=0 for the full value.
    if cap is None:
        cap = prec
    return h.add_bigoh(cap) if cap else h


def cg_height_any(E, p, P, prec, c=None, cap=None):
    """the same, for a model that need not be minimal: the height is intrinsic
    (E094(i)), so we transport P to the minimal model and compute there.

    With c omitted the constant is DERIVED from CM by Z[i] (the production
    case).  Pass c = c_from_padic_E2(...) explicitly for a curve where no
    derivation is available, so that the third-party input is visible."""
    Em, iso = _minimal_pair(E, p)
    if c is None:
        c = c_from_cm_qi(Em, p)
    return cg_height(Em, p, iso(P), prec, c, cap=cap)
