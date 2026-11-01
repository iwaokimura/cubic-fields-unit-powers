# check-qc-phase0.sage --- E048 Phase 0, Gate 2 of E048.
#
# THE QUESTION.  E048 asks, before committing to a port of Tuitman's
# algorithm, whether the SHORT route (Route A) is open: transport the quadratic
# Chabauty computation from the plane quartic C_4 to the pieces of the
# decomposition Jac(C_4) ~ E x P.  Over K = Q(4^(1/3)) the Prym P is the
# Jacobian of the genus-2 curve X of E039(e) (Ritzenthaler-Romagny Thm 1.1),
# and SageMath's Coleman integration covers hyperelliptic curves.  So:
#
#   GATE 2.  If 4 is a cube mod p then K embeds in Q_p and X is a genus-2 curve
#   over Q_p.  E044(e) records that the defining sextic factors over K into
#   three irreducible quadratics, so X has NO K-rational Weierstrass point and
#   hence no odd degree model over K.  Over Q_p one of the three quadratics may
#   nevertheless split, which would give a Q_p-rational Weierstrass point, an
#   odd degree model, and therefore an input Sage's coleman_integrals_on_basis
#   accepts.  Does that happen, and does the integration then actually run?
#
# WHY THE ODD DEGREE MODEL IS THE ISSUE.  Sage's Monsky-Washnitzer machinery
# (monsky_washnitzer.py, SpecialHyperellipticQuotientRing) refuses anything but
# y^2 = Q(x) with Q MONIC -- "NotImplementedError: polynomial must be monic" --
# and its basis of H^1_dR is the one of a degree-(2g+1) model.  A degree-6
# model has to be moved to a degree-5 one first, and that needs a rational root
# of the sextic.
#
# WHAT THIS SCRIPT DOES.
#   1. Rebuilds X over K from Theorem 1.1 and calibrates it against E039/E044:
#      det A, nonzero discriminant, genus 2, and the 3-irreducible-quadratics
#      factorisation of E044(e).
#   2. For every good p < PMAX with 4 a cube mod p, decides whether the sextic
#      acquires a Q_p-rational root, i.e. whether an odd degree model over Q_p
#      exists.  This is exact: a quadratic splits over Q_p iff its
#      discriminant is a square there.
#   3. For the first few such p, builds the monic quintic model over Q_p and
#      RUNS Sage's coleman_integrals_on_basis, checking I(P,P) = 0 and the path
#      additivity I(P,Q) + I(Q,R) = I(P,R).
#
# Failure counts are printed explicitly and the run ends with a VERDICT block.

import sys


def say(s=""):
    print(s)
    sys.stdout.flush()


PMAX = 200          # range of primes for the census in section 2
NPREC = 25          # p-adic working precision
NRUN = 3            # how many primes to actually integrate on


# ============================================================ 1. X over K

R0 = PolynomialRing(QQ, 't')
t = R0.gen()
Kw = NumberField(t^3 - 4, 'w')
w = Kw.gen()
RK = PolynomialRing(Kw, 'x')
x = RK.gen()


def build_X():
    """Theorem 1.1 of Ritzenthaler-Romagny applied to
       C_4 : W^4 - 6(T-Z)^2 W^2 + 27 T (T^3 - 4 Z^3) = 0,
    with f = 27T(T - wZ), g = T^2 + wTZ + w^2 Z^2, h = 6(T-Z)^2.
    Returns (A, a, b, c, sextic).  Column convention as in check-c4-prym-rr.gp.
    """
    A = matrix(Kw, [[27, -27*w, 0],
                    [6, -12, 6],
                    [1, w, w^2]])
    Ai = A.inverse()
    a = Ai[0, 0] + 2*Ai[1, 0]*x + Ai[2, 0]*x^2
    b = Ai[0, 1] + 2*Ai[1, 1]*x + Ai[2, 1]*x^2
    c = Ai[0, 2] + 2*Ai[1, 2]*x + Ai[2, 2]*x^2
    return A, a, b, c, b*(b^2 - a*c)


fails = 0

say("=== 1. the genus-2 curve X over K = Q(w), w^3 = 4  (calibration) ===")
say()

A, aa, bb, cc, S = build_X()
detA = A.determinant()
say("  det A = %s" % detA)
if detA != -324*w^2 - 324*w + 648:
    say("  *** FAIL: det A disagrees with E039(e) ***")
    fails += 1
else:
    say("  ok: agrees with E039(e), -324w^2 - 324w + 648")

say("  sextic degree      : %s" % S.degree())
disc_S = S.discriminant()
say("  sextic disc nonzero: %s" % (disc_S != 0))
if S.degree() != 6 or disc_S == 0:
    say("  *** FAIL: not a genus-2 model ***")
    fails += 1

fac = S.factor()
degs = sorted([g.degree() for g, e in fac for _ in range(e)])
say("  factorisation over K, degrees of irreducible factors: %s" % degs)
if degs != [2, 2, 2]:
    say("  *** FAIL: E044(e) says three irreducible quadratics ***")
    fails += 1
else:
    say("  ok: three irreducible quadratics -- E044(e) reproduced.")
    say("      => no K-rational Weierstrass point, no odd degree model over K.")
say()

quads = [g for g, e in fac if g.degree() == 2]
lead = S.leading_coefficient() / prod(g.leading_coefficient() for g in quads)


# ============================================================ 2. census over p

def cube_root_of_4(p, N):
    """A root of x^3 - 4 in Z_p, by Newton from an F_p root; None if none."""
    rs = [ZZ(r) for r in GF(p)(4).nth_root(3, all=True)]
    if not rs:
        return None
    Qp_ = Qp(p, N)
    r = Qp_(rs[0])
    for _ in range(2*N.nbits() + 4):
        r = r - (r^3 - 4) / (3*r^2)
    if (r^3 - 4) != 0:
        return None
    return r


def embed(el, r):
    """K -> Q_p determined by w |-> r."""
    return el.polynomial()(r)


def split_data(p, N):
    """Return (nsplit, datum) : how many of the three quadratics of section 1
    split over Q_p, and, for the first one that does, the datum
    (r, i, rho, rho') -- the embedding K -> Q_p, the index of the split
    quadratic, and its two Q_p-roots.  (None, None) if p is unusable (4 not a
    cube mod p, or bad reduction of this model)."""
    r = cube_root_of_4(p, N)
    if r is None:
        return None, None
    if embed(disc_S, r).valuation() != 0:
        return None, None                      # bad reduction of this model
    nsplit = 0
    datum = None
    for i, q in enumerate(quads):
        C0, C1, C2 = [embed(q[j], r) for j in range(3)]
        d = C1^2 - 4*C2*C0
        if d.valuation() % 2 == 0 and d.is_square():
            nsplit += 1
            if datum is None:
                s = d.sqrt()
                datum = (r, i, (-C1 + s)/(2*C2), (-C1 - s)/(2*C2))
    return nsplit, datum


say("=== 2. census: does X acquire a Q_p-rational Weierstrass point? ===")
say("    p with 4 a cube mod p and good reduction; nsplit = how many of the")
say("    three quadratics of section 1 split over Q_p")
say()

census = []
for p in prime_range(5, PMAX):
    ns, datum = split_data(p, NPREC)
    if ns is None:
        continue
    census.append((p, ns, datum))

line = "  "
for (p, ns, root) in census:
    line += "%d:%d  " % (p, ns)
say(line)
ngood = len([1 for (p, ns, _) in census if ns > 0])
say()
say("  %d usable primes below %d, %d of them with an odd degree model over Q_p"
    % (len(census), PMAX, ngood))
if len(census):
    say("  proportion with a Q_p-Weierstrass point: %d/%d" % (ngood, len(census)))
say()


# ============================================================ 3. run Coleman

def monic_quintic(datum, p, N):
    """Move the Q_p-rational Weierstrass point to infinity and scale to a monic
    quintic:  y^2 = S(x) with S(rho) = 0  becomes  Y^2 = g(U), g monic deg 5.

    The cofactor T = S/(x - rho) is built EXACTLY from the factorisation
    S = lead * q_1 q_2 q_3 over K of section 1 -- writing the split quadratic
    q_i as C2 (x - rho)(x - rho') -- rather than by dividing a p-adically
    approximated sextic, which loses the exact vanishing at rho.
    """
    r, i, rho, rhop = datum
    Qp_ = Qp(p, N)
    # NB the variable must be called 'x': Sage's Monsky-Washnitzer code builds
    # its own PolynomialRing(R, 'x') and subtracts, which fails across names.
    RQ = PolynomialRing(Qp_, 'x')
    X_ = RQ.gen()

    C2 = embed(quads[i][2], r)
    T = embed(lead, r) * C2 * (X_ - rhop)
    for j, q in enumerate(quads):
        if j != i:
            T *= sum(embed(q[k], r) * X_^k for k in range(3))
    if T.degree() != 5:
        return None, "cofactor has degree %s, not 5" % T.degree()

    # calibration: (x - rho) * T must reproduce the sextic over Q_p
    Sp = sum(embed(S[k], r) * X_^k for k in range(7))
    err = (X_ - rho)*T - Sp
    if err != 0 and min([c.valuation() for c in err.coefficients()]) < N - 8:
        return None, "cofactor calibration failed (error valuation %s)" % \
            min([c.valuation() for c in err.coefficients()])

    # x = rho + 1/u, y = v/u^3  =>  v^2 = u^5 T(rho + 1/u) =: q(u), degree 5
    q = RQ(0)
    for k, ck in enumerate(T.coefficients(sparse=False)):
        q += ck * (rho*X_ + 1)^k * X_^(5 - k)
    if q.degree() != 5:
        return None, "transformed model has degree %s, not 5" % q.degree()
    a5 = q.leading_coefficient()
    # Y^2 = U^5 + ... : U = a5*u, Y = a5^2*v
    g = RQ(0)
    for k, ck in enumerate(q.coefficients(sparse=False)):
        g += ck * a5^(4 - k) * X_^k
    return g / g.leading_coefficient(), None


def count_C4(p):
    """#C_4(F_p) for C_4 : W^4 - 6(T-Z)^2 W^2 + 27 T (T^3 - 4 Z^3) = 0."""
    F = GF(p)
    tot = 0
    for T in F:                                   # affine patch Z = 1
        for W in F:
            if W^4 - 6*(T-1)^2*W^2 + 27*T*(T^3-4) == 0:
                tot += 1
    RF = PolynomialRing(F, 's')
    s = RF.gen()
    tot += len((s^4 - 6*s^2 + 27).roots())        # Z = 0, T = 1; [0:0:0] is not a point
    return tot


E36 = EllipticCurve([0, 0, 0, -36, 0])


say("=== 3. does Sage's Coleman integration run on X over Q_p? ===")
say("    each model is first checked to BE the Prym curve, by reducing it mod p")
say("    and comparing its Frobenius trace with E038's")
say("    a_p(P) = a_p(C_4) - a_p(E),  E : y^2 = x^3 - 36x")
say()

runs = 0
for (p, ns, datum) in census:
    if ns == 0 or runs >= NRUN:
        continue
    runs += 1
    say("  --- p = %d ---" % p)
    g, err = monic_quintic(datum, p, NPREC)
    if g is None:
        say("      *** FAIL: %s ***" % err)
        fails += 1
        continue
    say("      monic quintic model built over Q_%d, disc valuation %s"
        % (p, g.discriminant().valuation()))
    try:
        H = HyperellipticCurve(g)
    except Exception as e:
        say("      *** FAIL: HyperellipticCurve refused the model: %s ***" % e)
        fails += 1
        continue
    say("      genus %s" % H.genus())

    # is this really the Prym curve?  reduce mod p and compare traces
    vmin = min([c.valuation() for c in g.coefficients() if c != 0])
    if vmin < 0:
        say("      *** FAIL: model not integral at p (min valuation %s) ***" % vmin)
        fails += 1
        continue
    gbar = PolynomialRing(GF(p), 'x')(
        [GF(p)(c.residue(1)) for c in g.coefficients(sparse=False)])
    apX = p + 1 - HyperellipticCurve(gbar).count_points(1)[0]
    apP = (p + 1 - count_C4(p)) - E36.ap(p)
    say("      a_p(Jac of this model) = %d   a_p(P) = a_p(C_4) - a_p(E) = %d   %s"
        % (apX, apP, "ok" if apX == apP else "*** MISMATCH ***"))
    if apX != apP:
        fails += 1
        continue

    # three points in distinct good (non-Weierstrass) residue discs
    pts, xs = [], []
    for x0 in range(0, 60):
        if len(pts) == 3:
            break
        try:
            v = g(H.base_ring()(x0))
            if v == 0 or v.valuation() != 0 or not v.is_square():
                continue
            pts.append(H.lift_x(H.base_ring()(x0)))
            xs.append(x0)
        except Exception:
            continue
    if len(pts) < 3:
        say("      *** FAIL: found only %d usable Q_p-points ***" % len(pts))
        fails += 1
        continue
    P, Q, Rr = pts
    say("      points at x = %s" % xs)
    try:
        I_PP = H.coleman_integrals_on_basis(P, P)
        I_PQ = H.coleman_integrals_on_basis(P, Q)
        I_QR = H.coleman_integrals_on_basis(Q, Rr)
        I_PR = H.coleman_integrals_on_basis(P, Rr)
    except Exception as e:
        say("      *** FAIL: coleman_integrals_on_basis raised: %r ***" % e)
        fails += 1
        continue
    say("      I(P,Q) = %s" % (tuple(I_PQ),))
    zero_ok = all(v.valuation() >= NPREC - 5 or v == 0 for v in I_PP)
    add = [(I_PQ[i] + I_QR[i] - I_PR[i]) for i in range(len(I_PQ))]
    add_ok = all(v.valuation() >= NPREC - 5 or v == 0 for v in add)
    say("      I(P,P) = 0                : %s" % zero_ok)
    say("      I(P,Q) + I(Q,R) = I(P,R)  : %s   (valuations %s)"
        % (add_ok, [v.valuation() for v in add]))
    if not (zero_ok and add_ok):
        say("      *** FAIL: calibration of the integrator failed ***")
        fails += 1
    say()

if runs == 0:
    say("  (no prime with an odd degree model was available -- nothing run)")
    fails += 1

say()
say("=== VERDICT ===")
say("  failures: %d" % fails)
if fails == 0:
    say("  GATE 2 = GREEN: over Q_p the sextic of E039(e) does acquire a")
    say("  rational Weierstrass point, and Sage's hyperelliptic Coleman")
    say("  integration runs on the resulting odd degree model and passes the")
    say("  I(P,P)=0 and path-additivity calibrations.")
else:
    say("  GATE 2 = RED at some step; see the *** FAIL *** lines above.")
