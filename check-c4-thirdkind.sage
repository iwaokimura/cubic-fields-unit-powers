r"""
check-c4-thirdkind.sage --- E109 (Tier 1): the differential of the third kind
with residue divisor kappa' = [sigma b] - [b], and the cost of integrating it.

E108 left b = h_p(kappa', delta_11) - (5/2) log_13(2) + log_13(3) with the two
ell-adic terms computed and h_p unknown.  Coleman-Gross gives

    h_p(D_1, D_2) = int_{D_2} omega_{D_1},

omega_{D_1} of the third kind with residue divisor D_1 and normalised so that
its class lies in the unit root subspace W.  E094 5.4 named this "the
newest component" and asked for a Tier 1 measurement before committing.  This
script is that measurement.  It does NOT compute h_p.

MODEL.  C_4 : Q = y^4 - 6(x-1)^2 y^2 + 27x(x^3-4) over Q, (x,y) = (t,w),
b = (1,3), sigma b = (1,-3), x_11 = (-1/11, 15/11); sigma is y |-> -y.
The four points over x = 1 are y^4 = 81, i.e. y = +-3 and the degree-2 place
y^2 = -9.

WHAT IS MEASURED, in order:
 (1) omega_0 exists in closed form over Q, with residue divisor exactly kappa'.
 (2) the port cannot hold it: E allows poles only over x = infinity and over
     the zeros of r, and r(1) = 27/2 is not zero.
 (3) the escape r |-> (x-1) r, and what it does to the dimensions.
 (4) the escape costs nothing: same chi(T), same running time.
 (5) H^1_dR(X) + Q_p [omega_0] is Frobenius-stable, with Phi[omega_0] =
     p[omega_0] mod H^1_dR(X), and Phi - I invertible on it -- so Algorithm 3.7
     applies to a SEVEN-dimensional system, not a thirty-three-dimensional one.
"""

import sys, os, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.frobenius import FrobeniusMatrix

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Q1 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)
Rx = PolynomialRing(QQ, 'x')
X = Rx.gen()
P_GATE = 13
N_CHI = ZZ(os.environ.get("E109_NCHI", 4))
N_PHI = ZZ(os.environ.get("E109_NPHI", 6))

FAIL = []


def check(cond, msg):
    ok = bool(cond)
    print("   %s %s" % ("[ok] " if ok else "[FAIL]", msg))
    if not ok:
        FAIL.append(msg)
    sys.stdout.flush()
    return ok


def info(msg):
    print("        %s" % msg)
    sys.stdout.flush()


def omega0(C):
    """The third-kind differential with residue divisor [sigma b] - [b].

    ANSATZ, and it is forced.  On a smooth plane quartic the adjoint forms
    G(x,y) dx / Q_y with G polynomial are regular on the affine curve, and
    regular at infinity iff deg G <= 1 (the holomorphic ones, g = 3) resp. at
    worst simply-polar there iff deg G <= 2.  Poles at the points over x = 1
    and nowhere else therefore ask for

        omega = G(x,y) dx / ((x-1) Q_y),   deg G <= 2,

    which is regular at infinity because G/(x-1) then has degree <= 1.  sigma
    acts by y |-> -y, dx/Q_y is sigma-ODD (Q_y = 4y^3 - 12(x-1)^2 y is odd), so
    omega is odd iff G is even in y: G = a + bx + cx^2 + e y^2.  Then

        res_{(1,3)}  = G(1,3)/Q_y(1,3)   = (a+b+c+9e)/108,
        res_{(1,-3)} = -res_{(1,3)}      (oddness),
        res at the degree-2 place y^2 = -9 : G(1,3i)/Q_y(1,3i),  G(1,3i)=a+b+c-9e.

    Killing the third and setting the first to -1 gives e = -6, a+b+c = -54,
    and the two remaining parameters are exactly (x-1) and (x^2-1) over (x-1),
    i.e. the two sigma-odd holomorphic forms dx/Q_y and x dx/Q_y.  The choice
    a = -54, b = c = 0 is the representative used here.
    """
    L = C.L
    xL, yL = L(C.x), C.y
    Qy = 4*yL**3 - 12*(xL - 1)**2*yL
    return (-6*(yL**2 + 9) / ((xL - 1) * Qy)) * xL.differential()


def enlarged(name):
    """The same plane model with r replaced by (x-1) r.

    Tuitman's r (Definition 2.2) is the radical of Delta = disc_y Q; the
    algorithm only ever uses that its zeros are removed from the affine curve
    and that s = r/(dQ/dy) is integral (Proposition 2.4), and both survive
    multiplication by (x-1): s becomes (x-1)s, still integral, and Prop 2.7's
    G = M/r becomes (x-1)M/(x-1)r.  What changes is that the four points over
    x = 1 are removed as well, which is precisely what makes room for omega_0.
    """
    C = TuitmanCurve(Q1, name=name)
    C.r = C.r * (X - 1)
    C.degr = C.r.degree()
    return C


def main():
    print("=== check-c4-thirdkind.sage --- E109: omega_{kappa'} and the cost "
          "of integrating it ===")
    t00 = time.time()

    # ------------------------------------------------------------ group (1)
    print("(1) THE FORM, EXACTLY")
    C0 = TuitmanCurve(Q1, name="C_4")
    C = enlarged("C_4 minus x=1")
    H0, H = Cohomology(C0), Cohomology(C)
    L = C.L
    xL, yL = L(C.x), C.y
    om0 = omega0(C)
    sig = L.hom(-yL)
    info("omega_0 = -6 (y^2+9) dx / ((x-1)(4y^3 - 12(x-1)^2 y))")

    pl = H.candidate_places()
    poles = [(P, H.pole_order(om0, P)) for P in pl]
    deg1_at_1 = [P for P, m in poles if m > 0]
    check(len(deg1_at_1) == 2 and all(P.degree() == 1 for P in deg1_at_1)
          and all(m == 1 for _, m in poles if m > 0)
          and sum(1 for _, m in poles if m > 0) == 2,
          "omega_0 has simple poles at exactly two places, both of degree 1, "
          "and is regular at every other candidate place -- including the "
          "degree-2 place y^2 = -9 over x = 1, the four places over the zeros "
          "of the original r, and the degree-4 place at infinity")

    Pb = [P for P in pl if P.degree() == 1 and (xL - 1).valuation(P) > 0
          and (yL - 3).valuation(P) > 0]
    Psb = [P for P in pl if P.degree() == 1 and (xL - 1).valuation(P) > 0
           and (yL + 3).valuation(P) > 0]
    zero_elsewhere = all(om0.residue(P) == 0 for P in pl
                         if P not in Pb + Psb)
    check(len(Pb) == 1 and len(Psb) == 1 and zero_elsewhere
          and om0.residue(Pb[0]) == -1 and om0.residue(Psb[0]) == 1,
          "its residue divisor is EXACTLY kappa' = [sigma b] - [b]: -1 at "
          "b = (1,3), +1 at sigma b = (1,-3), 0 elsewhere.  Sage's residue(), "
          "over Q, on the function field -- exact, not to precision [T(CAS)]")

    check(sig(om0._f) == -om0._f,
          "sigma^* omega_0 = -omega_0 as an identity in the function field, so "
          "omega_0 is in the Prym part, where kappa' lives")

    hol = [vector(QQ, h) for h in H.holomorphic_forms_in_E()]
    Vh = (QQ**H.dim_E).span(hol)
    Sh = []
    for h in hol:
        o = H.differential_of(h)
        Sh.append(vector(QQ, H.form_in_E(sig(o._f) * xL.differential())))
    Bm = matrix(QQ, hol).transpose()
    Ms = matrix(QQ, [Bm.solve_right(v) for v in Sh]).transpose()
    ev = sorted(Ms.eigenvalues())
    check(Vh.dimension() == 3 and ev == [-1, -1, 1]
          and Ms.is_diagonalizable(),
          "the ambiguity in omega_0 is H^0(Omega^1), of dimension 3, and "
          "sigma^* has eigenvalues (1, -1, -1) on it, so the sigma-odd "
          "third-kind forms with residue divisor kappa' are a TWO-parameter "
          "family -- which is the g_Prym = 2 unknowns the Coleman-Gross "
          "normalisation (class in W) will have to fix")

    # ------------------------------------------------------------ group (2)
    print("(2) THE OBSTRUCTION, NAMED")
    info("original r = %s" % factor(C0.r))
    check(C0.r(1) == QQ(27)/2 and C0.r(1) != 0,
          "x = 1 is not a zero of Tuitman's r: r(1) = 27/2.  So the four "
          "points over x = 1 are NOT removed from the affine curve the port "
          "works on, and a differential with poles there is outside E")
    bad = None
    try:
        H0.form_in_E(omega0(C0))
    except ArithmeticError as e:
        bad = str(e)
    check(bad is not None and "(x - 1)" in bad,
          "form_in_E rejects omega_0 for the original r, and the rejection "
          "names the reason: a coefficient with denominator (x - 1).  Nothing "
          "in Phases 1-4 can hold this form as it stands: %s" % bad)

    # ------------------------------------------------------------ group (3)
    print("(3) THE ESCAPE: r |-> (x-1) r")
    Rp = C.r.change_ring(GF(P_GATE))
    check(Rp.is_squarefree() and Rp.degree() == 9,
          "(x-1)r stays separable mod p = 13 -- Tuitman's Assumption 1 -- "
          "because r(1) = 27/2 is a unit there")
    d0 = H0.H1X_tuitman()
    d1 = H.H1X_tuitman()
    info("plain    : dim E = %d, dim H^1(U) = %d, H1X data %s"
         % (H0.dim_E, H0.H1U()[0], d0))
    info("enlarged : dim E = %d, dim H^1(U) = %d, H1X data %s"
         % (H.dim_E, H.H1U()[0], d1))
    check(H.H1U()[0] == H0.H1U()[0] + 4 and d1[0] == d0[0] == 6
          and d1[2] == d0[2] == 14,
          "removing the four geometric points over x = 1 adds exactly 4 to "
          "H^1_rig(U) (an affine curve has no residue relation left to spend) "
          "and leaves H^1_dR(X) at 2g = 6 and the finite residue kernel at 14: "
          "the enlargement adds residue directions and disturbs nothing else")
    w0 = vector(QQ, H.form_in_E(om0))
    den = lcm([QQ(c).denominator() for c in w0])
    check(den == 12 and gcd([ZZ(c) for c in w0*den]) == 1,
          "omega_0 lies in the enlarged E, with 12 omega_0 primitive integral "
          "there -- so the saturated lattice H1X_basis works with is not "
          "disturbed by adjoining it")

    # ------------------------------------------------------------ group (4)
    print("(4) THE ESCAPE COSTS NOTHING")
    out = {}
    for tag, CC, HH in [("plain", C0, H0), ("enlarged", C, H)]:
        t0 = time.time()
        FM = FrobeniusMatrix(CC, HH, P_GATE, N_CHI)
        FM.compute()
        out[tag] = (FM.chi(), time.time() - t0, FM.certified_precision())
        info("%-9s chi = %s   (%.1f s, certified %s)"
             % (tag, out[tag][0][0], out[tag][1], out[tag][2]))
    check(out["plain"][0][0] == out["enlarged"][0][0],
          "the two runs give the SAME chi(T), so the enlarged r does not "
          "disturb what E059 calibrated against point counts at 428 primes -- "
          "H^1_dR(X) and its Frobenius are the same object inside the larger E")
    check(out["enlarged"][1] < 2 * out["plain"][1],
          "and it costs the same: %.1f s against %.1f s at N = %s"
          % (out["enlarged"][1], out["plain"][1], N_CHI))

    # ------------------------------------------------------------ group (5)
    print("(5) THE SEVEN-DIMENSIONAL STABLE SUBSPACE")
    info("phi lifts x |-> x^p; the four points over x = 1 reduce to "
         "(1, +-3) and (1, +-2) mod 13, all F_13-rational (81 = 3^4 and "
         "-9 = 4 = 2^2 in F_13), so each of the four residue disks is "
         "phi-stable and res(phi^* omega_0) = p res(omega_0).")
    info("Hence [phi^* omega_0] - p [omega_0] has zero residues, i.e. lies in "
         "H^1_dR(X): the span of H^1_dR(X) and [omega_0] is Phi-stable. [T]")

    FM = FrobeniusMatrix(C, H, P_GATE, N_PHI)
    base = FM.base
    hbasis, imbasis = list(FM.basis), list(FM.im_basis)

    def phi_on(extra):
        """Phi on span(H^1_dR(X), extra), by Algorithm 3.7's own step 5."""
        bas = hbasis + [extra]
        n = H.dim_E
        cols = [vector(base, [base(QQ(c)) for c in b]) for b in bas]
        dcols = [vector(base, [base(QQ(c)) for c in b]) for b in imbasis]
        A = matrix(base, n, len(cols) + len(dcols),
                   lambda i, j: (cols[j][i] if j < len(cols)
                                 else dcols[j - len(cols)][i]))
        cols_out, worst = [], None
        for b in bas:
            u = FM._form_coefficients(b)
            coords = FM.reduce_to_E(FM.frobenius_of_form(u))
            sol = A.solve_right(coords)
            resid = A*sol - coords
            vals = [c.valuation() for c in resid if c != 0]
            v = min(vals) if vals else FM.N
            worst = v if worst is None else min(worst, v)
            cols_out.append([sol[j] for j in range(len(cols))])
        m = len(cols)
        return matrix(base, m, m,
                      lambda i, j: cols_out[j][i]), worst

    t0 = time.time()
    Phi7, resid7 = phi_on(list(w0 * den))
    info("Phi on the 7-dimensional span computed in %.1f s, solve residual "
         "p^%s, certified %s" % (time.time() - t0, resid7,
                                 FM.certified_precision()))
    cert = FM.certified_precision()[0]
    bottom = [Phi7[6, j] for j in range(7)]
    info("bottom row of Phi: %s" % [str(c) for c in bottom])
    check(all(c == 0 for c in bottom[:6])
          and (bottom[6] - base(P_GATE)).valuation() >= cert,
          "measured: the last row is (0,...,0,p) to the certified p^%d.  The "
          "span IS stable and Phi acts on the residue line by p, exactly as "
          "the disk argument says -- so the 33-dimensional H^1_rig(U) is not "
          "needed" % cert)
    dt = (Phi7 - identity_matrix(base, 7)).determinant()
    check(dt.valuation() == 0,
          "det(Phi - I) is a unit, so Algorithm 3.7's linear system is "
          "invertible on the seven-dimensional space: the Coleman integral of "
          "omega_0 is obtainable by exactly the machinery of E061, on a 7 x 7 "
          "system instead of a 6 x 6 one")

    # negative control, criterion fixed before the run: a direction outside
    # the stable span must give a strictly worse solve residual (or fail).
    junk = [QQ(0)] * H.dim_E
    junk[H._index[(0, 0)]] = QQ(1)          # dx / r, poles at every zero of r
    ctl, why = None, ""
    try:
        _, ctl = phi_on(junk)
    except Exception as e:
        why = "%s: %s" % (type(e).__name__, e)
    check(ctl is None or ctl < resid7,
          "negative control: replacing [omega_0] by the class of dx/r -- whose "
          "residues sit at the zeros of r, where the span is NOT stable -- "
          "%s, against p^%s for omega_0"
          % ("makes the step-5 solve fail (%s)" % why if ctl is None
             else "drops the solve residual to p^%s" % ctl, resid7))

    # ------------------------------------------------------------ group (6)
    print("(6) WHAT REMAINS")
    info("Tier 2 (E110): the Coleman-Gross normalisation.  omega_{kappa'} = "
         "omega_0 + c_1 dx/Q_y + c_2 x dx/Q_y with (c_1, c_2) in Q_p^2 fixed "
         "by requiring the class to lie in W; E094 already has W as the graph "
         "of tau over the phase-4 basis, and the class of omega_0 in "
         "H^1_dR(X) is read off from the 7 x 7 Phi computed here.")
    info("Tier 3: int_{sigma x_11}^{x_11} omega_{kappa'} by Algorithm 3.7 on "
         "the 7 x 7 system, then h_p = that integral, then")
    info("    b = h_p(kappa', delta_11) - (5/2) log_13(2) + log_13(3).")
    info("What must be watched: the endpoints x_11 and sigma x_11 reduce to "
         "(7,12) and (7,1) mod 13, neither of them over x = 1, so no endpoint "
         "sits in a disk that was newly removed.")

    print("=" * 72)
    print("E109 GATE: %s   (%d failures, %.0f s)"
          % ("*** GREEN ***" if not FAIL else "*** RED ***",
             len(FAIL), time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    return 1 if FAIL else 0


sys.exit(int(main()))  # int(): a Sage Integer here makes sys.exit report failure
