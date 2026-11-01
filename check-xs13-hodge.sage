# check-xs13-hodge.sage --- E065 (E048 Phase 4) GATE, part 10.
#
# E075.  The PUBLISHED VALUES of [BDM+19] §6.1, Hodge half.  Everything E068 to
# E074 built has so far been checked against itself, against point counts and
# against Sage; this is the first time it meets numbers somebody else printed.
#
# X = X_s(13) = X_0^+(169), genus 3, the smooth plane quartic Q = 0 of §6.1,
# affine chart Z != 0, base point b = P_2 = (0,0), the basis omega of §6.1 and
# the two Tate classes Z_1, Z_2 given there.  [BDM+19] print, for each Z_i:
#
#     eta_{Z_1}   = -(44 x^2 + 148/3 xy + 8 y^2) dx/Q_y
#     eta_{Z_2}   = -(40 x^2 + 148 xy + 36 y^2) dx/Q_y
#     beta_Fil,Z_1 = (0, 1/2, 1/2)^T        gamma_Fil,Z_1 =  5y/6 + 3x/2
#     beta_Fil,Z_2 = (0, -1/2, -5/2)^T      gamma_Fil,Z_2 = -5y/6 - 15x/2
#
# ONE OF THOSE IS WRONG, and check (4) finds it: the printed eta_{Z_2} does not
# have the residues §4.5 step (i) asks for, and the differential that does is
#
#     eta_{Z_2}   = -(40 x^2 - 148 xy - 36 y^2) dx/Q_y,
#
# two sign errors.  With it, everything else printed in §6.1 is reproduced.
#
# THE PREDICTIONS, fixed before the gate was run (E074's derivation, and the
# only free signs in the pipeline; the correspondences are taken from the paper
# verbatim, so there is no scale or sign left to fit):
#
#   (P1) eta comes out with the SAME sign as printed.  Our step (i) picks eta
#        with the residues of Omega^T Z omega (E071: that, and not (19)); the
#        published one is picked with the residues of the paper's dg_x, and the
#        two agree iff dg_x = -(Omega^T Z omega - eta), which is the sign
#        relation E074 derived from G_x = s_x^{-1} s_0.
#   (P2) So (beta, gamma) come out as the NEGATIVES of the printed pair -- our
#        solver writes the condition as "g_x - gamma - beta^T Omega_x regular"
#        with ITS g_x.  A sign error anywhere in E068-E074 would show up here as
#        a mismatch that is not a global sign.
#   (P3) gamma_Fil is UNIQUE (shifting beta by a holomorphic direction leaves
#        the condition unchanged with the same gamma, and gamma(b) = 0 kills the
#        constant), and so are the LAST g coordinates of beta_Fil.  The first g
#        are convention.  So the printed 3-vector must be the last three, which
#        is what E070 guessed from its own solve; that guess is tested here.
#   (P4) The published pair satisfies E074's CORRECTED condition and not the
#        printed one.  This is convention-free -- it does not depend on which
#        beta inside the coset either side chose -- and it is the sharpest test
#        of E074 available: the correction was derived from Hadian's theorem,
#        and §6.1's numbers were produced by somebody else's implementation.
#
# THE CHECKS.  All exact over Q; no p-adic arithmetic anywhere.  §5 of
# [BDM+19] and the prime 17 are E076.
#
#   (1) THE MODEL.  Q is Baran's equation under the substitution of §6.1, the
#       seven listed points lie on it, the genus is 3, and the reduction is
#       smooth at 17 and singular at 13 -- the two facts Remark 6.1 gives for
#       choosing p = 17.
#   (2) THE BASIS.  The six printed differentials lie in Tuitman's E, are a
#       basis of H^1_dR(X), have their first three spanning H^0(X, Omega^1)
#       ([BT] Def 2.16(1)) and are SYMPLECTIC for the cup product (§4.2).  The
#       last is an independent test of E066's cup product: the basis is
#       somebody else's and the answer must be exactly J.
#   (3) THE CORRESPONDENCES.  Z_1 and Z_2 satisfy §4.1 (b), (c), (d) -- (a) is
#       p-adic and belongs to E076 -- and are independent.
#   (4) eta, both correspondences.  §4.4 pins eta only INSIDE the span of the
#       unprinted omega_6, omega_7, omega_8, so the printed values cannot be
#       reproduced from Z alone -- but both are (quadratic in x, y) dx/Q_y, so
#       the span is visible, and inside it eta IS unique.        [P1]
#   (5) beta_Fil and gamma_Fil, both correspondences, both conditions, against
#       the printed ones.                                         [P2, P3]
#   (6) THE DEFECT OF THE PUBLISHED PAIR under each of the two conditions, at
#       every place of D.                                         [P4]
#   (7) THE NEW LOCAL EXPANSIONS against Sage's own completion map, on all
#       four curves.  Sage's map is EXPONENTIAL in the requested precision on
#       this curve -- 0.1 s at 2, 0.2 s at 3, 1.1 s at 4, 52 s at 6, at each of
#       the three places -- so E068-E074's route cannot reach the precision 28
#       that §4.5 needs here.  padic/coho.py now expands x and y once and
#       derives every other element by series arithmetic, refining the pair by
#       Newton on Q(x,y) = 0 and T(x,y) = t.  This check is what makes that
#       legitimate; the E068-E074 gates are its regression.  It runs last
#       because it is the only slow thing here, and the slow half is SAGE's.
#
# Run: sage check-xs13-hodge.sage

import sys, time
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology

t_start = time.time()
fails = []


def check(ok, msg):
    print("   %s  %s" % (msg, "ok" if ok else "*** NO ***"))
    if not ok:
        fails.append(msg)
    sys.stdout.flush()
    return ok


def pole_order(s):
    if s.is_zero():
        return ZZ(0)
    return max(ZZ(0), -ZZ(s.valuation()))


# ------------------------------------------------------------------ the data

P3 = PolynomialRing(QQ, ['X', 'Y', 'Z'])
X, Y, Z = P3.gens()
BARAN = ((-Y-Z)*X**3 + (2*Y**2+Z*Y)*X**2 + (-Y**3+Z*Y**2-2*Z**2*Y+Z**3)*X
         + (2*Z**2*Y**2-3*Z**3*Y))
QUARTIC = (Y**4 + 5*X**4 - 6*X**2*Y**2 + 6*X**3*Z + 26*X**2*Y*Z + 10*X*Y**2*Z
           - 10*Y**3*Z - 32*X**2*Z**2 - 40*X*Y*Z**2 + 24*Y**2*Z**2 + 32*X*Z**3
           - 16*Y*Z**3)
POINTS = [("P_0", (1, 1, 1)), ("P_1", (1, 1, 2)), ("P_2", (0, 0, 1)),
          ("P_3", (-3, 3, 2)), ("P_4", (1, 1, 0)), ("P_5", (0, 2, 1)),
          ("P_6", (-1, 1, 0))]

R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Qxy = QUARTIC(x, y, 1)

# [BDM+19] §6.1, the numerators of omega_0, ..., omega_5 over dx/Q_y
OMEGA_NUM = [
    R2(1),
    x,
    y,
    -160*x**4/3 + 736*x**3/3 - 16*x**2*y/3 + 436*x**2/3 - 440*x*y/3 + 68*y**2/3,
    -80*x**3/3 + 44*x**2 - 40*x*y/3 + 68*y**2/3 - 32,
    -16*x**2*y + 28*x**2 + 72*x*y - 4*y**2 - 160*x/3 + 272/3,
]

Z1 = matrix(QQ, [[0, -976, -1104, 10, -6, 18],
                 [976, 0, -816, -3, 1, 3],
                 [1104, 816, 0, -3, 3, -11],
                 [-10, 3, 3, 0, 0, 0],
                 [6, -1, -3, 0, 0, 0],
                 [-18, -3, 11, 0, 0, 0]])
Z2 = matrix(QQ, [[0, 112, -656, -6, 6, 6],
                 [-112, 0, -2576, 15, 9, 27],
                 [656, 2576, 0, 3, 3, -3],
                 [6, -15, -3, 0, 0, 0],
                 [-6, -9, -3, 0, 0, 0],
                 [-6, -27, 3, 0, 0, 0]])

# The published Hodge data, per correspondence: the numerator of eta over
# dx/Q_y AS PRINTED, the same numerator AS IT MUST BE (E075: for Z_2 the
# printed one does not have the residues step (i) asks for; the entry below is
# what check (4) SOLVES for, and it is recorded here so that later runs
# regress against it), beta_Fil as printed and gamma_Fil as printed.
PUBLISHED = [
    ("Z_1", Z1,
     -(44*x**2 + 148*x*y/3 + 8*y**2),
     -(44*x**2 + 148*x*y/3 + 8*y**2),
     [QQ(0), QQ(1)/2, QQ(1)/2],
     5*y/6 + 3*x/2),
    ("Z_2", Z2,
     -(40*x**2 + 148*x*y + 36*y**2),
     -(40*x**2 - 148*x*y - 36*y**2),
     [QQ(0), QQ(-1)/2, QQ(-5)/2],
     -5*y/6 - 15*x/2),
]

BASE = (QQ(0), QQ(0))                        # b = P_2 = (0 : 0 : 1)

print("=== check-xs13-hodge.sage --- E065 gate: the published X_s(13) "
      "values of [BDM+19] §6.1, Hodge half (E075) ===")

# -------------------------------------------------------------- (1) the model

print("-" * 72)
print("(1) the model")
sub = QUARTIC(X-Y, X+Y, X+Z)
lam = None
for m in BARAN.monomials():
    lam = sub.monomial_coefficient(m) / BARAN.monomial_coefficient(m)
    break
check(sub == lam * BARAN,
      "Q(X-Y, X+Y, X+Z) = (%s) * Baran's equation" % lam)
check(all(QUARTIC(*v) == 0 for _, v in POINTS),
      "the seven points of §6.1 lie on Q = 0")
check(len(set(POINTS[i][1] for i in range(len(POINTS)))) == 7,
      "the seven points are distinct")

t0 = time.time()
C = TuitmanCurve(Qxy, name="X_s(13)")
H = Cohomology(C)
g, n = ZZ(C.genus), 2 * ZZ(C.genus)
check(g == 3, "genus 3")
check(C.W0_is_identity, "Tuitman's Assumption 2 (W^0 = I) holds")
print("   deg r = %s, d_x = %s  (%.1f s)" % (C.degr, C.dx, time.time()-t0))


def smooth_mod(q):
    """Is the plane quartic Q = 0 smooth over F_q?"""
    Fq = GF(q)
    S = PolynomialRing(Fq, ['X', 'Y', 'Z'])
    Qq = S(QUARTIC)
    I = S.ideal([Qq.derivative(v) for v in S.gens()] + [Qq])
    return I.dimension() <= 0


check(smooth_mod(17), "the reduction at p = 17 is a smooth plane quartic")
check(not smooth_mod(13), "the reduction at 13 is singular (Remark 6.1)")
check(not smooth_mod(2), "the reduction at 2 is singular (§6.1)")

# -------------------------------------------------------------- (2) the basis

print("-" * 72)
print("(2) the basis omega of §6.1")
L, xL, yL = C.L, C.L(C.x), C.y
dxL = xL.differential()


def toL(f):
    return sum(QQ(c) * xL**ZZ(e[0]) * yL**ZZ(e[1]) for e, c in f.dict().items())


QyL = toL(Qxy.derivative(y))


def omega_of(fnum):
    """(polynomial in x, y) dx / Q_y as a differential of L."""
    return (toL(fnum) / QyL) * dxL


t0 = time.time()
reps = [H.form_in_E(omega_of(f)) for f in OMEGA_NUM]
check(all(H.differential_of(reps[i]) == omega_of(OMEGA_NUM[i])
          for i in range(n)),
      "all six lie in Tuitman's E (round trip through E-coordinates)")

bas, _ = H.H1X_basis()
dM = H.d_matrix()
cols = [vector(QQ, list(b)) for b in bas] \
    + [dM.column(j) for j in range(dM.ncols())]
Msolve = matrix(QQ, cols).transpose()
S = matrix(QQ, [list(Msolve.solve_right(vector(QQ, v)))[:n] for v in reps])
check(S.determinant() != 0, "they are a basis of H^1_dR(X)")

T = H.holomorphic_classes(reps)
check(T.submatrix(0, g, g, n - g) == 0 and T.submatrix(0, 0, g, g) != 0
      and T.submatrix(0, 0, g, g).determinant() != 0,
      "omega_0, omega_1, omega_2 span H^0(X, Omega^1) ([BT] Def 2.16(1))")

forms = [H.differential_of(v) for v in reps]
places = H._pole_places(forms)
print("   D has %d places over x = infinity, of degrees %s, total %d"
      % (len(places), [ZZ(P.degree()) for P in places],
         sum(ZZ(P.degree()) for P in places)))
check(sum(ZZ(P.degree()) for P in places) == 4,
      "d = #D(Qbar) = 4, so the third-kind part has dimension d - 1 = 3")
check(len(H.third_kind_basis()) == 3, "third_kind_basis returns 3 elements")
print("   (%.1f s)" % (time.time() - t0))
sys.stdout.flush()

t0 = time.time()
Mcup = H.cup_product_matrix(basis=reps)
J = matrix(QQ, n, n, lambda i, j: QQ(1) if (i < g and j == i + g) else
           (QQ(-1) if (i >= g and j == i - g) else QQ(0)))
check(Mcup == J or Mcup == -J,
      "the cup product matrix is the standard symplectic form (§4.2)")
print("   cup product = %sJ  (%.0f s)"
      % ("" if Mcup == J else "-", time.time() - t0))
sys.stdout.flush()

# ----------------------------------------------------- (3) the correspondences

print("-" * 72)
print("(3) the correspondences Z_1, Z_2 of §6.1 against §4.1")
for (nm, Zm, _, _, _, _) in PUBLISHED:
    check(Zm.transpose() == -Zm, "%s: (d) Z is antisymmetric" % nm)
    check((Zm.transpose() * Mcup).trace() == 0,
          "%s: (c) Z dies under the cup product H^1 (x) H^1 -> H^2" % nm)
    check(Zm.submatrix(g, g, g, g) == 0,
          "%s: (b) Z lies in Fil^1(H^1 (x) H^1)" % nm)
    Ze = Zm * Mcup
    check(Ze.base_ring() == QQ and all(c in ZZ for c in Ze.list())
          and Ze.trace() == 0 and Mcup * Ze == Ze.transpose() * Mcup,
          "%s: the endomorphism Z M is integral, trace zero, Rosati-symmetric"
          % nm)
check(matrix(QQ, [Z1.list(), Z2.list()]).rank() == 2,
      "Z_1 and Z_2 are independent (the 2 = g + rho - 1 - r of §6)")

# ------------------------------------------------------------------- (4) eta

RESPREC = 4 * H.worst_pole(forms) + 10     # the precision E066's cup product
                                           # already built and cached


def residues(om, prec=RESPREC):
    """The residues of a differential at the places of D."""
    out = []
    for P in places:
        m = H.expansion_at(P, prec)
        s = m(om / xL.differential() / P.local_uniformizer().derivative())
        out.append(s[-1])
    return out


def res_vector(om):
    """The residues of a differential at the places of D, flattened over Q."""
    out = []
    for c in residues(om):
        out += [QQ(a) for a in
                (c.vector() if hasattr(c, "vector") else [c])]
    return out


print("-" * 72)
print("(4) eta   [P1]")
# §4.4 pins eta only INSIDE THE SPAN of omega_6, ..., omega_8, and §6.1 does
# not print those.  But both printed etas are (quadratic in x, y) dx/Q_y, so
# the span is visible: it is this one.  Everything below is a solve inside it,
# never a fit -- the residues come from Z and from nothing else.
SPAN3 = [x**2, x*y, y**2]
span3 = [omega_of(f) for f in SPAN3]
check(all(H.pole_order(o, P) == 1 for o in span3 for P in places),
      "x^2, xy, y^2 over dx/Q_y are of the third kind")
RES3 = matrix(QQ, [res_vector(o) for o in span3]).transpose()
check(RES3.rank() == 3,
      "their residues are independent, so eta is unique inside their span")

etafix = {}
for (nm, Zm, etanum, etatrue, _, _) in PUBLISHED:
    t0 = time.time()
    theirs = omega_of(etanum)
    check(all(H.pole_order(theirs, P) == 1 for P in places),
          "%s: the printed eta is of the third kind (simple poles on D)" % nm)
    _, etavec, _, _ = H.hodge_eta(Zm, basis=reps)
    ours = H.differential_of(etavec)
    ro = res_vector(ours)
    # the unique element of the span with the residues step (i) asks for
    sol = RES3.solve_right(vector(QQ, ro))
    fixed = sum((sol[i] * SPAN3[i] for i in range(3)), R2(0))
    etafix[nm] = H.form_in_E(omega_of(fixed))
    check(fixed == R2(etatrue),
          "%s: step (i) gives -(%s) dx/Q_y inside that span" % (nm, -fixed))
    agree = (R2(etanum) == R2(etatrue))
    check(agree == (nm == "Z_1"),
          "%s: and that %s the printed eta%s"
          % (nm, "IS" if agree else "is NOT",
             "" if agree else
             "  -- §6.1 prints -(%s), whose xy and y^2 coefficients have the "
             "wrong sign" % (-R2(etanum))))
    print("      (%.0f s)" % (time.time() - t0))
    sys.stdout.flush()

# ------------------------------------------------- (5) and (6) beta and gamma


def defect(info, Zm, beta_vec, gamma_fn):
    """Worst pole order of  g_x - gamma - beta^T Omega  over the places of D,
    for the corrected and for the printed condition, and of the correction.

    The pair is the SOLVER's, i.e. the one that makes "g_x - gamma - beta^T
    Omega regular" the condition; E074 derived that [BDM+19]'s pair is its
    negative, so the published values are passed in negated.
    """
    dc, dp, dA = ZZ(0), ZZ(0), ZZ(0)
    for (P, Om, gx_used) in info["local"]:
        A = H._fil0_quadratic(Zm, Om, n, g)
        gx = gx_used + A if info["fil0_correction"] else gx_used
        m = H.local_data(P, info["prec"], reps)[0]
        e = gx - m(gamma_fn)
        for i in range(n):
            if beta_vec[i] != 0:
                e = e - QQ(beta_vec[i]) * Om[i]
        dp = max(dp, pole_order(e))
        dc = max(dc, pole_order(e - A))
        dA = max(dA, pole_order(A))
    return dc, dp, dA


print("-" * 72)
print("(5) beta_Fil and gamma_Fil, against the printed ones"
      "   [P2: negated; P3: the printed 3-vector is the LAST g]")
print("    Both signs of eta and both forms of the condition are run: exactly")
print("    one must reproduce §6.1, and it must be the same one for both")
print("    correspondences.  Nothing here is chosen to fit.")
solves, hits = {}, {}
for (nm, Zm, _, _, betapub, gammapub) in PUBLISHED:
    pred_beta = [QQ(0)] * g + [-QQ(c) for c in betapub]
    pred_gamma = -toL(R2(gammapub))
    for sg in (1, -1):
        ev = [sg * QQ(c) for c in etafix[nm]]
        for corr in (True, False):
            tag = "eta %+d, %s" % (sg, "corrected" if corr else "printed  ")
            t0 = time.time()
            try:
                beta, gamma, info = H.hodge_filtration(
                    Zm, eta=ev, base=BASE, basis=reps, fil0_correction=corr)
            except ArithmeticError as e:
                print("   %s, %s: NO SOLUTION -- %s" % (nm, tag, e))
                sys.stdout.flush()
                continue
            solves[(nm, sg, corr)] = (beta, gamma, info)
            ok = (list(beta) == pred_beta) and (gamma == pred_gamma)
            hits[(nm, sg, corr)] = ok
            print("   %s, %s: beta = %s%s   (%.0f s)"
                  % (nm, tag, beta, "   <== REPRODUCES §6.1" if ok else "",
                     time.time() - t0))
            print("      gamma = %s" % gamma)
            sys.stdout.flush()
    win = [k for k, v in hits.items() if v and k[0] == nm]
    check(len(win) == 1, "%s: exactly one of the four combinations reproduces "
          "beta_Fil and gamma_Fil (%d do)" % (nm, len(win)))
    if win:
        print("      winner: eta sign %+d, %s condition"
              % (win[0][1], "corrected" if win[0][2] else "printed"))
w1 = [k[1:] for k, v in hits.items() if v and k[0] == "Z_1"]
w2 = [k[1:] for k, v in hits.items() if v and k[0] == "Z_2"]
check(w1 and w1 == w2, "the winning combination is the same for Z_1 and Z_2")
if w1 and w1 == w2:
    check(w1[0][1], "and it is E074's CORRECTED condition, not the printed "
          "one   [P4]")
    check(w1[0][0] == 1,
          "and eta enters dg_x with the sign of §4.5 step (i)   [P1]")

print("-" * 72)
print("(6) the defect of the PUBLISHED pair, convention-free   [P4]")
for (nm, Zm, _, _, betapub, gammapub) in PUBLISHED:
    key = (nm, 1, True)
    if key not in solves:
        check(False, "%s: no solve to measure the defect against" % nm)
        continue
    info = solves[key][2]
    bvec = [QQ(0)] * g + [-QQ(c) for c in betapub]
    dc, dp, dA = defect(info, Zm, bvec, -toL(R2(gammapub)))
    print("   %s: Omega^T Z s_2 Omega has a pole of order %s at worst" % (nm, dA))
    check(dc == 0, "   %s: the published pair solves E074's CORRECTED "
          "condition (defect %s)" % (nm, dc))
    check(dp > 0, "   %s: it does NOT solve the condition PRINTED in step "
          "(iii) (defect %s)" % (nm, dp))

# ------------------------------------------------ (7) the new local expansions

print("-" * 72)
print("(7) _LocalExpansion against Sage's completion map")
for (nm, Qc, pr, own) in [("y^2 = x^5-1", y**2 - (x**5 - 1), 6, None),
                          ("y^2 = x^6+x^4-x^2+1",
                           y**2 - (x**6+x**4-x**2+1), 6, None),
                          ("C_4", y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4),
                           6, None),
                          ("X_s(13)", Qxy, 4, reps)]:
    t0 = time.time()
    if own is None:
        Cc = TuitmanCurve(Qc, name=nm)
        Hc = Cohomology(Cc)
        vecs = Hc.H1X_basis()[0]
    else:
        Cc, Hc, vecs = C, H, own
    Lc, xc = Cc.L, Cc.L(Cc.x)
    fc = [Hc.differential_of(v) for v in vecs]
    bad, tot, seeds = 0, 0, set()
    for Pc in Hc._pole_places(fc):
        fast = Hc.expansion_at(Pc, pr)
        seeds.add(fast.seed)
        slow = Lc.completion(Pc, prec=pr)
        dtdx = Pc.local_uniformizer().derivative()
        els = [Cc.y, xc, Cc.y**2, Cc.y**3, 1 / Lc(Cc.r), 1 / dtdx] \
            + list(Lc.maximal_order().basis())
        if own is None:
            els += [o / xc.differential() / dtdx for o in fc]
        # On X_s(13) the forms themselves are left out, and not to be kind to
        # ourselves: Sage is priced per ELEMENT as well as per precision there.
        # At precision 4 and at a place of degree 1 it expands y in 1.2 s and
        # y^2 in 1.5 s, and it had not finished ONE of the six forms -- each of
        # which carries a 1/Q_y and a numerator of forty monomials -- after two
        # hours.  The list above is exactly the set of atoms __call__ builds
        # every expansion out of, by Horner in x, powers of y and one division,
        # so what is left untested on this curve is only the bookkeeping that
        # the other three curves test in full.
        for el in els:
            tot += 1
            if fast(el) != slow(el):
                bad += 1
    check(bad == 0, "%s: %d expansions at precision %d agree exactly "
          "(Newton seeds %s, %.0f s)"
          % (nm, tot, pr, sorted(seeds), time.time() - t0))

# ---------------------------------------------------------------- the verdict

print("=" * 72)
print("total %.0f s" % (time.time() - t_start))
if fails:
    print("E075 GATE: *** RED ***  (%d failures)" % len(fails))
    for f in fails:
        print("   -", f.strip())
else:
    print("E075 GATE: GREEN")
