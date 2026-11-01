# check-qc-gate0.sage --- E065 (E048 Phase 4) GATE 0.
#
# The four cheap, decisive checks that E065 requires BEFORE any quadratic
# Chabauty code is written.  Same discipline as E048's Phase 0.
#
#   (a) Does C_4 have potentially good reduction at l = 2, 3?  The one input of
#       BDMTV Algorithm 3.12 that its authors call outside the scope of their
#       implementation is the local height function at primes that do NOT.
#       Two computations here: the branch locus of C_4 -> E and how it
#       degenerates, and an exhaustive search for a good model in the scaling
#       family.
#   (c) Which p?  Remark 3.15 gives the cheap splitting of the Hodge filtration
#       -- the unit root subspace -- only at ORDINARY p.  Test ordinariness and
#       measure what the resulting prime costs on the bad point (0,0).
#   (d) Can the cup product be read off Frobenius via Phi^T M Phi = p M?
#
# ((b), the count of unknowns in the height pairing, is arithmetic done in the
# report: it needs no computation beyond what is printed here.)
#
# Run: sage check-qc-gate0.sage

import sys, time, itertools
sys.path.insert(0, '.')
from padic.auxpolys import TuitmanCurve
from padic.coho import Cohomology
from padic.points import CurvePoint
from padic.integrals import ColemanIntegrals, tprec_for
from padic.frobenius import FrobeniusMatrix

R = PolynomialRing(QQ, ['x', 'y'])
x, y = R.gens()
C4 = y**4 - 6*(x-1)**2*y**2 + 27*x*(x**3-4)

Rt = PolynomialRing(QQ, ['t', 'w', 'z'])
t, w, z = Rt.gens()
F0 = w**4 - 6*(t - z)**2 * w**2 + 27*t**4 - 108*t*z**3      # homogenised C_4


# ----------------------------------------------------------------- (a) part 1

def branch_locus():
    print("(a1) The branch locus of the double cover C_4 -> E.")
    print("     sigma : w -> -w has fixed locus w = 0, i.e. 27 t (t^3-4) = 0,")
    print("     so C_4 -> E is branched at FOUR points: t = 0 and t^3 = 4.")
    print("     (Riemann-Hurwitz: 2*3-2 = 2(2*1-2) + 4.)")
    E = EllipticCurve([-36, 0])
    print("     E : y^2 = x^3-36x has j = %s (integral) => POTENTIALLY GOOD"
          % E.j_invariant())
    print("     reduction everywhere; E has CM by Z[i], so a_p(E) = 0 iff p = 3 mod 4.")
    for l in [3, 2]:
        K = NumberField(x**3 - 4, 'a') if False else None
        v0 = QQ(ZZ(4).valuation(l)) / 3          # v(4^{1/3}), v(l) = 1
        vz = QQ(1) / 2 if l == 3 else QQ(0)      # v(1 - zeta_3)
        print("     l = %d : v(4^(1/3)) = %s, v(1-zeta_3) = %s"
              % (l, v0, vz))
        print("             pairwise distance of the three cube roots : %s"
              % (v0 + vz))
        print("             distance from t = 0                       : %s" % v0)
        if v0 == 0 and vz > 0:
            print("             => the THREE cube roots collide, t = 0 stays apart")
        elif v0 > 0:
            print("             => ALL FOUR branch points collide")
    print("     In residue characteristic != 2 the stable model of a double")
    print("     cover is governed by this configuration (admissible covers);")
    print("     at l = 2 the residue characteristic equals the degree of the")
    print("     cover, the cover is wild, and that reading does not apply.")
    sys.stdout.flush()


# ----------------------------------------------------------------- (a) part 2

def reduction_at(md, l, a, b):
    vals = [v + i * b + j * a for (i, j, k, v, c) in md]
    m = min(vals)
    S = PolynomialRing(GF(l), ['t', 'w', 'z'])
    T, W, Z = S.gens()
    G = S.zero()
    for (i, j, k, v, c), vv in zip(md, vals):
        if vv == m:
            G += S(GF(l)(c / l**c.valuation(l))) * T**i * W**j * Z**k
    return G


def smooth_quartic(G):
    if G == 0 or G.total_degree() != 4 or not G.is_squarefree():
        return False
    S = G.parent()
    J = S.ideal([G] + list(G.gradient()))
    return J.saturation(S.ideal(S.gens()))[0].is_one()


def scaling_search(l, shifts=range(0, 4)):
    """EXHAUSTIVE inside the family (t,w,z) -> (l^b T + c Z, l^a W + d Z, Z).

    Which monomials survive depends on (a,b) only through the argmin set, which
    is constant on the cells of a polyhedral subdivision; so testing every
    pairwise-tie line and every triple-tie point covers every reduction the
    family can produce.  No grid and no cutoff -- but also no proof of bad
    reduction if nothing is found, since PGL_3 is bigger than this family.
    """
    found = None
    for st in shifts:
        for sw in shifts:
            F = F0.subs({t: t + st * z, w: w + sw * z})
            md = [(mon.degree(t), mon.degree(w), mon.degree(z),
                   QQ(c.valuation(l)), c)
                  for mon, c in zip(F.monomials(), F.coefficients()) if c != 0]
            lines = []
            for u, v in itertools.combinations(range(len(md)), 2):
                (i1, j1, _, v1, _), (i2, j2, _, v2, _) = md[u], md[v]
                if (j1 - j2, i1 - i2) != (0, 0):
                    lines.append(((j1 - j2, i1 - i2), v2 - v1))
            pts = set()
            for (A1, r1), (A2, r2) in itertools.combinations(lines, 2):
                M = matrix(QQ, [list(A1), list(A2)])
                if M.rank() == 2:
                    s = M.solve_right(vector(QQ, [r1, r2]))
                    pts.add((s[0], s[1]))
            for (a, b) in pts:
                if smooth_quartic(reduction_at(md, l, a, b)):
                    found = (st, sw, a, b)
                    return found
    return found


# --------------------------------------------------------------------- (c)

def ordinariness():
    print("(c1) Ordinary primes.  Jac(C_4) ~ E x P, and the unit root splitting")
    print("     of Remark 3.15 needs BOTH factors ordinary.")
    E = EllipticCurve([-36, 0])
    prym = {5: 25*x**4+20*x**3+10*x**2+4*x+1, 7: 49*x**4+21*x**3+6*x**2+3*x+1,
            11: 121*x**4+22*x**3+18*x**2+2*x+1, 13: 169*x**4+13*x**3+8*x**2+x+1}
    print("      p | Prym middle coeff | P ord | a_p(E) | E ord | Jac ord")
    for p in sorted(prym):
        # ZZ(...) is not decoration: prym[p] lives in a polynomial ring over
        # QQ, and "c % p" there is polynomial division by a unit, which is 0
        # for every p.  That silently reported every prime as non-ordinary.
        c = ZZ(prym[p].coefficient({x: 2}))
        po = (c % p != 0)
        ap = E.ap(p)
        eo = (ap % p != 0)
        print("     %2d | %17s | %5s | %6s | %5s | %s"
              % (p, c, po, ap, eo, po and eo))
    print("     E has CM by Z[i] (j = 1728), so a_p(E) = 0 exactly for")
    print("     p = 3 mod 4: p = 7, 11 are supersingular for E and unusable.")
    sys.stdout.flush()


def cost_at(p, N, es):
    print("(c2) Cost of Algorithm 3.12 from (0,0) at p = %d, N = %d." % (p, N))
    print("     t-adic truncations: %s"
          % {e: tprec_for(p, N, e) for e in [1] + list(es)})
    t0 = time.time()
    C = TuitmanCurve(C4, name='C_4')
    H = Cohomology(C)
    FM = FrobeniusMatrix(C, H, p, N)
    FM.compute(primitives=True)
    print("     Phi: %.0f s, chi certified to p^%s"
          % (time.time() - t0, FM.certified_precision()[0]))
    sys.stdout.flush()
    CI = ColemanIntegrals(FM)
    B = CurvePoint(FM.RR, FM.base(0), y=FM.base(0))
    Ry = PolynomialRing(FM.base, 'Y')
    Yv = Ry.gen()
    q0 = Ry.zero()
    for (ex, ey), cc in C4.dict().items():
        q0 += FM.RR._coerce_QQ(cc) * FM.base(1)**ZZ(ex) * Yv**ZZ(ey)
    P = None
    for r, _ in q0.roots():
        cand = CurvePoint(FM.RR, FM.base(1), y=r)
        if cand.is_good() and cand.on_curve():
            P = cand
            break
    for e in es:
        t0 = time.time()
        v = CI.coleman_integrals_general(B, P, e=e)
        prec = CI.certified_precision(*CI.last_eval_points)
        off = infinity
        for a in v:
            c = list(a.polynomial()) if a != 0 else []
            for i in range(1, len(c)):
                if c[i] != 0:
                    off = min(off, QQ(c[i].valuation()) + QQ(i) / e)
        print("     e = %2d (= %s): %.0f s, certified p^%s, off-Q_p part p^%s"
              % (e, "p e_P + 1" if e == 2*p+1 else "2 p e_P",
                 time.time() - t0, prec, off))
        sys.stdout.flush()


# --------------------------------------------------------------------- (d)

def cup_from_frobenius(label, Qxy, p, N):
    C = TuitmanCurve(Qxy, name=label)
    H = Cohomology(C)
    FM = FrobeniusMatrix(C, H, p, N)
    FM.compute(primitives=True)
    n = 2 * ZZ(C.genus)
    Phi = FM.Phi.transpose()
    cert = ZZ(FM.certified_precision()[0])
    Zk = Zmod(p**cert)
    PhiZ = matrix(Zk, n, n, [Zk(ZZ(Phi[i][j])) if Phi[i][j] != 0 else Zk(0)
                             for i in range(n) for j in range(n)])
    idx = [(i, j) for i in range(n) for j in range(i + 1, n)]
    rows = []
    for (a, b) in idx:
        E = matrix(Zk, n, n)
        E[a, b], E[b, a] = Zk(1), Zk(-1)
        D = PhiZ.transpose() * E * PhiZ - Zk(p) * E
        rows.append([D[i][j] for i in range(n) for j in range(n)])
    ker = matrix(Zk, rows).transpose().right_kernel()
    gens = list(ker.gens())
    nondeg = 0
    for v in gens:
        M = matrix(Zk, n, n)
        for c, (a, b) in zip(v, idx):
            M[a, b], M[b, a] = c, -c
        L = matrix(ZZ, n, n, [ZZ(M[i][j]) for i in range(n) for j in range(n)])
        vv = min([L[i][j].valuation(p) for i in range(n) for j in range(n)
                  if L[i][j] != 0] or [cert])
        if vv < cert:
            Mp = matrix(GF(p), n, n, [GF(p)(L[i][j] // p**vv)
                                      for i in range(n) for j in range(n)])
            if Mp.rank() == n:
                nondeg += 1
    print("     %-14s p=%2d: %2d generators mod p^%d, %d of them nondegenerate "
          "mod p" % (label, p, len(gens), cert, nondeg))
    sys.stdout.flush()


def main():
    print("=== check-qc-gate0.sage --- E065 Gate 0 (BDMTV Alg 3.12) ===")
    print()
    branch_locus()
    print()
    print("(a2) Exhaustive search for a good model in the scaling family:")
    for l in [3, 2]:
        t0 = time.time()
        r = scaling_search(l)
        print("     l = %d: C_4 mod %d is %s -> %s   (%.0f s)"
              % (l, l, F0.change_ring(GF(l)),
                 "SMOOTH MODEL %s" % (r,) if r else
                 "no smooth reduction in this family (NOT a proof of bad "
                 "reduction: PGL_3 is bigger)", time.time() - t0))
        sys.stdout.flush()
    print()
    ordinariness()
    print()
    cost_at(13, 8, [27, 52])
    print()
    print("(d) Can the cup product be recovered from Phi^T M Phi = p M?")
    for (lab, Q, p, N) in [("y^2=x^5-1", y**2 - (x**5-1), 11, 8),
                           ("y^2=x^7-1", y**2 - (x**7-1), 11, 8),
                           ("C_4", C4, 13, 8)]:
        cup_from_frobenius(lab, Q, p, N)
    print("     A nondegenerate solution is what the cup product would be.")
    print("     STRUCTURAL OBSTRUCTION: if f in End(J) is Rosati-symmetric and")
    print("     commutes with Phi, then M_f(u,v) := M(f u, v) solves the same")
    print("     equation.  Jac(C_4) ~ E x P gives two such projectors, so the")
    print("     solution space has dimension >= 2 and the equation CANNOT pin")
    print("     the cup product down -- for the very reason (rho >= 2) that")
    print("     makes quadratic Chabauty applicable to C_4 at all.")
    print("=" * 70)
    print("GATE 0: see E065 for the reading of these numbers.")


main()
