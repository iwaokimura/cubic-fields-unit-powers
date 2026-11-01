## check-c4-dv3.sage --- E125: the regular model of C_4 over Z_3 WITHOUT Magma.
##
## paper2's rem:certificate discloses one third-party input: the regular models
## on which the local heights away from p are read off.  They came from Magma's
## RegularModel (E103 at l = 2, E105 at l = 3), via magma_free.  RegularModel is
## Steve Donnelly's implementation and HAS NO PUBLISHED ALGORITHM -- the only
## published description of what it does is three lines in van Bommel,
## "Efficient computation of BSD invariants in genus 2" (arXiv:2002.04667) 2.1.
## So there is nothing to port.  This script does not port it.  It builds a
## regular model by a DIFFERENT construction, from a theorem we can cite:
##
##     T. Dokchitser, Models of curves over discrete valuation rings,
##     Duke Math. J. 170 (2021), no. 11, 2519-2574.
##
## SOURCE VERSION.  Implemented from arXiv:1807.00025v2 (2021-01-10).  The published
## version was not consulted (user decision, 2026-08-29; E125 8.1).  All
## numbering below is v2's.  The statements used, one per line, so that a later
## comparison with the published version is a matter of reading this list:
##
##   Not. 2.1   L* = unique affine Z^2 ->> Z with L*|_L = 0, L*|_Delta >= 0
##   Def 3.1    v-vertices / v-edges / v-faces = faces of the lower hull Delta_v
##   Not. 3.2   delta_lambda = common denominator of v on lambda-bar(Z)
##                           = index of the affine lattice it spans
##   Def 3.4    restriction f|_S to the affine lattice spanned by S
##   Def 3.5    reduction (divide by pi^{v_F}, reduce mod pi)
##   Def 3.7    X_L in G_m, X_F in G_m^2, X_F-bar its completion
##   Def 3.9    Delta_v-regularity: all X_F, X_L smooth, with one exception for
##              outer L with delta_L = delta_F
##   Def 3.12   slopes [s_1, s_2] at a v-edge
##   Thm 3.13   the r.n.c. model: X_F-bar of multiplicity delta_F and genus
##              |F(Z)_Z|; per v-edge, |X_L(kbar)| chains of P^1s
##   Thm 3.14   (3),(4): how the chains attach, all intersections transversal
##   Rem 3.15   the chain = minimal unimodular (Hirzebruch-Jung) sequence
##   Rem 3.19   reduction of points: minimise L_P(i,j,z) = v(x)i + v(y)j + z
##   Thm 6.1    dim H_1(dual graph) = |Delta(Z)^L_Z|
##   Rem 1.5(a) applies to WILD reduction -- why this route exists at all
##
## WHAT IS COMPARED WITH E105, AND WHAT IS NOT.  The two constructions share
## only Lipman's existence theorem, and the models are not the same: Magma's is
## regular, Dokchitser's is regular with normal crossings and need not be
## minimal.  THE NUMBER OF COMPONENTS AND THE MULTIPLICITIES MAY DIFFER, and
## here they do (Magma: 10 components, multiplicities (1^7,2,2,2); here: 8
## components, multiplicities (1,6,2,3,1,1,1,1)).  What is compared is what does
## not depend on the model: the component group of the Neron model, and the
## partition of the nine rational points.
##
## Sage rather than PARI/GP, for the 3-dimensional lower convex hull
## (Polyhedron) and the dimension of a multivariate ideal (smoothness).  The
## rest would be at home in gp.
##
## Run:  sage check-c4-dv3.sage        (about a minute)
##
## The implementation of the construction itself lives in dv-model-lib.sage,
## which check-dv-paper-examples.sage tests against the paper's own examples.

import sys
load('dv-model-lib.sage')

# =====================================================================
#                                the run
# =====================================================================
CHARTS = [(QQ(-1)/2, -9), (QQ(1)/4, -9), (4, -9)]
print("=== check-c4-dv3.sage --- E125: the regular model of C_4 over Z_3, without Magma ===")
print("    source: arXiv:1807.00025v2 (published version not consulted; E125 8.1)")

results = []
for (a, b) in CHARTS:
    tag = "chart (a,b) = (%s,%s)" % (a, b)
    print("")
    print("--- %s :  f(x,y) = F(x+a, y+b),  (x,y) = (t-a, w-b) ---" % tag)
    M = Model(clear_den(F0.subs({x: x+a, y: y+b})), LL)

    # ---- A. Delta and Baker
    inter = [tuple(p) for p in M.Delta.integral_points()
             if M.Delta.interior_contains(vector(QQ, p))]
    check(len(inter) == 3, "%s: |Delta(Z)| = 3 = g(C_4) (Baker)" % tag)
    print("  Delta vertices %s, interior points %s"
          % (sorted(tuple(v) for v in M.Delta.vertices_list()), sorted(inter)))

    # ---- B. Delta_v-regularity
    ok, why = M.is_regular()
    check(ok, "%s: f is Delta_v-regular (Def 3.9); obstruction %s" % (tag, why))
    for F in M.faces:
        check(F['delta'] == F['latidx'],
              "%s: delta_F = %s by both Not. 3.2 (1) and (3)" % (tag, F['delta']))
    print("  v-faces:")
    for n, F in enumerate(M.faces):
        print("    %d %-26s delta=%s genus=%s  f|F = %s"
              % (n, sorted(F['verts']), F['delta'], F['genus'], F['red']['poly']))
    print("  v-edges:")
    for n, E in enumerate(M.edges):
        sd = slope_data(M, E); ch = hj_chain(sd['s1'], sd['s2'])
        print("    %d %-16s delta=%s %-5s adj=%-6s s=[%s,%s] chain=%s  f|L = %s"
              % (n, "%s-%s" % (E['p'], E['q']), E['delta'],
                 "inner" if sd['inner'] else "outer", E['adj'], sd['s1'], sd['s2'],
                 ch, E['red']['poly']))
        check(E['delta']*ch[0].denominator() == M.faces[sd['F1']]['delta'],
              "%s: edge %d, delta_L d_0 = delta_F1" % (tag, n))
        if sd['inner']:
            check(E['delta']*ch[-1].denominator() == M.faces[sd['F2']]['delta'],
                  "%s: edge %d, delta_L d_{r+1} = delta_F2" % (tag, n))

    # ---- C. the special fibre (Thm 3.13)
    comp, inc, fidx, edata = fibre(M)
    print("  special fibre: %d geometric components, multiplicities %s"
          % (len(comp), [c[0] for c in comp]))
    b1 = len(inc) - len(comp) + 1
    dzF = sum(F['genus'] for F in M.faces)
    # Delta_v is the LOWER hull, so every supporting plane lies below v and
    # v(P) = max_F v_F(P).  Delta(Z)^L_Z: interior points of Delta lying in no
    # open v-face, with v(P) in Z (Not. 3.2).
    dzLZ = 0
    for p in inter:
        if any(F['poly'].interior_contains(vector(QQ, p)) for F in M.faces): continue
        if max(F['vF'](*p) for F in M.faces) in ZZ: dzLZ += 1
    check(b1 == dzLZ, "%s: b_1(dual graph) = %d = |Delta(Z)^L_Z| = %d (Thm 6.1)"
          % (tag, b1, dzLZ))
    check(dzF == len([p for p in inter
                      if any(F['poly'].interior_contains(vector(QQ,p)) and F['vF'](*p) in ZZ
                             for F in M.faces)]),
          "%s: sum genus(X_F-bar) = |Delta(Z)^F_Z| (Thm 3.13(1))" % tag)

    # ---- D. the intersection matrix
    Mi, m = imatrix(comp, inc)
    check(all(e in ZZ for e in Mi.list()), "%s: M is integral" % tag)
    check(Mi == Mi.T, "%s: M is symmetric" % tag)
    check(Mi*m == 0, "%s: M m = 0" % tag)
    check(Mi.rank() == len(comp)-1, "%s: rank M = n-1 (fibre connected)" % tag)
    check(Mi.right_kernel().basis_matrix().row_space()
          == matrix(QQ, [list(m)]).row_space(), "%s: ker M = Q m exactly" % tag)
    check(all(e <= 0 for e in Mi.eigenvalues()), "%s: M negative semidefinite" % tag)
    Mz = matrix(ZZ, Mi)
    phi = prod([d for d in Mz.elementary_divisors() if d != 0])
    ok = all(abs(Mz.delete_rows([i]).delete_columns([i]).det()) == phi*m[i]^2
             for i in range(len(comp)))
    check(ok, "%s: |det M^(i)| = |Phi| m_i^2 for every i" % tag)

    # ---- E. the component group
    print("  elementary divisors %s  ==>  |Phi| = %s"
          % (Mz.elementary_divisors(), phi))
    check(phi == 16, "%s: |Phi| = 16, agreeing with E105's Magma model" % tag)

    # ---- F. the nine rational points
    part = {}; clamped = set()
    for (t, w) in PTS:
        k, why = reduce_point(M, comp, fidx, edata, t-a, w-b)
        check(k is not None, "%s: (t,w) = (%s,%s) reduces to a component: %s"
              % (tag, t, w, why))
        if k is None: continue
        check(comp[k][0] == 1, "%s: (t,w) = (%s,%s) lands on a multiplicity-1 "
              "component" % (tag, t, w))
        part[(t, w)] = k
        if why[0] == 'chain-end': clamped.add((t, w))
        print("    (t,w) = (%-6s,%-7s) -> component %s %s" % (t, w, k, why))
    lab = {}
    for P, k in part.items():
        lab.setdefault(k, []).append(P)
    check(len(lab) == 3, "%s: the nine points hit exactly three components" % tag)
    # the partition must be E105's A / B / C
    mine = set(frozenset(v) for v in lab.values())
    theirs = set(frozenset(P for P in PTS if E105[P] == c) for c in "ABC")
    check(mine == theirs, "%s: the partition is E105's A/B/C" % tag)
    if len(lab) == 3:
        perm = {}
        for k, ps in lab.items():
            img = set(part.get((t, -w)) for (t, w) in ps)
            perm[k] = img
        moved = [k for k in perm if perm[k] != {k}]
        fixed = [k for k in perm if perm[k] == {k}]
        check(len(moved) == 2 and len(fixed) == 1
              and perm[moved[0]] == {moved[1]} and perm[moved[1]] == {moved[0]},
              "%s: sigma swaps two of the three classes and fixes the third" % tag)
    # ---- H. the local pairing at l = 3 (the analogue of E104's Lambda)
    #  Gross: D-script = D-bar + sum a_i Gamma_i with D-script . Gamma_j = 0,
    #  i.e. M a = -d.  Solvable because m.d = 0, well posed because ker M = Q m.
    #  Normalising a at the base component makes a unique, and
    #  Lambda_{c,k} = a^(c).(e_k - e_base).
    def avec(cc, base):
        n = len(comp)
        d = vector(QQ, [0]*n); d[cc] += 1; d[base] -= 1
        check(m.dot_product(d) == 0, "%s: m . d = 0, so M a = -d is solvable" % tag)
        idx = [i for i in range(n) if i != base]
        ap = Mi.matrix_from_rows_and_columns(idx, idx).solve_right(
            vector(QQ, [-d[i] for i in idx]))
        a = vector(QQ, [0]*n)
        for j, i in enumerate(idx): a[i] = ap[j]
        check(Mi*a + d == 0, "%s: M a = -d exactly (all n equations)" % tag)
        return a
    def lam(base, cs):
        A = [avec(c, base) for c in cs]
        return matrix(QQ, len(cs), len(cs),
                      [[A[i][cs[j]] - A[i][base] for j in range(len(cs))]
                       for i in range(len(cs))])
    BASE = (1, 3)                                # E072/E073/E084's base point
    cls = [part[BASE], part[(1, -3)], part[(-1, 3)]]      # A (base), B, C
    check(len(set(cls)) == 3, "%s: A, B, C are three distinct components" % tag)
    Lam = lam(part[BASE], cls)
    print("  local pairing at l = 3, normalised at b = (1,3), in the order A,B,C:")
    for row in Lam.rows(): print("     ", list(row))
    check(Lam == Lam.T, "%s: Lambda is symmetric" % tag)
    check(all(Lam[0, j] == 0 and Lam[j, 0] == 0 for j in range(3)),
          "%s: Lambda vanishes on the base class, as a pairing normalised at b must"
          % tag)
    check(all(e in ZZ for e in (phi*Lam).list()),
          "%s: |Phi| Lambda is integral" % tag)
    # sigma is an automorphism of the model, so it preserves the pairing; it
    # moves the base point, so the identity to check is Lambda^(b) = Lambda^(sb)
    # read through the permutation sigma = (A B)(C).
    sb = part[(1, -3)]
    Lams = lam(sb, [cls[1], cls[0], cls[2]])
    check(Lam == Lams, "%s: sigma-equivariance, Lambda^(b) = Lambda^(sigma b)" % tag)
    # ---- I. Upsilon_3, as far as the model settles it (E104's argument at l=3)
    #  E104's structural facts are l-independent: h_l(A_Z(b,x)) depends on x only
    #  through the component vector of pi_1(x) = [x-b], because pi_2 = Z_* pi_1
    #  plus a constant class and Z acts on component vectors through sigma.  So
    #  h_3 is constant on components, and:
    #    (i) a Q_3-point reduces to a smooth point of a multiplicity-1 component,
    #        which must therefore be defined over F_3;
    #   (ii) sigma-invariance of h_3 (E088) collapses the two that sigma swaps;
    #  (iii) h_3 vanishes on the base class, where pi_1 has component vector 0.
    m1 = [k for k in range(len(comp)) if comp[k][0] == 1]
    m1F3 = []
    for k in m1:
        lb = comp[k][1]
        if lb[0] == 'F':
            m1F3.append(k)                       # X_F-bar is defined over k
        else:
            _, n, c, i = lb
            if edata[n]['roots'][c] in GF(LL): m1F3.append(k)
    print("  multiplicity-1 components: %d geometric, %d defined over F_3"
          % (len(m1), len(m1F3)))
    check(len(m1) == 5 and len(m1F3) == 3,
          "%s: five multiplicity-1 components, three of them over F_3 "
          "(u^4+2 has two roots in F_3 and a conjugate pair in F_9)" % tag)
    check(set(part.values()) == set(m1F3),
          "%s: the nine points hit exactly the F_3-rational multiplicity-1 "
          "components" % tag)
    check(len(set(part.values())) <= 3, "%s: |Upsilon_3| <= 3 (h_3 is constant on "
          "components, and there are three a Q_3-point can meet)" % tag)
    check(len(lab) == 3 and len(moved) == 2,
          "%s: sigma collapses two of the three, so |Upsilon_3| <= 2" % tag)
    zero = [P for P in PTS if part[P] == part[BASE]]
    nz = [P for P in PTS if part[P] not in (part[BASE], part[(1, -3)])]
    check(len(zero) == 3 and len(nz) == 3,
          "%s: the base class carries h_3 = 0" % tag)
    check(set(t for (t, w) in zero + [P for P in PTS if part[P] == part[(1, -3)]])
          == set([1, -2, QQ(-1)/11]) and set(t for (t, w) in nz) == set([-1, 0]),
          "%s: h_3 = 0 exactly on t in {1,-2,-1/11} and is the other value on "
          "t in {-1,0} -- E084's table, from a regular model over Z_3" % tag)
    # E084's semistable model sits over K(pi^{1/e}) with e = lcm_F delta_F (sec. 4)
    e_ss = lcm([F['delta'] for F in M.faces])
    check(e_ss*QQ(1)/8 == Lam[2, 2],
          "%s: e * j_Gamma(R) = %s * 1/8 = %s = Lambda_CC (observation)"
          % (tag, e_ss, e_ss*QQ(1)/8))
    # ---- J. can Lambda pin the VALUE in Upsilon_3?  (E088's constant class)
    #  BDMTV Lemma 3.7 (E088): h(A_Z(b,x)) = B(u,Eu) + B(u,c) with u = AJ_b(x),
    #  E the endomorphism induced by Z, and c = [IA_Z(b)].  E088 determines c
    #  MODULO THE ELLIPTIC LINE as -E(AJ_b(sigma b)).  Work in the component
    #  group, coordinates (gamma,delta) for gamma(e_B-e_A) + delta(e_C-e_A).
    lamZ = -16848                                   # E088, E096, E102: quoted
    Sg = matrix(QQ, [[-1, -1], [0, 1]])             # sigma, columns = images
    check(Sg^2 == 1, "%s: sigma^2 = 1 on component vectors" % tag)
    Zs = lamZ*(1 + 3*Sg)/2                          # E = Z_* = lam (1+3 sigma)/2
    kapp = vector(QQ, [1, 0])                       # AJ_b(sigma b) = [sigma b - b]
    check(Sg*kapp == -kapp, "%s: [sigma b - b] is sigma-anti-invariant" % tag)
    check(Zs*kapp == -lamZ*kapp,
          "%s: E has eigenvalue -lambda_Z on the anti-invariant part" % tag)
    inv = (Sg - 1).right_kernel().basis()
    check(len(inv) == 1 and vector(QQ, inv[0]) == vector(QQ, [1, -2])/gcd([1, 2]) * 1
          or len(inv) == 1,
          "%s: the sigma-invariant line is one-dimensional" % tag)
    ev = vector(QQ, inv[0])
    # a sigma-invariant pairing makes the two eigenspaces orthogonal, so
    # <kappa', ev> = 0, i.e. Lambda_BB = 2 Lambda_BC.  Check it on OUR Lambda and
    # on E104's quoted l = 2 matrix.
    LAM2 = matrix(QQ, [[0,0,0],[0,QQ(1)/2,QQ(1)/4],[0,QQ(1)/4,QQ(7)/8]])   # E104
    for nm, LL2 in (("ours, l=3", Lam), ("E104's, l=2", LAM2)):
        BB = matrix(QQ, [[LL2[1,1], LL2[1,2]], [LL2[2,1], LL2[2,2]]])
        check(kapp*BB*ev == 0,
              "%s: %s -- the sigma-eigenspaces are Lambda-orthogonal, i.e. "
              "Lambda_BB = 2 Lambda_BC" % (tag, nm))
    # h_l(x)/(-log_13 l) as a function of the one remaining unknown mu
    Rm = PolynomialRing(QQ, 'mu'); mu = Rm.gen()
    def hval(LL2, d):
        BB = matrix(Rm, [[LL2[1,1], LL2[1,2]], [LL2[2,1], LL2[2,2]]])
        cc = -Zs*kapp + mu*ev
        dd = vector(Rm, d)
        return dd*BB*(matrix(Rm, Zs)*dd) + dd*BB*cc
    for nm, LL2 in (("ours, l=3", Lam), ("E104's, l=2", LAM2)):
        check(hval(LL2, [1, 0]) == 0,
              "%s: %s -- h_l vanishes on the sigma-image of the base class, "
              "identically in mu (so sigma-invariance pins nothing)" % (tag, nm))
    h3 = hval(Lam, [0, 1]); h2 = hval(LAM2, [0, 1])
    print("  h_l(C)/(-log_13 l) :  l=3 : %s     l=2 : %s" % (h3, h2))
    #  measured (quoted): h_2 = 2106 log_13 2 (E092), h_3 = -4212 log_13 3 (E093)
    mu2 = [r for r in (h2 - (-2106)).roots(multiplicities=False)]
    mu3 = [r for r in (h3 - 4212).roots(multiplicities=False)]
    check(mu2 == [lamZ], "%s: at l=2 the measured h_2 forces mu_2 = lambda_Z "
          "(one equation, one unknown -- no spare information)" % tag)
    check(mu3 == [3*lamZ/2], "%s: at l=3 the measured h_3 corresponds to "
          "mu_3 = (3/2) lambda_Z" % tag)
    check(mu2 != mu3, "%s: mu is a per-prime quantity (the elliptic line's "
          "component vector at l), so l=2 does not calibrate l=3" % tag)
    print("     mu_2 = %s = lambda_Z,   mu_3 = %s = (3/2) lambda_Z  -- v is NOT"
          " determined" % (mu2[0], mu3[0]))
    # ---- K. what the model DOES constrain about the value: a lattice, not a size
    #  Gross's formula on a model whose component group has exponent e puts the
    #  local heights of integral classes in (1/e) Z * log_13(l).  That is a
    #  denominator bound and NOT a numerator bound, so it cannot by itself turn
    #  E093's lindep into a theorem; what it does is (a) give an independent
    #  check the lindep answer must pass, and (b) quantify exactly how crude a
    #  numerator bound would suffice.
    expPhi = lcm([d for d in Mz.elementary_divisors() if d != 0])
    check(expPhi == 4, "%s: exp(Phi_3) = 4 (invariants %s)"
          % (tag, Mz.elementary_divisors()))
    check(all(e in ZZ for e in (expPhi*Lam).list()),
          "%s: exp(Phi_3) * Lambda is integral, so the pairing of integral "
          "classes lies in (1/4) Z" % tag)
    q3, q2, e2 = -4212, -2106, 8            # E093/E092 measured; E103: Phi_2 = Z/8
    check(q3 in QQ and (expPhi*q3) in ZZ,
          "%s: the measured q_3 = h_3/(-log_13 3) = %d lies in (1/4) Z" % (tag, q3))
    check((e2*q2) in ZZ,
          "%s: the measured q_2 = %d lies in (1/8) Z (E103: Phi_2 = Z/8)"
          % (tag, q2))
    #  uniqueness threshold: two elements of (1/e)Z agreeing to p^N differ by at
    #  least p^N/e, so the lindep answer is unique among |q| < p^N/(2e).
    for N, nm in ((6, "certified (E113)"), (10, "observed (E113)")):
        thr = 13^N/(2*expPhi)
        check(abs(q3) < thr,
              "%s: at %s precision p^%d, q_3 is the unique element of (1/4)Z "
              "with |q| < %s matching; |q_3| = %d, headroom %d-fold"
              % (tag, nm, N, thr, abs(q3), floor(thr/abs(q3))))
    print("  the gap between [E] and [T(CAS)] for the value: an a priori bound")
    print("  |q_3| < %s (certified) or < %s (observed), against |q_3| = %d"
          % (13^6/8, 13^10/8, abs(q3)))
    results.append((tag, phi, mine, [c[0] for c in comp], clamped, Lam))

# ---- G. the three charts agree
print("")
print("--- G. the three charts ---")
for tag, phi, mine, mult, cl, Lam in results:
    print("   %-24s |Phi| = %s   multiplicities %s   clamped: %s"
          % (tag, phi, mult, sorted(cl) if cl else "none"))
check(len(set(r[1] for r in results)) == 1,
      "the three charts give the same |Phi|")
check(len(set(frozenset(r[2]) for r in results)) == 1,
      "the three charts give the same partition of the nine points")
check(len(set(str(r[5]) for r in results)) == 1,
      "the three charts give the same local pairing Lambda")
# Every point placed by the free-end reading of Thm 3.13(2) in one chart is
# placed by the exact chain fraction in another, and the answers agree.  That is
# what corroborates the reading, which the theorem does not spell out.
allcl = set().union(*[r[4] for r in results])
check(allcl and all(any(P not in r[4] for r in results) for P in allcl),
      "every clamped point is placed exactly in some other chart (%d points)"
      % len(allcl))

gate("E125")
sys.exit(int(1 if FAIL else 0))
