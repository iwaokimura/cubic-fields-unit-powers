## check-dv-paper-examples.sage --- E125 addendum: our implementation of
## Dokchitser's construction, against the paper's OWN worked examples.
##
## check-c4-dv3.sage builds a regular model of C_4 over Z_3 from
##     T. Dokchitser, Models of curves over discrete valuation rings,
##     Duke Math. J. 170 (2021) 2519-2574   [implemented from arXiv:1807.00025v2]
## and its internal checks (delta_F two ways, delta_L d_0 = delta_F1, M m = 0,
## |det M^(i)| = |Phi| m_i^2, Thm 6.1, three charts agreeing) test the
## implementation against ITSELF.  This script tests it against the PAPER: every
## example in v2 that states a number is recomputed here.  If our reading of
## Defs 3.1-3.9 were wrong, these would not come out.
##
## The examples, and what each pins down:
##
##   Ex 3.6   y^2 - x^3 - pi          one v-face, delta_F = 6, and the reduction
##                                    f|F = y - x - 1  -- pins Def 3.4/3.5
##   Intro    y^2 + pi x^3 y + x^3 + pi^5
##                                    delta_F = 6,3; five v-edges, 4 outer and 1
##                                    inner; genus 2; Delta_v-regular for ANY k
##   Ex 3.3   y^3+pi^2x^2y^2+y^2+pi^3x^6+pi x^3+pi^3
##                                    delta_F = 3,3,6; delta_L = 1,1,1,2,3,3,3;
##                                    five v-vertices (the pi^2x^2y^2 term is not
##                                    one); genus 4; and by Ex 3.10 it is
##                                    Delta_v-regular IFF char k != 3 -- the one
##                                    example with a characteristic-dependent
##                                    answer, so it tests the smoothness test
##   Sec 10   (x-y+1)^p + y^p = 1 over Z_p
##                                    the five monomials x^p, px, -py, -py^{p-1},
##                                    -pxy^{p-1} are the vertices of Delta_v;
##                                    genus (p-1)(p-2)/2; regularity is automatic
##                                    except at the leftmost v-edge, where
##                                    f|L = (1/p)[(1-y)^p + y^p - 1]; and the
##                                    multiple roots of that are all double and
##                                    F_p-rational
##
## Run:  sage check-dv-paper-examples.sage      (about a minute)

import sys
load('dv-model-lib.sage')

def data(f, l):
    M = Model(f, l)
    ok, why = M.is_regular()
    return M, ok, why, \
        sorted(F['delta'] for F in M.faces), sorted(E['delta'] for E in M.edges), \
        sum(1 for E in M.edges if len(E['adj']) == 2), \
        len([1 for q in M.Delta.integral_points()
             if M.Delta.interior_contains(vector(QQ, q))])

def norm1(g):
    """a one-variable reduced restriction, normalised: strip u-powers, make monic"""
    u = g.parent().gen(0)
    while g % u == 0: g //= u
    return g/g.leading_coefficient()

print("=== check-dv-paper-examples.sage --- E125 addendum ===")
print("    our implementation against arXiv:1807.00025v2's own examples")

print("")
print("--- Example 3.6:  f = y^2 - x^3 - pi ---")
for l in (5, 7, 11):
    M, ok, why, dF, dL, inn, g = data(y^2 - x^3 - l, l)
    check(dF == [6], "Ex 3.6 (l=%d): one v-face with delta_F = 6, got %s" % (l, dF))
    check(ok, "Ex 3.6 (l=%d): Delta_v-regular" % l)
    r = M.faces[0]['red']['poly']
    # Def 3.4: the restriction is defined up to GL_2(Z) and monomials, so what
    # is pinned is that it is a linear form in three terms with unit coefficients
    check(r.total_degree() == 1 and len(r.monomials()) == 3,
          "Ex 3.6 (l=%d): f|F is a linear trinomial (paper: y - x - 1), got %s" % (l, r))
    print("   l=%-3d delta_F=%s  f|F = %s" % (l, dF, r))

print("")
print("--- Introduction:  y^2 + pi x^3 y + x^3 + pi^5 ---")
for l in (5, 7, 11, 13):
    M, ok, why, dF, dL, inn, g = data(y^2 + l*x^3*y + x^3 + l^5, l)
    check(dF == [3, 6], "Intro (l=%d): delta_F = 6, 3; got %s" % (l, dF))
    check(len(dL) == 5 and inn == 1,
          "Intro (l=%d): five v-edges, four outer and one inner; got %d, %d inner"
          % (l, len(dL), inn))
    check(g == 2, "Intro (l=%d): genus 2 = |Delta(Z)|; got %s" % (l, g))
    check(ok, "Intro (l=%d): Delta_v-regular (paper: for any ground field K)" % l)
    print("   l=%-3d delta_F=%s delta_L=%s (%d inner) g=%s regular=%s"
          % (l, dF, dL, inn, g, ok))

print("")
print("--- Example 3.3 + Example 3.10 ---")
for l in (5, 7, 11, 13, 3):
    f = y^3 + l^2*x^2*y^2 + y^2 + l^3*x^6 + l*x^3 + l^3
    M, ok, why, dF, dL, inn, g = data(f, l)
    check(dF == [3, 3, 6], "Ex 3.3 (l=%d): delta_F = 3,3,6; got %s" % (l, dF))
    check(dL == [1, 1, 1, 2, 3, 3, 3],
          "Ex 3.3 (l=%d): delta_L = 1,1,1,2,3,3,3; got %s" % (l, dL))
    check(len(M.P3.vertices()) == 5,
          "Ex 3.3 (l=%d): five v-vertices (pi^2x^2y^2 is not one); got %d"
          % (l, len(M.P3.vertices())))
    check(g == 4, "Ex 3.3 (l=%d): genus 4 = |Delta(Z)|; got %s" % (l, g))
    check(ok == (l != 3),
          "Ex 3.10 (l=%d): Delta_v-regular iff char k != 3; got %s" % (l, ok))
    print("   l=%-3d delta_F=%s delta_L=%s vert=%d g=%s regular=%s %s"
          % (l, dF, dL, len(M.P3.vertices()), g, ok, "" if ok else why))

print("")
print("--- Section 10: Fermat curves (x-y+1)^p + y^p = 1 over Z_p ---")
for p in (3, 5, 7, 11, 13, 17):
    f = (x - y + 1)^p + y^p - 1
    M, ok, why, dF, dL, inn, g = data(f, p)
    vert = set((v[0], v[1]) for v in M.P3.vertices())
    five = set([(p,0), (1,0), (0,1), (0,p-1), (1,p-1)])
    check(vert == five,
          "Fermat p=%d: the vertices of Delta_v are the paper's five monomials "
          "x^p, px, -py, -py^{p-1}, -pxy^{p-1}; got %s" % (p, sorted(vert)))
    check(g == (p-1)*(p-2)/2,
          "Fermat p=%d: |Delta(Z)| = (p-1)(p-2)/2 = %d (Baker); got %s"
          % (p, (p-1)*(p-2)/2, g))
    # the paper's f|L at the leftmost edge
    RZ = PolynomialRing(ZZ, 'Y'); YZ = RZ.gen()
    fb = PolynomialRing(GF(p), 'Y')(((1 - YZ)^p + YZ^p - 1)/p)
    rho = len([1 for h, e in fb.factor() if e > 1])
    check(all(e == 2 and h.degree() == 1 for h, e in fb.factor() if e > 1),
          "Fermat p=%d: every multiple root of (1/p)[(1-y)^p+y^p-1] is double and "
          "F_p-rational" % p)
    # which edges are non-smooth
    bad = []
    for E in M.edges:
        if E['red'] is None: continue
        gg = E['red']['poly']; u = gg.parent().gen(0)
        while gg % u == 0: gg //= u
        if gg.degree() >= 1 and gcd(gg, gg.derivative()).degree() > 0:
            bad.append(E)
    check(len(bad) <= 1, "Fermat p=%d: at most one non-smooth v-edge; got %d"
          % (p, len(bad)))
    check(ok == (rho == 0),
          "Fermat p=%d: Delta_v-regular iff (1/p)[(1-y)^p+y^p-1] is squarefree "
          "(rho = %d); got %s" % (p, rho, ok))
    if bad:
        check(set([bad[0]['p'], bad[0]['q']]) == set([(0,1), (0,p-1)]),
              "Fermat p=%d: the non-smooth edge is the LEFTMOST one, (0,1)-(0,p-1); "
              "got %s-%s" % (p, bad[0]['p'], bad[0]['q']))
    # and the restriction there IS the paper's polynomial
    L = bad[0] if bad else [E for E in M.edges
                            if set([E['p'], E['q']]) == set([(0,1), (0,p-1)])][0]
    mine = norm1(L['red']['poly'])
    theirs = norm1(PolynomialRing(GF(p), 'u')(list(fb)))
    rev = norm1(PolynomialRing(GF(p), 'u')(list(reversed(list(theirs)))))
    check(mine == theirs or mine == rev,
          "Fermat p=%d: f|L at the leftmost edge equals (1/p)[(1-y)^p+y^p-1] up to "
          "the monomial/GL_1(Z) ambiguity of Def 3.4; got %s vs %s"
          % (p, mine, theirs))
    print("   p=%-3d vertices ok, g=%-4s rho=%d regular=%s  f|L = %s"
          % (p, g, rho, ok, mine))

gate("E125-examples")
sys.exit(int(1 if FAIL else 0))
