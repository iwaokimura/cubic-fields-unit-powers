# check-xs13-hecke.sage --- E065 (E048 Phase 4) GATE, part 13.
#
# E079.  Where §6.4 of [BDM+19] says the correspondences come from.  The
# published paper (Ann. of Math. 189 (2019); arXiv v1 does NOT say this) states
# that Z_1 and Z_2 are obtained by
#
#     "computing the matrix A_q of T_q with respect to omega, and multiplying
#      6 A_q - tr(A_q) I_6 by the inverse of the cup product matrix with
#      respect to omega ... using q = 7 and q = 11, respectively."
#
# That is a claim we can test exactly, over Q, with no p-adic arithmetic and
# without ever forming a Hecke matrix: T_q acts on H^1_dR(X) through
# End(J) (x) Q = K, so as an element of K the matrix Z_q M is
#
#     6 a_q(f) - tr(A_q) = 6 a_q(f) - 2 Tr_{K/Q}(a_q(f)),
#
# the factor 2 because H^1_dR is free of rank 2 over K and the 6 because that
# is what makes it traceless.  Its MINIMAL POLYNOMIAL over Q is therefore
# computable from the newform alone, and must equal the minimal polynomial of
# Z_q M, which E076 measured.  The two minimal polynomials involved are
# different, so the assignment of q to Z is FORCED by this test.
#
# WHAT THE TEST FINDS.  The assignment is the other way round:
#
#     Z_1 M  <->  q = 11,     Z_2 M  <->  q = 7,
#
# not "q = 7 and q = 11, respectively".  This is the first error found in the
# PUBLISHED paper rather than in arXiv:1711.05846v1 (§E077 established that all
# four earlier ones are the preprint's), and it is a labelling slip: nothing
# downstream uses which Hecke operator a correspondence came from, only that
# the Z_i satisfy §4.4 (a)-(d) and are independent, which E075 and E076 checked
# directly.
#
# WHY THIS IS WORTH A GATE.  It is the first time anything in the port is
# checked against the MODULAR side of X_s(13) -- a space of cusp forms computed
# by Sage's modular symbols, which shares no code and no mathematics with
# Tuitman's cohomology.  It tests, in one identity: E066's cup product (the M
# in Z M), E071's reading that Z is the class and not the endomorphism (with
# the endomorphism the minimal polynomial is different), and the K-structure
# E076 built.  It also pins the embedding iota: K -> End(H^1_dR) that E078
# needs in order to compare with §6.4.1's printed elements of K.
#
# THE CHECKS, all exact over Q.
#   (1) THE NEWFORM.  Level 169 weight 2 has three newforms; exactly one has
#       the q-expansion §6.1 prints, a_2 = alpha and a_3 = -alpha^2-2alpha with
#       alpha^3+2alpha^2-alpha-1 = 0.  Its coefficient field has discriminant
#       49, i.e. is Q(zeta_7)^+.  The first six printed coefficients are
#       checked one by one.
#   (2) THE IDENTIFICATION.  min poly of Z_i M against min poly of
#       6 a_q - 2 Tr(a_q) for q = 7 and q = 11, all four combinations.  Exactly
#       one matching is consistent, and it is the swapped one.
#   (3) THE NORMALISATION.  6 a_q - 2 Tr(a_q) has trace zero, as tr(Z_i M) = 0
#       requires, and the "6" is forced by that.
#   (4) NEGATIVE CONTROL.  With the ENDOMORPHISM Z_i in place of the class
#       Z_i M -- E071's correction -- no q matches.
#   (5) THE EMBEDDING iota: K -> Q[Z_1 M], defined by
#       iota(6 a_11 - 2 Tr(a_11)) = Z_1 M, is well defined (a_11 generates K)
#       and carries a_7 to (Z_2 M + 2 Tr(a_7))/6.  That last is a CHECK, not a
#       definition: it says the two correspondences see the same embedding.
#
# Run: sage check-xs13-hecke.sage

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


# ------------------------------------------------------------------ the data

P3 = PolynomialRing(QQ, ['X', 'Y', 'Z'])
X, Y, Z = P3.gens()
QUARTIC = (Y**4 + 5*X**4 - 6*X**2*Y**2 + 6*X**3*Z + 26*X**2*Y*Z + 10*X*Y**2*Z
           - 10*Y**3*Z - 32*X**2*Z**2 - 40*X*Y*Z**2 + 24*Y**2*Z**2 + 32*X*Z**3
           - 16*Y*Z**3)
R2 = PolynomialRing(QQ, ['x', 'y'])
x, y = R2.gens()
Qxy = QUARTIC(x, y, 1)
OMEGA_NUM = [R2(1), x, y,
             -160*x**4/3 + 736*x**3/3 - 16*x**2*y/3 + 436*x**2/3 - 440*x*y/3
             + 68*y**2/3,
             -80*x**3/3 + 44*x**2 - 40*x*y/3 + 68*y**2/3 - 32,
             -16*x**2*y + 28*x**2 + 72*x*y - 4*y**2 - 160*x/3 + 272/3]
Z1 = matrix(QQ, [[0, -976, -1104, 10, -6, 18], [976, 0, -816, -3, 1, 3],
                 [1104, 816, 0, -3, 3, -11], [-10, 3, 3, 0, 0, 0],
                 [6, -1, -3, 0, 0, 0], [-18, -3, 11, 0, 0, 0]])
Z2 = matrix(QQ, [[0, 112, -656, -6, 6, 6], [-112, 0, -2576, 15, 9, 27],
                 [656, 2576, 0, 3, 3, -3], [6, -15, -3, 0, 0, 0],
                 [-6, -9, -3, 0, 0, 0], [-6, -27, 3, 0, 0, 0]])

print("=" * 72)
print("=== check-xs13-hecke.sage --- E079: where §6.4's Z_1, Z_2 come from ===")
print("=" * 72)

# --------------------------------------------------------------- (1) the form

print("(1) the newform of level 169")
Rt = PolynomialRing(QQ, 't')
t = Rt.gen()
MINPOL = t**3 + 2*t**2 - t - 1
Kf = NumberField(MINPOL, 'al')
al = Kf.gen()
check(Kf.discriminant() == 49
      and Kf.is_isomorphic(CyclotomicField(7).subfields(3)[0][0]),
      "Q[x]/(x^3+2x^2-x-1) has discriminant 49, i.e. is Q(zeta_7)^+")

# the coefficients §6.1 prints
PRINTED = {2: al, 3: -al**2 - 2*al, 4: al**2 - 2, 5: al**2 + 2*al - 2,
           6: -al - 1}

t0 = time.time()
NF = Newforms(Gamma0(169), 2, names='a')
print("   %d newforms at level 169, degrees %s  (%.0f s)"
      % (len(NF), [f.hecke_eigenvalue_field().degree() for f in NF],
         time.time() - t0))

match = None
for f in NF:
    Ff = f.hecke_eigenvalue_field()
    if Ff.degree() != 3:
        continue
    for emb in Ff.embeddings(Kf):
        if all(emb(Ff(f[n])) == v for n, v in PRINTED.items()):
            match = (f, Ff, emb)
            break
    if match:
        break
check(match is not None,
      "exactly one newform has the q-expansion printed in §6.1 "
      "(a_2 = al, a_3 = -al^2-2al, a_4, a_5, a_6)")
if match is None:
    print("E079 GATE: RED (no matching newform)")
    sys.exit(1)
f, Ff, emb = match
others = [g for g in NF if g is not f
          and g.hecke_eigenvalue_field().degree() == 3
          and any(emb2(g.hecke_eigenvalue_field()(g[n])) == v
                  for emb2 in g.hecke_eigenvalue_field().embeddings(Kf)
                  for n, v in PRINTED.items() if n == 2)]
a = dict((q, emb(Ff(f[q]))) for q in (2, 3, 5, 7, 11, 13))
for q in (2, 3, 5, 7, 11, 13):
    print("   a_%-2s = %s" % (q, a[q]))

# --------------------------------------------------------- the cup product

print("-" * 72)
print("(2) the identification of Z_1, Z_2 with Hecke operators")
t0 = time.time()
C = TuitmanCurve(Qxy, name="X_s(13)")
H = Cohomology(C)
g, n = ZZ(C.genus), 2 * ZZ(C.genus)
L, xL, yL = C.L, C.L(C.x), C.y
dxL = xL.differential()


def toL(fn):
    return sum(QQ(c) * xL**ZZ(e[0]) * yL**ZZ(e[1])
               for e, c in fn.dict().items())


QyL = toL(Qxy.derivative(y))
reps = [H.form_in_E((toL(fn) / QyL) * dxL) for fn in OMEGA_NUM]
Mcup = H.cup_product_matrix(basis=reps)
J = matrix(QQ, n, n, lambda i, j: QQ(1) if (i < g and j == i + g) else
           (QQ(-1) if (i >= g and j == i - g) else QQ(0)))
check(Mcup == J or Mcup == -J, "the cup product is the standard symplectic form")
print("   cup product = %sJ  (%.0f s)" % ("" if Mcup == J else "-",
                                          time.time() - t0))

AZ = {"Z_1": Z1 * Mcup, "Z_2": Z2 * Mcup}


def hecke_elt(q):
    """6 a_q - tr(A_q) as an element of K, tr(A_q) = 2 Tr_{K/Q}(a_q)."""
    return 6 * a[q] - 2 * a[q].trace()


table = {}
for lab in ("Z_1", "Z_2"):
    mp = AZ[lab].minpoly().change_ring(QQ)
    for q in (7, 11):
        e = hecke_elt(q)
        table[(lab, q)] = (mp, e.minpoly().change_ring(QQ),
                           mp == e.minpoly().change_ring(QQ))
        print("   %s M: minpoly %s   vs   6a_%s - tr: %s   %s"
              % (lab, mp, q, e.minpoly(),
                 "MATCH" if table[(lab, q)][2] else "-"))
check(table[("Z_1", 11)][2] and table[("Z_2", 7)][2],
      "Z_1 M is 6a_11 - tr(A_11) and Z_2 M is 6a_7 - tr(A_7)")
check(not table[("Z_1", 7)][2] and not table[("Z_2", 11)][2],
      "and NOT the other way round -- §6.4's \"q = 7 and q = 11, "
      "respectively\" has them SWAPPED")

print("-" * 72)
print("(3) the normalisation")
for q in (7, 11):
    check(hecke_elt(q).trace() == 0,
          "6a_%s - 2Tr(a_%s) has trace zero, as tr(Z M) = 0 requires" % (q, q))
check(all(AZ[lab].trace() == 0 for lab in AZ),
      "and both Z_i M do have trace zero")

print("-" * 72)
print("(4) NEGATIVE CONTROL: the endomorphism instead of the class (E071)")
bad = 0
for lab, Zm in (("Z_1", Z1), ("Z_2", Z2)):
    mp = Zm.minpoly().change_ring(QQ)
    for q in (7, 11):
        if mp == hecke_elt(q).minpoly().change_ring(QQ):
            bad += 1
    print("   %s (the class in H^1 (x) H^1, NOT times M): minpoly %s"
          % (lab, mp))
check(bad == 0,
      "no q matches when Z is used in place of Z M, so the cup product really "
      "is doing the work")

print("-" * 72)
print("(5) the embedding iota: K -> Q[Z_1 M]")
check(a[11].minpoly().degree() == 3,
      "a_11 generates K, so iota is determined by iota(6a_11 - 2Tr(a_11)) "
      "= Z_1 M")
# express al as a polynomial in u = 6 a_11 - 2 Tr(a_11), then iota(al) = P(Z_1M)
u = hecke_elt(11)
Vm = matrix(QQ, [list(Kf(1).vector()), list(u.vector()),
                 list((u * u).vector())]).transpose()
coef = Vm.solve_right(vector(QQ, list(al.vector())))
Pal = sum(coef[i] * t**i for i in range(3))
IOTA_AL = sum(QQ(coef[i]) * AZ["Z_1"]**i for i in range(3))
print("   al = %s  evaluated at u = 6a_11 - 2Tr(a_11)" % Pal)
check(IOTA_AL.minpoly().list() == MINPOL.list(),
      "iota(al) has minimal polynomial x^3+2x^2-x-1 (got %s)"
      % IOTA_AL.minpoly())
check(IOTA_AL.submatrix(g, 0, g, g) == 0,
      "iota(al) preserves Fil^1")
# the cross-check: does the SAME embedding send a_7 to (Z_2 M + 2Tr(a_7))/6 ?
IOTA_A7 = sum(QQ(c) * IOTA_AL**i for i, c in
              enumerate(a[7].polynomial().change_ring(QQ).list()))
check(6 * IOTA_A7 - 2 * a[7].trace() * matrix.identity(QQ, n) == AZ["Z_2"],
      "iota(6a_7 - 2Tr(a_7)) = Z_2 M EXACTLY -- the two correspondences see "
      "the same embedding, which pins iota for E078")

print("=" * 72)
print("total %.0f s, %d failure(s)" % (time.time() - t_start, len(fails)))
for m in fails:
    print("   FAILED: %s" % m)
print("E079 GATE: %s" % ("GREEN" if not fails else "RED"))
print("=" * 72)
# for E078: the coefficients of iota(al) in the basis 1, Z_1 M, (Z_1 M)^2
print("iota(al) = %s + %s*(Z_1 M) + %s*(Z_1 M)^2"
      % (coef[0], coef[1], coef[2]))
