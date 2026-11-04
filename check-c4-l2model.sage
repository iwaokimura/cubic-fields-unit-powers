# check-c4-l2model.sage -- E128, the production gate.
#
# A regular model of C_4 over Z_2 built with Q. Liu's desingularization
# algorithm for double covers of regular surfaces (arXiv:2504.16808v3),
# by running the algorithm twice:
#
#     P^1_{Z_2}  <--2--  cE  <--2--  cC_4 ,
#
# the first round resolving the Weierstrass model of E: u^2 - 6(t-1)^2 u
# + 27t(t^3-4) = 0 over P^1_t, the second the double cover w^2 = u of the
# regular model cE that the first round produces.
#
# Groups:
#   (C) round 1 at ell = 2 and 3 against PARI/Sage's Tate algorithm;
#   (E) round 2 at ell = 2: components, multiplicities, Phi, and the fibre
#       genus from the geometric genera (g - sum m_i delta_i: M right and
#       every component regular);
#   (F) the contraction of the two (-1)-curves against Magma's model
#       (report of section E103), matrix and multiplicities;
#   (G) the reduction of the nine rational points, to the point and not only
#       to the component (what section E127 Addendum 3 needed);
#   (H) the local intersection pairing Lambda_2 of section E104;
#   (I) the independent checks on M: SNF, |det M^(i)| = |Phi| m_i^2.
#
# E129 replaced the degree-<=2 search for singular points by an exact finite
# candidate set (Section 5.2 at the generic point of each component), so this
# gate now runs with the heuristic switched off.  The numbers are unchanged;
# check-liu-exact-search.sage is where that is checked.
#
# No Magma is run.  Magma's recorded output is used only as an answer key.
import sys
# Run from the directory that holds liu-model-lib.sage (the repository
# root); see the README.
load("liu-model-lib.sage")

NPASS = 0
NFAIL = 0
FAILS = []


def check(name, got, want=None, cond=None):
    global NPASS, NFAIL
    ok = (got == want) if cond is None else cond
    if ok:
        NPASS += 1
        print("  PASS  %-58s %s" % (name, got))
    else:
        NFAIL += 1
        FAILS.append(name)
        print("  FAIL  %-58s got %s want %s" % (name, got, want))
    sys.stdout.flush()


# --- the curve and its nine rational points --------------------------------
# C_4 : w^4 - 6(t-1)^2 w^2 + 27 t (t^3-4) = 0,  genus 3, Aut = Z/2 (sigma: w -> -w)
# E   : u^2 - 6(t-1)^2 u + 27 t (t^3-4) = 0,    u = w^2
PTS = [("(1,3)", 1, 3), ("(1,-3)", 1, -3),
       ("(-1,3)", -1, 3), ("(-1,-3)", -1, -3),
       ("(-2,6)", -2, 6), ("(-2,-6)", -2, -6),
       ("(-1/11,15/11)", QQ(-1) / 11, QQ(15) / 11),
       ("(-1/11,-15/11)", QQ(-1) / 11, QQ(-15) / 11),
       ("(0,0)", 0, 0)]
SIGMA = {"(1,3)": "(1,-3)", "(1,-3)": "(1,3)", "(-1,3)": "(-1,-3)",
         "(-1,-3)": "(-1,3)", "(-2,6)": "(-2,-6)", "(-2,-6)": "(-2,6)",
         "(-1/11,15/11)": "(-1/11,-15/11)", "(-1/11,-15/11)": "(-1/11,15/11)",
         "(0,0)": "(0,0)"}


def build(ell, P=10, sections=True):
    B = LiuBase(ell)
    Rs = PolynomialRing(B.O, 's')
    t = Rs.gen()
    secs = [(nm, t0, w0 ** 2, w0) for (nm, t0, w0) in PTS] if sections else []
    # E129: the points to visit are now an exact finite set -- Section 5.2
    # at the generic point of every component of the closed fibre, for the
    # cover of the next round, together with the zeros of the discriminant
    # along each component.  The degree heuristic of E128 (all_rational with
    # point_degree = 2) is off; check-liu-exact-search.sage shows that the two
    # give the same model.
    LC = LineCover(B, -6 * (t - 1) ** 2, 27 * t * (t ** 3 - 4), 1,
                   sections=secs, all_rational=False, next_cover=True)
    return LC, LC.resolution()


print("=" * 74)
print("E128 gate: a regular model of C_4 over Z_2 by Liu's algorithm")
print("=" * 74)

# ---------------------------------------------------------------------------
print("\n(A) the plane models and the nine points")
# ---------------------------------------------------------------------------
Rt = PolynomialRing(QQ, 't,w')
tv, wv = Rt.gens()
F4 = wv ** 4 - 6 * (tv - 1) ** 2 * wv ** 2 + 27 * tv * (tv ** 3 - 4)
check("all nine points lie on C_4",
      all(F4(t0, w0) == 0 for (_, t0, w0) in PTS), True)
check("C_4 -> E is w |-> u = w^2",
      (wv ** 2) ** 2 - 6 * (tv - 1) ** 2 * wv ** 2 + 27 * tv * (tv ** 3 - 4) == F4,
      True)
EQ = EllipticCurve([0, 216, 0, -31104, -2985984]).minimal_model()
check("Jac of u^2-6(t-1)^2u+27t(t^3-4) is y^2=x^3-36x",
      EQ.is_isomorphic(EllipticCurve([0, 0, 0, -36, 0])), True)

# ---------------------------------------------------------------------------
print("\n(C) round 1: the regular model of E, against Tate's algorithm")
# ---------------------------------------------------------------------------
ROUND1 = {}
for ell, kod, tam, phi, mults in [(2, 'I2*', 4, [2, 2], [1, 1, 1, 1, 2, 2, 2]),
                                  (3, 'I0*', 4, [2, 2], [1, 1, 1, 1, 2])]:
    LC, res1 = build(ell)
    ROUND1[ell] = (LC, res1)
    comps1, Ms1, good1 = analyse(res1)
    check("ell=%s: exactly one intersection matrix" % ell, len(good1), 1)
    choice, M1, mu1, gen1, cps1, rep1 = good1[0]
    ld = EQ.local_data(ell)
    check("ell=%s: Kodaira symbol (Tate)" % ell, str(ld.kodaira_symbol()), kod)
    check("ell=%s: Tamagawa number (Tate)" % ell, ld.tamagawa_number(), tam)
    check("ell=%s: multiplicities of the closed fibre" % ell, sorted(mu1), mults)
    check("ell=%s: Phi(E) from our model" % ell, rep1['Phi'], phi)
    check("ell=%s: all components are rational curves" % ell, gen1,
          [0] * len(gen1))
    check("ell=%s: fibre genus (geometric genera) = g(E) = 1" % ell,
          genus_of_fibre(M1, mu1, gen1), 1)
    check("ell=%s: M symmetric, M m = 0, ker = Q m, negative semidefinite" % ell,
          [rep1['symmetric'], rep1['Mm'], rep1['kernel_is_m'],
           rep1['neg_semidef']], [True] * 4)
    check("ell=%s: |det M^(i)| = |Phi| m_i^2 for every i" % ell,
          rep1['minor_test'], True)
    check("ell=%s: the model is already minimal" % ell,
          len(contract_minus_ones(M1, mu1, gen1, cps1)[4]), 0)

# ---------------------------------------------------------------------------
print("\n(E) round 2 at ell = 2: the closed fibre of C_4")
# ---------------------------------------------------------------------------
LC2, res1 = ROUND1[2]
res2, lab2, eps2 = round2(res1, P=10)
comps2, Ms2, good2 = analyse(res2, P=10)
check("exactly one intersection matrix", len(good2), 1)
choice, M2, mu2, gen2, cps2, rep2 = good2[0]
check("number of components of the closed fibre", len(cps2), 8)
check("multiplicities", sorted(mu2), [1, 1, 1, 2, 2, 2, 2, 4])
check("three components of multiplicity 1",
      len([m for m in mu2 if m == 1]), 3)
check("all components are rational curves", gen2, [0] * len(gen2))
check("fibre genus (geometric genera) = g(C_4) = 3",
      genus_of_fibre(M2, mu2, gen2), 3)
check("component group Phi_2", rep2['Phi'], [8])
check("M symmetric, M m = 0, ker = Q m, negative semidefinite",
      [rep2['symmetric'], rep2['Mm'], rep2['kernel_is_m'], rep2['neg_semidef']],
      [True] * 4)

# ---------------------------------------------------------------------------
print("\n(F) the contraction, against Magma's model (section E103)")
# ---------------------------------------------------------------------------
MAGMA_M = matrix(ZZ, [[-3, 1, 0, 1, 0, 0],
                      [1, -3, 0, 1, 0, 0],
                      [0, 0, -4, 0, 2, 0],
                      [1, 1, 0, -3, 0, 1],
                      [0, 0, 2, 0, -3, 1],
                      [0, 0, 0, 1, 1, -1]])
MAGMA_MULT = [1, 1, 1, 2, 2, 4]
minus1 = [i for i in range(len(mu2)) if M2[i, i] == -1]
check("components with self-intersection -1", sorted([mu2[i] for i in minus1]),
      [2, 2, 4])
# contract the two (-1)-curves of multiplicity 2 (Castelnuovo); the third,
# of multiplicity 4, is the one Magma's model keeps
Mc, muc, genc, labc = M2, list(mu2), list(gen2), list(cps2)
for _ in range(2):
    pick = [i for i in range(Mc.nrows()) if Mc[i, i] == -1 and muc[i] == 2]
    keep = [j for j in range(Mc.nrows()) if j != pick[0]]
    N = matrix(ZZ, len(keep), len(keep))
    for x, j in enumerate(keep):
        for y, kk in enumerate(keep):
            N[x, y] = Mc[j, kk] + Mc[j, pick[0]] * Mc[pick[0], kk]
    Mc = N
    muc = [muc[j] for j in keep]
    genc = [genc[j] for j in keep]
    labc = [labc[j] for j in keep]
check("after contracting the two (-1)-curves: number of components",
      Mc.nrows(), 6)
check("after contracting: multiplicities", sorted(muc), MAGMA_MULT)
repc = fibre_report(Mc, vector(ZZ, muc))
check("after contracting: Phi", repc['Phi'], [8])
found = None
from itertools import permutations
for pm in permutations(range(6)):
    if [muc[pm[i]] for i in range(6)] != MAGMA_MULT:
        continue
    if all(Mc[pm[i], pm[j]] == MAGMA_M[i, j] for i in range(6) for j in range(6)):
        found = pm
        break
check("the contracted matrix equals Magma's, up to relabelling",
      found is not None, True)
print("        permutation (Magma index -> ours):", found)

# ---------------------------------------------------------------------------
print("\n(G) the nine rational points")
# ---------------------------------------------------------------------------
pc = point_components(res2, cps2)
check("every point reduces to a multiplicity-1 component",
      sorted(set(pc[nm]['mult'] for (nm, _, _) in PTS)), [1])
classes = {}
for (nm, _, _) in PTS:
    classes.setdefault(pc[nm]['comp'], []).append(nm)
check("the nine points meet exactly three components", len(classes), 3)
part = sorted(sorted(v) for v in classes.values())
E104 = sorted([sorted(["(1,3)", "(-1,3)", "(-1/11,-15/11)"]),
               sorted(["(1,-3)", "(-1,-3)", "(-1/11,15/11)"]),
               sorted(["(-2,6)", "(-2,-6)", "(0,0)"])])
check("the partition is section E104's / E127(r)'s", part, E104)
same = {}
for (nm, _, _) in PTS:
    key = (pc[nm]['node'], pc[nm]['red'])
    same.setdefault(key, []).append(nm)
sep = {}
for (nm, _, _) in PTS:
    s = SIGMA[nm]
    if nm == s:
        continue
    sep[nm] = (pc[nm]['node'], pc[nm]['red']) != (pc[s]['node'], pc[s]['red'])
check("sigma separates the pair over t = 1", sep["(1,3)"], True)
check("sigma separates the pair over t = -1", sep["(-1,3)"], True)
check("sigma separates the pair over t = -1/11", sep["(-1/11,15/11)"], True)
check("sigma does NOT separate the pair over t = -2 (E127 Add.3(p))",
      sep["(-2,6)"], False)
check("(0,0) is sigma-fixed and lies with the t=-2 pair",
      pc["(0,0)"]['comp'] == pc["(-2,6)"]['comp'], True)

# ---------------------------------------------------------------------------
print("\n(H) the local pairing Lambda_2 of section E104")
# ---------------------------------------------------------------------------
base = pc["(1,3)"]['comp']
others = sorted(set(pc[nm]['comp'] for (nm, _, _) in PTS) - {base})
order = [base] + others
L = local_pairing(M2, mu2, order, base)
E104_L = matrix(QQ, [[0, 0, 0], [0, QQ(1) / 2, QQ(1) / 4],
                     [0, QQ(1) / 4, QQ(7) / 8]])
check("Lambda_2 (base = the component of (1,3))", L, E104_L)
check("Lambda_2 is symmetric", L == L.transpose(), True)
check("|Phi| * Lambda_2 is integral",
      all((8 * c).is_integer() for c in L.list()), True)
Lb = local_pairing(M2, mu2, [pc["(1,-3)"]['comp']] +
                   [c for c in order if c != pc["(1,-3)"]['comp']],
                   pc["(1,-3)"]['comp'])
check("Lambda_2 is sigma-equivariant (recomputed at sigma b)", Lb, E104_L)

# ---------------------------------------------------------------------------
print("\n(D) the cross-check at ell = 3, against section E125")
# ---------------------------------------------------------------------------
# Section E125 built a regular model of C_4 over Z_3 by a completely different
# construction (Dokchitser's Newton polytopes).  It reports |Phi_3| = 16, the
# A/B/C partition of the nine points, and Lambda_3.  Those are what the two
# constructions can be compared on.  We work over W(F_9), the unramified
# quadratic extension of Z_3: base change does not alter the model, and it
# makes the components geometrically irreducible, which is the setting E125
# computes in.
Zt = PolynomialRing(QQ, 'th')
B3 = LiuBase(3, Zt.gen() ** 2 + 1)
Rs3 = PolynomialRing(B3.O, 's')
t3 = Rs3.gen()
LC3 = LineCover(B3, -6 * (t3 - 1) ** 2, 27 * t3 * (t3 ** 3 - 4), 1,
                sections=[(nm, t0, w0 ** 2, w0) for (nm, t0, w0) in PTS],
                all_rational=False, next_cover=True)
res13 = LC3.resolution()
c13, Ms13, g13 = analyse(res13)
check("ell=3 over W(F_9): round 1 is still I_0*",
      [len(c13), sorted(g13[0][2]), g13[0][5]['Phi'],
       genus_of_fibre(g13[0][1], g13[0][2], g13[0][3])],
      [5, [1, 1, 1, 1, 2], [2, 2], 1])
res23, lab3, eps3 = round2(res13, P=12)
comps3, Ms3, good3 = analyse(res23, P=12)
check("ell=3: exactly one intersection matrix", len(good3), 1)
ch3, M3, mu3, gen3, cps3, rep3 = good3[0]
check("ell=3: number of components", len(cps3), 7)
check("ell=3: multiplicities", sorted(mu3), [1, 1, 1, 1, 1, 2, 2])
check("ell=3: all components are rational curves", gen3, [0] * len(gen3))
check("ell=3: fibre genus (geometric genera) = g(C_4) = 3",
      genus_of_fibre(M3, mu3, gen3), 3)
check("ell=3: Phi_3 (section E125: Z/2 x Z/2 x Z/4, order 16)",
      rep3['Phi'], [2, 2, 4])
check("ell=3: |Phi_3| = 16", prod(rep3['Phi']), 16)
check("ell=3: M m = 0, ker = Q m, negative semidefinite, minors",
      [rep3['Mm'], rep3['kernel_is_m'], rep3['neg_semidef'], rep3['minor_test']],
      [True] * 4)
pc3 = point_components(res23, cps3)
cls3 = {}
for (nm, _, _) in PTS:
    cls3.setdefault(pc3[nm]['comp'], []).append(nm)
E125_ABC = sorted([sorted(["(1,3)", "(-2,-6)", "(-1/11,15/11)"]),
                   sorted(["(1,-3)", "(-2,6)", "(-1/11,-15/11)"]),
                   sorted(["(-1,3)", "(-1,-3)", "(0,0)"])])
check("ell=3: the A/B/C partition of section E125(c)",
      sorted(sorted(v) for v in cls3.values()), E125_ABC)
check("ell=3: sigma swaps A and B",
      pc3["(1,3)"]['comp'] != pc3["(1,-3)"]['comp'], True)
check("ell=3: sigma fixes C",
      pc3["(-1,3)"]['comp'] == pc3["(-1,-3)"]['comp'], True)
A3 = pc3["(1,3)"]['comp']
B3c = pc3["(1,-3)"]['comp']
C3 = [c for c in set(pc3[nm]['comp'] for (nm, _, _) in PTS)
      if c not in (A3, B3c)][0]
L3 = local_pairing(M3, mu3, [A3, B3c, C3], A3)
check("ell=3: Lambda_3 of section E125(g)", L3,
      matrix(QQ, [[0, 0, 0], [0, 1, QQ(1) / 2], [0, QQ(1) / 2, QQ(3) / 4]]))

# ---------------------------------------------------------------------------
print("\n(I) independent checks on M")
# ---------------------------------------------------------------------------
check("elementary divisors of M", rep2['elementary_divisors'],
      [1, 1, 1, 1, 1, 1, 8, 0])
check("|det M^(i)| = |Phi| m_i^2 for every i", rep2['minor_test'], True)
check("charpoly of M has no negative coefficient (neg. semidefinite)",
      all(c >= 0 for c in M2.charpoly().coefficients(sparse=False)), True)
check("rank M = n - 1 (the fibre is connected)", M2.rank(), len(cps2) - 1)

print()
print("=" * 74)
print("intersection matrix of the closed fibre of C_4 over Z_2:")
print(M2)
print("multiplicities:", list(mu2))
print("=" * 74)
if NFAIL == 0:
    print("JUDGEMENT: GREEN -- %s/%s checks passed" % (NPASS, NPASS))
    sys.exit(int(0))
else:
    print("JUDGEMENT: RED -- %s/%s checks failed: %s"
          % (NFAIL, NPASS + NFAIL, FAILS))
    sys.exit(int(1))
