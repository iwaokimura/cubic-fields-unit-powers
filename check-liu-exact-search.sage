# check-liu-exact-search.sage -- E129, the gate.
#
# E128 searched for the singular points of the double cover of the next round
# among the closed points of degree <= 2 of each component of the closed fibre,
# and recorded the [GAP] that a singular point over a closed point of higher
# degree would be missed, no stopping degree being proved.
#
# E129 replaces that search by Section 5.2 of arXiv:2504.16808v3 run at the
# GENERIC point of each component: the candidates are then the zeros of an
# explicit element of k(Gamma), an exact finite set of closed points of any
# degree, and the degree heuristic is not used at all.
#
# Groups:
#   (A) E129 (a): the precision of the round-2 charts, and Prop. 3.1(5b);
#   (B) E129 (b2) against E128: the generic ramification data along every
#       component agrees with the local data read at the visited points;
#   (C) the exact set contains every point E128 blew up, and it finds by
#       itself the degree-2 closed point that the heuristic needed;
#   (D) with the heuristic switched off, the model does not move;
#   (E) cross-validation against an exhaustive search to degree 4 (ell = 2)
#       and degree 3 (ell = 3);
#   (F) negative controls: dropping candidates makes the gate red;
#   (G) every number of E128, and E104's |Upsilon_2| <= 2 rerun on this model;
#   (H) p_a of the closed fibre, kept as the cheapest bug detector there is.
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
        print("  PASS  %-60s %s" % (name, got))
    else:
        NFAIL += 1
        FAILS.append(name)
        print("  FAIL  %-60s got %s want %s" % (name, got, want))
    sys.stdout.flush()


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
Zt = PolynomialRing(QQ, 'th')
W9 = Zt.gen() ** 2 + 1


def round1(ell, hpoly=None, all_rational=False, point_degree=1, next_cover=True):
    B = LiuBase(ell) if hpoly is None else LiuBase(ell, hpoly)
    Rs = PolynomialRing(B.O, 's')
    t = Rs.gen()
    LC = LineCover(B, -6 * (t - 1) ** 2, 27 * t * (t ** 3 - 4), 1,
                   sections=[(nm, t0, w0 ** 2, w0) for (nm, t0, w0) in PTS],
                   all_rational=all_rational, point_degree=point_degree,
                   next_cover=next_cover)
    return LC, LC.resolution()


def full(ell, hpoly=None, P=10, **kw):
    """round 1, round 2 and the reading of the closed fibre."""
    LC, res1 = round1(ell, hpoly, **kw)
    c1, Ms1, good1 = analyse(res1)
    res2, lab2, eps2 = round2(res1, P=P)
    c2, Ms2, good2 = analyse(res2, P=P)
    assert len(good2) == 1, "%s intersection matrices" % len(good2)
    ch, M, mu, gen, cps, rep = good2[0]
    return dict(LC=LC, res1=res1, res2=res2, lab2=lab2, eps=eps2,
                comps1=c1, good1=good1, comps2=cps, M=M, mult=list(mu),
                genus=gen, rep=rep, P=P,
                pa=genus_of_fibre(M, mu, gen),
                pc=point_components(res2, cps, P=P))


def visited(res):
    return set(nd.tag for nd in res.regular)


def blown_up(res):
    """the tags of the nodes at which the resolution actually blew up."""
    return set(nd.tag for nd in res.nodes if nd.lam is not None and nd.lam >= 2)


def all_nodes(res):
    return list(res.nodes)


CASES = set()
KINDS = set()


print("=" * 78)
print("E129 gate: the search for singular points as an exact finite set")
print("=" * 78)

# ---------------------------------------------------------------------------
print("\n(0) the two models, built without the degree heuristic")
# ---------------------------------------------------------------------------
EX2 = full(2, None, P=10)
EX3 = full(3, W9, P=12)
check("ell=2: all_rational is off", EX2['res1'].all_rational, False)
check("ell=3: all_rational is off", EX3['res1'].all_rational, False)
check("ell=2: the generic Section 5.2 is on", EX2['res1'].next_cover, True)
check("ell=3: the generic Section 5.2 is on", EX3['res1'].next_cover, True)

# ---------------------------------------------------------------------------
print("\n(A) E129 (a): precision, and the degree bounds of Prop. 3.1(5b)")
# ---------------------------------------------------------------------------
# Round 1 is exact: its charts are polynomials, nothing is truncated.
for ell, D in (2, EX2), (3, EX3):
    nds = all_nodes(D['res1'])
    check("ell=%s: round 1 carries no truncation (abprec is None)" % ell,
          set(nd.abprec for nd in nds), {None})
    check("ell=%s: round 1 charts carry no truncation" % ell,
          set(nd.chart.prec for nd in nds), {None})
# Round 2 is where the power series live.  Every root carries a finite
# precision, and every order read off a and b is asserted to be below it.
for ell, D in (2, EX2), (3, EX3):
    nds = all_nodes(D['res2'])
    pr = sorted(set(nd.abprec for nd in nds))
    check("ell=%s: every round-2 node carries a finite precision" % ell,
          all(p is not None for p in pr), True)
    check("ell=%s: round-2 precisions are <= P and >= 2" % ell,
          all(2 <= p <= D['P'] for p in pr), True)
    check("ell=%s: lambda < precision at every round-2 node" % ell,
          all(nd.lam is None or nd.lam < nd.abprec for nd in nds), True)
    print("        ell=%s: precisions %s, P = %s" % (ell, pr, D['P']))
# Prop. 3.1(5b) on every exceptional divisor of round 1: with r = [lambda/2],
# deg(abar) <= r and deg(bbar) <= 2r.  Those are the degrees that make the
# inequality "precision > lambda+1" sufficient.
for ell, D in (2, EX2), (3, EX3):
    ok = []
    for lab, d in D['res1'].divs.items():
        lp = d.get('lam_parent')
        if lp is None:
            continue
        r = ZZ(lp) // 2
        ab, bb = d['abar'], d['bbar']
        ok.append((ab == 0 or ab.degree() <= r) and
                  (bb == 0 or bb.degree() <= 2 * r))
    check("ell=%s: deg(abar) <= r and deg(bbar) <= 2r on every E_i" % ell,
          [len(ok), all(ok)], [len(ok), True])
# the negative control for (a): with the precision one short of lambda+1 the
# candidate search must refuse to run
lab = [l for l in EX2['res1'].divs if EX2['res1'].divs[l].get('lam_parent')][0]
d = EX2['res1'].divs[lab]
ch0, a1, b1 = d['chart0']
lp = d['lam_parent']
raised = None
try:
    Resolution._sing_candidates(ch0, a1, b1, lp, prec=2 * (ZZ(lp) // 2) + 1)
    raised = False
except AssertionError:
    raised = True
check("a precision of exactly lambda+1 is refused (negative control)",
      raised, True)
raised2 = None
try:
    Resolution._sing_candidates(ch0, a1, b1, lp, prec=2 * (ZZ(lp) // 2) + 2)
    raised2 = False
except AssertionError:
    raised2 = True
check("a precision of lambda+2 is accepted", raised2, False)

# ---------------------------------------------------------------------------
print("\n(B) E129 (b2) against E128: the generic data along every component")
# ---------------------------------------------------------------------------
# For each component E_i of the closed fibre of Z_N and each component Gamma of
# psi^{-1}(E_i), Section 5.1 at the generic point of Gamma gives the orders
# (nu_Gamma(a_2), nu_Gamma(b_2)) of the normalised next cover.  Only
# min{2 nu(a_2), nu(b_2)} is intrinsic (a translation of the cover coordinate
# moves the two separately), and it is 1 exactly where the next cover ramifies.
# It must agree with what E128 reads locally in every chart.
for ell, D in (2, EX2), (3, EX3):
    res1, res2, lab2 = D['res1'], D['res2'], D['lab2']
    loc = {}
    for ep in D['eps']:
        chp = ep.chart2
        for co, g in (('S', chp.base.S), ('T', chp.base.T)):
            if ep.divs2[co] is None:
                continue
            va = _coordval(chp, ep.a2, g)
            vb = _coordval(chp, ep.b2, g)
            loc.setdefault(ep.divs2[co][0], set()).add(min(2 * va, vb))
    agree, ecmp, nbcmp = [], [], []
    for lab in sorted(res1.divs):
        dd = res1.divs[lab]
        chart0, aa, bb = dd['chart0']
        gcs = component_generic_objects(chart0, dd['coord0'], aa, bb)
        nbcmp.append((len(gcs), dd['nbranch']))
        gmn = []
        for gc in gcs:
            gc.next_cover_candidates(dd['ucov0'])
            CASES.add(gc.case)
            KINDS.add(gc.kind)
            nA, rA, nB, rB = gc.normalise_next(dd['ucov0'])
            mn = nB if nA is infinity else min(2 * nA, nB)
            assert mn <= 1, "Section 5.1 did not normalise at the generic point"
            gmn.append(mn)
        agree.append(set(gmn) == loc[lab])
        ge = sorted(2 if m == 1 else 1 for m in gmn)
        le = sorted(res2.divs[lab2[(lab, al)]]['e'] for al in range(dd['nbranch']))
        ecmp.append(ge == le)
    check("ell=%s: number of branches of Theta_i = Prop. 3.7's nbranch" % ell,
          all(a == b for a, b in nbcmp), True)
    check("ell=%s: generic min{2nu(a2),nu(b2)} = the local one, on every E_i"
          % ell, [len(agree), all(agree)], [len(agree), True])
    check("ell=%s: generic ramification index of the next cover = E128's"
          % ell, [len(ecmp), all(ecmp)], [len(ecmp), True])
    # round 2 needs no blow-up at either prime, which is why E129 (a)'s
    # inequality never has to be used in anger here
    check("ell=%s: round 2 blows up nothing" % ell, blown_up(res2), set())
    check("ell=%s: round 2 has no exceptional divisor" % ell,
          len(res2.divs), len(D['comps1']))
check("all three cases of Prop. 3.7 occur (ram, split, inert)",
      sorted(KINDS), ['inert', 'ram', 'split'])
check("all three branches of Section 5.2 are exercised",
      sorted(CASES), ['(1)', '(2.1)', '(2.3)'])

# ---------------------------------------------------------------------------
print("\n(C) the exact set against E128's degree-<=2 search")
# ---------------------------------------------------------------------------
H2 = full(2, None, P=10, all_rational=True, point_degree=2, next_cover=False)
H3 = full(3, W9, P=12, all_rational=True, point_degree=1, next_cover=False)
EX3Q = full(3, None, P=12)
for ell, D, H in (2, EX2, H2), (3, EX3, H3):
    check("ell=%s: every point E128 blew up is in the exact set" % ell,
          blown_up(H['res1']) <= visited(D['res1']) | blown_up(D['res1']), True)
    check("ell=%s: E128's model and the exact model agree (components)" % ell,
          [len(D['comps2']), sorted(D['mult']), D['rep']['Phi'], D['pa']],
          [len(H['comps2']), sorted(H['mult']), H['rep']['Phi'], H['pa']])
    check("ell=%s: E128's model and the exact model agree (matrix)" % ell,
          D['M'] == H['M'] or
          sorted(D['M'].eigenvalues()) == sorted(H['M'].eigenvalues()), True)
    print("        ell=%s: visited %s points, E128 visited %s"
          % (ell, len(visited(D['res1'])), len(visited(H['res1']))))
# The sharpest single case: over Z_(3) the ramification of Theta_2 -> E_2 sits
# at the closed point X^2+1 of degree 2.  E128 had to be told to look there
# (point_degree = 2); the exact search finds it by itself, and without it the
# arithmetic genus comes out wrong.
tags = visited(EX3Q['res1'])
check("ell=3 over Z_(3): the exact search finds the degree-2 point X^2+1",
      any('[X^2 + 1]' in t for t in tags), True)
check("ell=3 over Z_(3): p_a = g = 3 with the exact search", EX3Q['pa'], 3)

# ---------------------------------------------------------------------------
print("\n(D) the heuristic is not needed")
# ---------------------------------------------------------------------------
check("ell=2: point_degree is 1", EX2['res1'].point_degree, 1)
check("ell=3: point_degree is 1", EX3['res1'].point_degree, 1)
check("ell=2: Phi_2 = Z/8 without the heuristic", EX2['rep']['Phi'], [8])
check("ell=3: Phi_3 = Z/2 x Z/2 x Z/4 without the heuristic",
      EX3['rep']['Phi'], [2, 2, 4])

# ---------------------------------------------------------------------------
print("\n(E) cross-validation against an exhaustive search")
# ---------------------------------------------------------------------------
# Every closed point of degree <= 4 (ell = 2) resp. <= 3 (ell = 3) of every
# component is visited as well.  Nothing new must turn up: no point outside
# the exact set may be singular, and the model may not move.
X2 = full(2, None, P=10, all_rational=True, point_degree=4)
check("ell=2: an exhaustive search to degree 4 blows up nothing new",
      blown_up(X2['res1']) <= visited(EX2['res1']) | blown_up(EX2['res1']), True)
check("ell=2: an exhaustive search to degree 4 gives the same model",
      [len(X2['comps2']), sorted(X2['mult']), X2['rep']['Phi'], X2['pa']],
      [len(EX2['comps2']), sorted(EX2['mult']), EX2['rep']['Phi'], EX2['pa']])
print("        ell=2: the exhaustive run visited %s points, the exact one %s"
      % (len(visited(X2['res1'])), len(visited(EX2['res1']))))
# At ell = 3 the exhaustive leg is run over Z_(3) rather than over W(F_9):
# that is the base on which a closed point of degree > 1 is load-bearing (the
# ramification of Theta_2 -> E_2 sits at X^2+1 there), and over F_9 every
# component of every closed point of degree <= 3 would be 285 points per
# divisor -- the cost of the base-change tower, not of the search.
X3 = full(3, None, P=12, all_rational=True, point_degree=3)
check("ell=3 over Z_(3): an exhaustive search to degree 3 blows up nothing new",
      blown_up(X3['res1']) <= visited(EX3Q['res1']) | blown_up(EX3Q['res1']), True)
check("ell=3 over Z_(3): an exhaustive search to degree 3 gives the same model",
      [len(X3['comps2']), sorted(X3['mult']), X3['rep']['Phi'], X3['pa']],
      [len(EX3Q['comps2']), sorted(EX3Q['mult']), EX3Q['rep']['Phi'], EX3Q['pa']])
print("        ell=3 over Z_(3): the exhaustive run visited %s points, the exact one %s"
      % (len(visited(X3['res1'])), len(visited(EX3Q['res1']))))

# ---------------------------------------------------------------------------
print("\n(F) what each exact set is worth, and the negative controls")
# ---------------------------------------------------------------------------
# Two exact sets replace the heuristic: the zeros of the discriminant along
# each component, and Section 5.2 at the generic point for the next cover.
# They are worth very different things here, and it is worth saying which.
#
# (F1) Section 5.2 at the generic point adds no point that round 1's own
# Section 5.2 has not already produced, at either prime: switching it off does
# not move the model.  It is not load-bearing for the ANSWER -- it is what
# makes the answer's completeness provable rather than lucky.
for name, ell, hp, P, D in (("ell=2", 2, None, 10, EX2),
                            ("ell=3 over W(F_9)", 3, W9, 12, EX3),
                            ("ell=3 over Z_(3)", 3, None, 12, EX3Q)):
    N = full(ell, hp, P=P, next_cover=False)
    check("%s: the generic Section 5.2 does not move the model" % name,
          [len(N['comps2']), sorted(N['mult']), N['rep']['Phi'], N['pa']],
          [len(D['comps2']), sorted(D['mult']), D['rep']['Phi'], D['pa']])
    extra = sorted(visited(D['res1']) - visited(N['res1']))
    print("        %s: it adds %s point(s): %s" % (name, len(extra), extra))
# (F2) drop the OTHER exact set -- the zeros of the discriminant -- and the
# gate is red: the arithmetic genus of the closed fibre comes out wrong.
_keep = component_ram_points
try:
    component_ram_points = lambda base, abar, bbar: set()
    pa2 = full(3, None, P=12)['pa']
except Exception as ex:
    pa2 = "exception: %s" % type(ex).__name__
finally:
    component_ram_points = _keep
check("dropping the discriminant zeros makes the gate red (negative control)",
      pa2 != 3, True)
print("        p_a with the discriminant zeros dropped: %s" % (pa2,))
# (F3) drop exactly ONE candidate: keep the discriminant zeros of degree 1 and
# throw away the rest.  That is the degree heuristic at point_degree = 1, and
# over Z_(3) it loses the single closed point X^2+1 -- and the gate is red.
try:
    component_ram_points = lambda base, abar, bbar, _k=_keep: set(
        F for F in _k(base, abar, bbar) if F.degree() <= 1)
    pa3 = full(3, None, P=12)['pa']
except Exception as ex:
    pa3 = "exception: %s" % type(ex).__name__
finally:
    component_ram_points = _keep
check("dropping the one degree-2 candidate makes the gate red (negative control)",
      pa3 != 3, True)
print("        p_a with the degree-2 candidate dropped: %s" % (pa3,))
check("the exact search is restored after the negative controls",
      full(3, None, P=12)['pa'], 3)

# ---------------------------------------------------------------------------
print("\n(G) every number of E128, from the model built without the heuristic")
# ---------------------------------------------------------------------------
EQ = EllipticCurve([0, 216, 0, -31104, -2985984]).minimal_model()
for ell, D, kod, tam, mults in ((2, EX2, 'I2*', 4, [1, 1, 1, 1, 2, 2, 2]),
                                (3, EX3, 'I0*', 4, [1, 1, 1, 1, 2])):
    ch1, M1, mu1, gen1, cps1, rep1 = D['good1'][0]
    ld = EQ.local_data(ell)
    check("ell=%s: round 1 is Tate's answer (%s, c=%s)" % (ell, kod, tam),
          [str(ld.kodaira_symbol()), ld.tamagawa_number(), sorted(mu1),
           rep1['Phi'], genus_of_fibre(M1, mu1, gen1)],
          [kod, tam, mults, [2, 2], 1])
check("E128 (d): eight components, multiplicities (1,1,1,2,2,2,2,4)",
      sorted(EX2['mult']), [1, 1, 1, 2, 2, 2, 2, 4])
check("E128 (d): Phi_2 = Z/8", EX2['rep']['Phi'], [8])
check("E128 (d): all components rational", EX2['genus'], [0] * len(EX2['genus']))
check("E128 (d): elementary divisors of M", EX2['rep']['elementary_divisors'],
      [1, 1, 1, 1, 1, 1, 8, 0])
check("E128 (d): M symmetric, Mm=0, ker=Qm, negative semidefinite, minors",
      [EX2['rep']['symmetric'], EX2['rep']['Mm'], EX2['rep']['kernel_is_m'],
       EX2['rep']['neg_semidef'], EX2['rep']['minor_test']], [True] * 5)
# (e) Magma's fibre, after contracting the two (-1)-curves of multiplicity 2
MAGMA_M = matrix(ZZ, [[-3, 1, 0, 1, 0, 0], [1, -3, 0, 1, 0, 0],
                      [0, 0, -4, 0, 2, 0], [1, 1, 0, -3, 0, 1],
                      [0, 0, 2, 0, -3, 1], [0, 0, 0, 1, 1, -1]])
MAGMA_MULT = [1, 1, 1, 2, 2, 4]
Mc, muc = EX2['M'], list(EX2['mult'])
check("E128 (e): the (-1)-curves have multiplicities 2, 2, 4",
      sorted([muc[i] for i in range(len(muc)) if Mc[i, i] == -1]), [2, 2, 4])
for _ in range(2):
    pick = [i for i in range(Mc.nrows()) if Mc[i, i] == -1 and muc[i] == 2][0]
    keep = [j for j in range(Mc.nrows()) if j != pick]
    N = matrix(ZZ, len(keep), len(keep))
    for x, j in enumerate(keep):
        for y, kk in enumerate(keep):
            N[x, y] = Mc[j, kk] + Mc[j, pick] * Mc[pick, kk]
    Mc, muc = N, [muc[j] for j in keep]
from itertools import permutations
found = None
for pm in permutations(range(6)):
    if [muc[pm[i]] for i in range(6)] != MAGMA_MULT:
        continue
    if all(Mc[pm[i], pm[j]] == MAGMA_M[i, j] for i in range(6) for j in range(6)):
        found = pm
        break
check("E128 (e): the contracted fibre is Magma's, up to relabelling",
      [sorted(muc), found is not None], [MAGMA_MULT, True])
# (f) the nine rational points
pc = EX2['pc']
check("E128 (f): every point meets a multiplicity-1 component",
      sorted(set(pc[nm]['mult'] for (nm, _, _) in PTS)), [1])
cls = {}
for (nm, _, _) in PTS:
    cls.setdefault(pc[nm]['comp'], []).append(nm)
E104 = sorted([sorted(["(1,3)", "(-1,3)", "(-1/11,-15/11)"]),
               sorted(["(1,-3)", "(-1,-3)", "(-1/11,15/11)"]),
               sorted(["(-2,6)", "(-2,-6)", "(0,0)"])])
check("E128 (f): the partition is E104's / E127(r)'s",
      sorted(sorted(v) for v in cls.values()), E104)
sep = dict((nm, (pc[nm]['node'], pc[nm]['red']) !=
            (pc[SIGMA[nm]]['node'], pc[SIGMA[nm]]['red']))
           for (nm, _, _) in PTS if SIGMA[nm] != nm)
check("E128 (f): sigma separates the pairs over t=1, -1, -1/11 and not over -2",
      [sep["(1,3)"], sep["(-1,3)"], sep["(-1/11,15/11)"], sep["(-2,6)"]],
      [True, True, True, False])
# (g) the local pairing
base = pc["(1,3)"]['comp']
order = [base] + sorted(set(pc[nm]['comp'] for (nm, _, _) in PTS) - {base})
L2 = local_pairing(EX2['M'], EX2['mult'], order, base)
check("E128 (g): Lambda_2 is E104's matrix", L2,
      matrix(QQ, [[0, 0, 0], [0, QQ(1) / 2, QQ(1) / 4],
                  [0, QQ(1) / 4, QQ(7) / 8]]))
# (h) the ell = 3 cross-check against E125
check("E128 (h): seven components, multiplicities (1,1,1,1,1,2,2)",
      sorted(EX3['mult']), [1, 1, 1, 1, 1, 2, 2])
check("E128 (h): Phi_3 = Z/2 x Z/2 x Z/4 (E125(b))", EX3['rep']['Phi'], [2, 2, 4])
pc3 = EX3['pc']
cls3 = {}
for (nm, _, _) in PTS:
    cls3.setdefault(pc3[nm]['comp'], []).append(nm)
E125_ABC = sorted([sorted(["(1,3)", "(-2,-6)", "(-1/11,15/11)"]),
                   sorted(["(1,-3)", "(-2,6)", "(-1/11,-15/11)"]),
                   sorted(["(-1,3)", "(-1,-3)", "(0,0)"])])
check("E128 (h): the A/B/C partition of E125(c)",
      sorted(sorted(v) for v in cls3.values()), E125_ABC)
A3 = pc3["(1,3)"]['comp']
B3 = pc3["(1,-3)"]['comp']
C3 = [c for c in set(pc3[nm]['comp'] for (nm, _, _) in PTS) if c not in (A3, B3)][0]
check("E128 (h): Lambda_3 is E125(g)'s matrix",
      local_pairing(EX3['M'], EX3['mult'], [A3, B3, C3], A3),
      matrix(QQ, [[0, 0, 0], [0, 1, QQ(1) / 2], [0, QQ(1) / 2, QQ(3) / 4]]))
# E104's bound on Upsilon_2, rerun on this model (E129 section 8-2)
one = [i for i in range(len(EX2['mult'])) if EX2['mult'][i] == 1]
check("E104 rerun: exactly three multiplicity-1 components", len(one), 3)
check("E104 rerun: C_4(Q_2) meets only those three",
      set(pc[nm]['comp'] for (nm, _, _) in PTS) <= set(one), True)
sig = dict((pc[nm]['comp'], pc[SIGMA[nm]]['comp']) for (nm, _, _) in PTS)
check("E104 rerun: sigma acts on them as a well-defined involution",
      all(sig[sig[c]] == c for c in sig) and len(sig) == 3, True)
fixed = [c for c in sig if sig[c] == c]
check("E104 rerun: sigma is a transposition, fixing exactly one component",
      len(fixed), 1)
# h_2 is constant on components and sigma-invariant (E088), so it takes at
# most one value on the transposed pair and one on the fixed component
check("E104 rerun: |Upsilon_2| <= 2 follows", 1 + len(fixed), 2)

# ---------------------------------------------------------------------------
print("\n(H) the arithmetic genus, kept")
# ---------------------------------------------------------------------------
check("ell=2: p_a(closed fibre) = g(C_4) = 3", EX2['pa'], 3)
check("ell=3: p_a(closed fibre) = g(C_4) = 3", EX3['pa'], 3)
check("ell=2: p_a of the round-1 fibre = g(E) = 1",
      genus_of_fibre(EX2['good1'][0][1], EX2['good1'][0][2],
                     EX2['good1'][0][3]), 1)
check("ell=3: p_a of the round-1 fibre = g(E) = 1",
      genus_of_fibre(EX3['good1'][0][1], EX3['good1'][0][2],
                     EX3['good1'][0][3]), 1)

print()
print("=" * 78)
if NFAIL == 0:
    print("JUDGEMENT: GREEN -- %s/%s checks passed" % (NPASS, NPASS))
    sys.exit(int(0))
else:
    print("JUDGEMENT: RED -- %s/%s checks failed: %s"
          % (NFAIL, NPASS + NFAIL, FAILS))
    sys.exit(int(1))
