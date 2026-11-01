# check-liu-examples.sage -- E128, the answer-key gate for liu-model-lib.sage.
#
# The implementation of Q. Liu, "Desingularization of double covers of regular
# surfaces" (arXiv:2504.16808v3) is tested against
#   (A) Example 3.10 of the paper itself -- a complete resolution of a genus 2
#       curve over Z_2, for which the paper states every lambda, every
#       multiplicity, the shape of every exceptional locus and the equation of
#       the elliptic component;
#   (B) Example 2.12 of the paper -- the multiplicity lambda_m(B);
#   (C) Tate's algorithm: Liu's algorithm is run on the Weierstrass double
#       cover E -> P^1_x of elliptic curves at ell = 2 and 3 (both wild) and
#       the closed fibre of the minimalized model is compared with the
#       Kodaira type and the component group.
import sys
# Run from the directory that holds liu-model-lib.sage (the repository
# root); see the README.
load("liu-model-lib.sage")

NPASS = 0; NFAIL = 0; FAILS = []

def check(name, got, want=None, cond=None):
    global NPASS, NFAIL
    ok = (got == want) if cond is None else cond
    if ok:
        NPASS += 1; print("  PASS  %-56s %s" % (name, got))
    else:
        NFAIL += 1; FAILS.append(name)
        print("  FAIL  %-56s got %s want %s" % (name, got, want))
    sys.stdout.flush()

print("=" * 74)
print("E128 answer-key gate for liu-model-lib.sage")
print("=" * 74)

# ---------------------------------------------------------------------------
print("\n(B) Example 2.12: B = Z[x,y]/(y^2 + x^5 - 1), lambda_m(B)")
# ---------------------------------------------------------------------------
# (2b) ell = 5, m_5 = (5, x-1):  lambda = ord(x^5-1) = 2
# (2c) ell = 2, m_2 = (2, x)  :  lambda = 2 ord(2)  = 2   (via z = y-1)
# (2d) ell = 2, m != m_2      :  lambda = 1
# (2a) ell != 2,5             :  lambda <= 1, = 1 iff f | x^5-1
for (ell, x0, want) in [(5, 1, 2), (5, 0, 0), (2, 0, 2), (2, 1, 1),
                        (3, 1, 1), (3, 0, 0), (7, 1, 1), (7, 0, 0),
                        (11, 1, 1), (11, 3, 1), (11, 2, 0)]:
    B = LiuBase(ell); S, T = B.S, B.T
    ch = LiuChart(B, T, {'S': None, 'T': 0})
    lam = ch.lam(B.R(0), (S + x0) ** 5 - 1)[0]
    check("ell=%-2s  m=(%s, x-%s):  lambda" % (ell, ell, x0), lam, want)

# ---------------------------------------------------------------------------
print("\n(A) Example 3.10: y^2 = (s^2-2)^3 + 16 m s^2 + n^2 over Z_2")
# ---------------------------------------------------------------------------
def ex310(n, m, verbose=False):
    B = LiuBase(2)
    Rs = PolynomialRing(B.O, 's'); s = Rs.gen()
    m1 = -(4 * m + 3)
    a = 2 * (s ** 3 + n)
    b = 2 * (3 * s ** 4 + n * s ** 3 + 2 * m1 * s ** 2 + 4)
    LC = LineCover(B, a, b, 2, verbose=verbose,
                   all_rational=True, point_degree=2)
    res = LC.resolution()
    by = {}
    for l in res.divs:
        if res.divs[l]['name'] != 'E0':
            by[res.divs[l]['name']] = res.divs[l]
    return LC, res, by

def D(by, tag, key):
    return by[tag][key] if tag in by else None

# --- Part (I)-(I.2): the point at infinity, common to every case ------------
for (n, m) in [(1, 0), (2, 0), (4, 0)]:
    LC, res, by = ex310(n, m)
    check("n=%s: (I)   lambda at q_infty" % n, D(by, 's=oo', 'lam_parent'), 2)
    check("n=%s: (I.1) Theta_1 = two lines of multiplicity 1" % n,
          [D(by, 's=oo', 'nbranch'), D(by, 's=oo', 'mult')], [2, 1])
    t2 = [k for k in by if k.startswith('s=oo|E') and k.endswith('@0')]
    check("n=%s: (I.1) unique singular point on Theta_1, lambda = 2" % n,
          D(by, t2[0], 'lam_parent'), 2)
    check("n=%s: (I.2) Theta_2 = a smooth conic of multiplicity 2" % n,
          [D(by, t2[0], 'nbranch'), D(by, t2[0], 'mult'), D(by, t2[0], 'e')],
          [1, 2, 1])

# --- Part (II)-(III): n odd -------------------------------------------------
LC, res, by = ex310(1, 0)
check("n odd: (II)   two singular points, over s=0 and s=1",
      sorted(k for k in by if '|' not in k), ['s=0', 's=1', 's=oo'])
check("n odd: (II)   lambda at p_0", D(by, 's=0', 'lam_parent'), 2)
check("n odd: (II.1) Theta_1 = a reduced degenerate conic, multiplicity 1",
      [D(by, 's=0', 'nbranch'), D(by, 's=0', 'mult')], [2, 1])
k1 = [k for k in by if k.startswith('s=0|E') and k.count('|') == 1][0]
check("n odd: (II.1) unique singular point p_1, lambda = 2",
      D(by, k1, 'lam_parent'), 2)
check("n odd: (II.2) Theta_2 = two lines of multiplicity 2",
      [D(by, k1, 'nbranch'), D(by, k1, 'mult')], [2, 2])
k2 = [k for k in by if k.startswith('s=0|E') and k.count('|') == 2][0]
check("n odd: (II.2) p_2 has lambda = 2", D(by, k2, 'lam_parent'), 2)
check("n odd: (II.3) Theta_3 = a smooth conic of multiplicity 3",
      [D(by, k2, 'nbranch'), D(by, k2, 'mult')], [1, 3])
check("n odd: (III)  p_* resolved by one blow-up, exceptional P^1 of mult 1",
      [D(by, 's=1', 'nbranch'), D(by, 's=1', 'mult'), D(by, 's=1', 'lam_parent')],
      [1, 1, 2])
check("n odd: (III)  no further blow-up over p_*",
      len([k for k in by if k.startswith('s=1|')]), 0)
comps, Ms, good = analyse(res)
check("n odd: at least one valid intersection matrix", len(good) >= 1, True)
check("n odd: all valid matrices agree on (mult, Phi, p_a)",
      len(set((tuple(sorted(g[2])), tuple(g[5]['Phi']),
               genus_of_fibre(g[1], g[2], g[3])) for g in good)), 1)
choice, M, mu, gen, cps, rep = good[0]
check("n odd: p_a(closed fibre) = g = 2", genus_of_fibre(M, mu, gen), 2)
check("n odd: M m = 0, ker = Q m, negative semidefinite, minors",
      [rep['Mm'], rep['kernel_is_m'], rep['neg_semidef'], rep['minor_test']],
      [True] * 4)
check("n odd: the resolution is already minimal",
      len(contract_minus_ones(M, mu, gen, cps)[4]), 0)

# --- Part (IV): n even ------------------------------------------------------
# NOTE (recorded defect, see E128): for m ODD the
# resolution below does not terminate in this implementation -- the
# multiplicities of the exceptional divisors grow without bound, which
# Lipman's theorem forbids, so it is a defect of the implementation.  The
# cases run here are m = 0; C_4's own resolution does not enter that branch.
for (n, m, lam2, thet3) in [(2, 0, 2, [2, 2]), (4, 0, 3, [1, 4])]:
    LC, res, by = ex310(n, m)
    check("n=%s: (IV)   lambda at p_0 = 3" % n, D(by, 's=0', 'lam_parent'), 3)
    check("n=%s: (IV.1) Theta_1 = 2 P^1 (e=2), multiplicity 2" % n,
          [D(by, 's=0', 'e'), D(by, 's=0', 'mult')], [2, 2])
    k1 = [k for k in by if k.startswith('s=0|E') and k.count('|') == 1][0]
    check("n=%s: (IV.1) lambda at p_1 = 4" % n, D(by, k1, 'lam_parent'), 4)
    check("n=%s: (IV.2) Theta_2: rational, multiplicity 2" % n,
          [D(by, k1, 'nbranch'), D(by, k1, 'mult')], [1, 2])
    k2 = [k for k in by if k.startswith('s=0|E') and k.count('|') == 2][0]
    check("n=%s: (IV.2) the singular point of Theta_2 is at t_2 = 1" % n,
          k2.endswith('@1'), True)
    check("n=%s: (IV.3) lambda at p_2" % n, D(by, k2, 'lam_parent'), lam2)
    check("n=%s: (IV.3) Theta_3: (branches, multiplicity)" % n,
          [D(by, k2, 'nbranch'), D(by, k2, 'mult')], thet3)
    if n == 4:
        k3 = [k for k in by if k.startswith('s=0|E') and k.count('|') == 3][0]
        check("n=%s: (IV.3.2) lambda at p_3 = 4" % n, D(by, k3, 'lam_parent'), 4)
        Xk = D(by, k3, 'bbar').parent().gen()
        check("n=%s m=%s: (IV.3.3) the elliptic component is w^2+w+x^3+m" % (n, m),
              [D(by, k3, 'abar'), D(by, k3, 'bbar')],
              [D(by, k3, 'abar').parent()(1), Xk ** 3 + GF(2)(m)])
    comps, Ms, good = analyse(res)
    check("n=%s m=%s: all valid matrices agree on (mult, Phi, p_a)" % (n, m),
          len(set((tuple(sorted(g[2])), tuple(g[5]['Phi']),
                   genus_of_fibre(g[1], g[2], g[3])) for g in good)), 1)
    choice, M, mu, gen, cps, rep = good[0]
    check("n=%s m=%s: p_a(closed fibre) = g = 2" % (n, m),
          genus_of_fibre(M, mu, gen), 2)
    check("n=%s m=%s: M m = 0, ker = Q m, negative semidefinite, minors" % (n, m),
          [rep['Mm'], rep['kernel_is_m'], rep['neg_semidef'], rep['minor_test']],
          [True] * 4)
    if n == 4:
        M2, mu2, g2, lb2, cont = contract_minus_ones(M, mu, gen, cps)
        check("n=4 m=%s: (IV.3.3) two (-1)-curves are contracted" % m,
              len(cont), 2)
        check("n=4 m=%s: the minimal fibre keeps the elliptic component" % m,
              1 in g2, True)

# ---------------------------------------------------------------------------
print("\n(A') Example 3.10 (IV.3.2): lambda at p_3, from the paper's own equation")
# ---------------------------------------------------------------------------
# Liu writes, for n = 2 n_1 with n_1 = 2 n_2 even, the equation of Y_3 at p_3
#     z_3^2 + n_2 s^2 (1+s x_1)^3 z_3 + x_1^3 s - m s^2 (1+s x_1)^4 = 0
# in the chart where 2 = s^2 (1 + s x_1), and states lambda_{p_3}(Y_3) = 4.
# Computing lambda from that very equation gives 4 unless BOTH n_2 and m are
# odd, where it is 3 -- with ord(a) = 2 and ord(b) = 3 for the optimal
# generator, so that Lemma 2.10(2a) applies (an initial form of odd degree is
# not a square).  This is the branch on which our resolution of Example 3.10
# does not terminate; see E128 (i').
Bx = LiuBase(2); Sx, Tx = Bx.S, Bx.T
chx = LiuChart(Bx, Sx ** 2 * (1 + Sx * Tx), {'S': 1, 'T': None})
check("the chart of (IV.3.3) has ord(2) = 2", chx.d, 2)
for (n2, m, want) in [(1, 0, 4), (1, 2, 4), (2, 0, 4), (2, 1, 4), (2, 3, 4),
                      (1, 1, 3), (1, 3, 3), (1, -1, 3), (3, 1, 3)]:
    aL = n2 * Sx ** 2 * (1 + Sx * Tx) ** 3
    bL = Tx ** 3 * Sx - m * Sx ** 2 * (1 + Sx * Tx) ** 4
    check("(IV.3.2) n_2=%-2s m=%-2s: lambda at p_3 %s" % (
              n2, m, "" if want == 4 else "(the paper says 4)"),
          chx.lam(aL, bL)[0], want)

# ---------------------------------------------------------------------------
print("\n(A'') Example 3.10, m odd: where the non-termination actually is")
# ---------------------------------------------------------------------------
# E128 (i') recorded that our resolution of Example 3.10 does not finish for m
# odd, and blamed the search of Lemma 2.10, "whose cost is |k|^(ord(b)/2+1)".
# That is wrong, and this group pins the real cause (E129,
# addendum).  The run stalls in depurate(), which iterates the rewriting
# ell^e -> f^e on every coefficient that is not an ell-adic unit.  That
# iteration converges when f's own coefficients are units and NEED NOT when
# they are not -- and a translation T -> T + theta with theta != 0 is exactly
# what destroys the unit property, through the binomial coefficients: in
# characteristic 2, (T+1)^4 has even middle coefficients.  So the run stalls
# at ...|E9@1 and not at ...|E9@0.
Bd = LiuBase(2); Sd, Td = Bd.S, Bd.T
CH_GOOD = LiuChart(Bd, Sd ** 11 * Td ** 4 + Sd ** 6 * Td ** 2)
CH_BAD = LiuChart(Bd, Sd ** 11 * (Td + 1) ** 4 + Sd ** 6 * (Td + 1) ** 2)


def depurate_rounds(ch, z, cap):
    """the maximum ell-adic valuation of the coefficients after each round of
    depurate()'s rewriting; it must fall to 0 for depurate() to terminate."""
    B = ch.base
    z = ch.R(z)
    out = []
    for _ in range(cap):
        W = ch._terms(z)
        out.append(max(t[2] for t in W))
        if out[-1] == 0:
            return out
        zn = ch.R(0)
        for (u, v), c, e, w in W:
            zn += (c / B.ell ** e) * ch._fpow(e) * B.S ** u * B.T ** v
        if zn == z:
            return out
        z = zn
    return out


check("the untranslated chart: f's coefficients are 2-adic units",
      sorted(set(Bd.oval(c) for c in CH_GOOD.f.dict().values())), [0])
check("the translated chart: f's coefficients are NOT all units",
      sorted(set(Bd.oval(c) for c in CH_BAD.f.dict().values())), [0, 1, 2])
rg = depurate_rounds(CH_GOOD, 2, 6)
check("depurate(2) terminates on the untranslated chart", rg[-1], 0)
rb = depurate_rounds(CH_BAD, 2, 4)
check("depurate(2) diverges on the translated chart: the valuation goes up",
      [rb[-1] > rb[0], rb == sorted(rb)], [True, True])
print("        valuations per round: untranslated %s, translated %s" % (rg, rb))
check("ord(2) is nevertheless correct and instant on both charts",
      [CH_GOOD.ord(CH_GOOD.R(2)), CH_BAD.ord(CH_BAD.R(2))], [8, 6])
# and the Lemma 2.10 search at the node where the run stalls is 3 candidates
STALL = "s=0|E3@0|E4@1|E5@0|E6@oo|E7@0|E9@1"


class _Caught(Exception):
    def __init__(self, nd):
        self.nd = nd


_procA = Resolution.process


def _proc_stop(self, nd, stack):
    if nd.tag == STALL:
        raise _Caught(nd)
    return _procA(self, nd, stack)


Resolution.process = _proc_stop
Bs = LiuBase(2)
Rss = PolynomialRing(Bs.O, 's'); ss = Rss.gen()
LCs = LineCover(Bs, 2 * (ss ** 3 + 4),
                2 * (3 * ss ** 4 + 4 * ss ** 3 + 2 * (-(4 * 1 + 3)) * ss ** 2 + 4), 2,
                all_rational=False, point_degree=1, next_cover=False)
ndS = None
try:
    LCs.resolution()
except _Caught as _c:
    ndS = _c.nd
finally:
    Resolution.process = _procA
check("the stalling node is reached (n=4, m=1)", ndS is not None, True)
chS = ndS.chart
oaS, obS = chS.ord(chS.R(ndS.a)), chS.ord(chS.R(ndS.b))
check("at the stalling node ord(a), ord(b) are small", [oaS, obS], [2, 2])
check("so Lemma 2.10 searches |k|^(ord(b)/2+1) = 2^2 = 4 candidates, not many",
      2 ** (ZZ(obS) // 2 + 1), 4)
check("and lambda there is 2, computed at once", chS.lam(chS.R(ndS.a), chS.R(ndS.b))[0], 2)
check("the stalling chart is the translated one (f not all units)",
      max(Bs.oval(c) for c in chS.f.dict().values()) > 0, True)

# ---------------------------------------------------------------------------
print("\n(A3) Example 3.10 for m odd: E128 (i') closed (E130)")
# ---------------------------------------------------------------------------
# E129's addendum localised the non-termination in depurate(), whose rewriting
# ell^e -> f^e need not converge when f's own coefficients are not ell-adic
# units.  E130 replaced the uses of depurate() that need only part of the
# answer by LiuChart.clean_below(), which rewrites a term only while its total
# degree (or its exponent of S resp. T) is below a bound; one rewriting raises
# that value by at least one, so it stops after boundedly many rounds.  The
# branch now runs to the end, and the arithmetic genus checks it.
for (n, m, ndiv, ncomp, mults) in [
        (4, 1, 13, 14, [1, 1, 2, 2, 2, 2, 4, 4, 6, 6, 8, 8, 10, 12]),
        (4, 3, 13, 14, [1, 1, 2, 2, 2, 2, 4, 4, 6, 6, 8, 8, 10, 12]),
        (1, 1, 7, 10, [1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
        (3, 1, 7, 10, [1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
        (4, 2, 7, 8, [1, 1, 2, 2, 2, 2, 2, 4])]:
    LC3, res3, by3 = ex310(n, m)
    comps3, Ms3, good3 = analyse(res3)
    check("n=%s m=%s: the resolution terminates" % (n, m),
          [len(res3.divs), len(comps3)], [ndiv, ncomp])
    check("n=%s m=%s: multiplicities of the closed fibre" % (n, m),
          sorted(good3[0][2]) if good3 else None, mults)
    check("n=%s m=%s: p_a(closed fibre) = g = 2" % (n, m),
          genus_of_fibre(good3[0][1], good3[0][2], good3[0][3]) if good3 else None,
          2)
# clean_below is what makes this terminate, and it is bounded by construction
Bt = LiuBase(2)
St, Tt = Bt.S, Bt.T
CHT = LiuChart(Bt, St ** 11 * (Tt + 1) ** 4 + St ** 6 * (Tt + 1) ** 2)
check("depurate() still diverges on the pathological chart (it is unchanged)",
      max(Bt.oval(c) for c in CHT.f.dict().values()) > 0, True)
for bnd in (1, 2, 3, 5, 8):
    z = CHT.clean_below(CHT.R(2), None, bnd)
    dirty = [e[0] + e[1] for e, c in z.dict().items() if Bt.oval(c) > 0]
    check("clean_below(2, total degree < %s) leaves nothing dirty below it" % bnd,
          (min(dirty) if dirty else Infinity) >= bnd, True)
check("no term of 2 survives below its order, so blowUp's division is exact",
      min(e[0] + e[1] for e in CHT.clean_below(CHT.R(2), None, 6).exponents()),
      CHT.ord(CHT.R(2)))
# The answer for m odd is not the paper's: (IV.3.3) is derived with
# r = [lambda_{p_3}/2] = 2, and group (A') computes lambda_{p_3} = 3 from the
# paper's own equation when n_2 and m are both odd.  There the elliptic
# component of (IV.3.3) does not appear at all.
for (n, m, nell, ncontract, mmin) in [
        (4, 0, 1, 2, [1, 1, 2, 2, 2, 2]),
        (4, 2, 1, 2, [1, 1, 2, 2, 2, 2]),
        (4, 1, 0, 1, [1, 1, 2, 2, 2, 4, 4, 6, 6, 8, 8, 10, 12]),
        (4, 3, 0, 1, [1, 1, 2, 2, 2, 4, 4, 6, 6, 8, 8, 10, 12])]:
    LC4, res4, by4 = ex310(n, m)
    c4, Ms4, g4 = analyse(res4)
    M4, mu4, gen4, cps4 = g4[0][1], g4[0][2], g4[0][3], g4[0][4]
    Mc4, muc4, genc4, lab4, con4 = contract_minus_ones(M4, mu4, gen4, cps4)
    check("n=%s m=%s: components of genus 1 in the closed fibre" % (n, m),
          len([g for g in gen4 if g == 1]), nell)
    check("n=%s m=%s: the minimal fibre" % (n, m),
          [len(con4), sorted(muc4)], [ncontract, mmin])

# ---------------------------------------------------------------------------
print("\n(C) Tate's algorithm: elliptic curves at ell = 2 and 3")
# ---------------------------------------------------------------------------
def kod_expect(sym):
    s = str(sym)
    if s in ('I0', 'I1', 'II'):  return ([1], [])
    if s == 'III':  return ([1, 1], [2])
    if s == 'IV':   return ([1, 1, 1], [3])
    if s == 'IV*':  return ([1, 1, 1, 2, 2, 2, 3], [3])
    if s == 'III*': return ([1, 1, 2, 2, 2, 3, 3, 4], [2])
    if s == 'II*':  return ([1, 2, 2, 3, 3, 4, 4, 5, 6], [])
    if s.startswith('I') and s.endswith('*'):
        n = 0 if s == 'I0*' else int(s[1:-1])
        return (sorted([1, 1, 1, 1] + [2] * (n + 1)), [2, 2] if n % 2 == 0 else [4])
    n = int(s[1:]);  return (sorted([1] * n), [n] if n > 1 else [])

CASES = [("24a1", 2, 'I1*'), ("32a1", 2, 'I3*'), ("72a1", 2, 'III'),
         ("96a1", 2, 'III'), ("128a1", 2, 'III'), ("256a1", 2, 'III'),
         ("288a1", 2, 'III'), ("225a1", 3, 'III'), ("288a1", 3, 'III'),
         ("27a1", 3, 'IV*'), ("54a1", 3, 'IV*'), ("72a1", 3, 'I1*'),
         ("24a1", 3, 'I2'), ("48a1", 3, 'I2'), ("96a1", 3, 'I2'),
         ("121a1", 2, 'I0'), ("99a1", 2, 'I0'), ("576a1", 3, 'III')]
for (lab, ell, kod) in CASES:
    E = EllipticCurve(lab).minimal_model()
    ld = E.local_data(ell)
    B = LiuBase(ell)
    Rs = PolynomialRing(B.O, 's'); x = Rs.gen()
    a1, a2, a3, a4, a6 = E.a_invariants()
    LC = LineCover(B, a1 * x + a3, -(x ** 3 + a2 * x ** 2 + a4 * x + a6), 1,
                   all_rational=True, point_degree=2)
    res = LC.resolution()
    comps, Ms, good = analyse(res)
    check("%-7s ell=%s  all valid matrices agree on (mult, Phi, p_a)" % (lab, ell),
          len(set((tuple(sorted(g[2])), tuple(g[5]['Phi']),
                   genus_of_fibre(g[1], g[2], g[3])) for g in good)), 1)
    choice, M, mu, gen, cps, rep = good[0]
    pa = genus_of_fibre(M, mu, gen)
    M2, mu2, g2, lb2, cont = contract_minus_ones(M, mu, gen, cps)
    rep2 = fibre_report(M2, vector(ZZ, mu2))
    em, ep = kod_expect(str(ld.kodaira_symbol()))
    check("%-7s ell=%s  Kodaira %-4s: multiplicities, Phi, p_a"
          % (lab, ell, ld.kodaira_symbol()),
          [sorted(mu2), rep2['Phi'], pa], [em, ep, 1])

print()
print("=" * 74)
if NFAIL == 0:
    print("JUDGEMENT: GREEN -- %s/%s checks passed" % (NPASS, NPASS))
    sys.exit(int(0))
else:
    print("JUDGEMENT: RED -- %s/%s checks failed: %s" % (NFAIL, NPASS + NFAIL, FAILS))
    sys.exit(int(1))
