# check-gamma-free.sage --- E135: throw Gamma_sigma away too.
#
# E135.  E133 replaced Balakrishnan--Dogra's
# correspondence class by a representative that does NOT contain Delta,
#
#     Z'_psi = Z_c - div(psi_1 - psi_2) = k Gamma_sigma - C_psi + (trivial),
#
# and got the local heights h_ell(z-b, D'(b,z)) EXACTLY -- but only at seven of
# the nine rational points of C_4.  Both survivors failed for the same reason:
# every such representative still CONTAINS Gamma_sigma, and
#
#     i_Delta^* Gamma_sigma = R  (the four sigma-fixed points, one of which is
#                                 the rational point (0,0)),
#     i_1^*     Gamma_sigma = (sigma b) .
#
# So z = (0,0) sits on Gamma_sigma diagonally, and z = sigma b = (1,-3) is hit
# through X_1.  Subtracting div(psi_1-psi_2) a second time cannot help: it would
# drive Delta's coefficient from 0 to -1, and a component of multiplicity -1 is
# still a component.  WHAT IS NEEDED IS A PRINCIPAL DIVISOR CONTAINING
# Gamma_sigma BUT NOT Delta.
#
# There is one.  For psi ANTI-invariant (psi o sigma = -psi, i.e. psi = w g with
# g in Q(E) = Q(X)^sigma) the function psi_1 + psi_2 vanishes on Gamma_sigma and
# not on Delta, and the automorphism id x sigma of X x X carries Delta to
# Gamma_sigma and {psi_1 = psi_2} to {psi_1 = -psi_2}, so it carries the
# multiplicity 1 of Delta in div(psi_1-psi_2) to Gamma_sigma:
#
#     div_0(psi_1 + psi_2) = Gamma_sigma + C''_psi ,   mult(Gamma_sigma) = 1.
#
# Hence, with Z'_t = 2 Gamma_sigma - C_2 + (trivial) from E133,
#
#     Z''_psi := Z'_t - 2 div(psi_1 + psi_2) = - C_2 - 2 C''_psi + (trivial),
#
# which contains NEITHER Delta NOR Gamma_sigma.  The three pullbacks are
#
#     i_Delta^* C''_psi = div_0(psi) + div_inf(psi) - R ,
#     i_x^*     C''_psi = psi^*(psi(sigma x)) - (sigma x)    (x = b or z).
#
# THE POLE TERM IS NOT DECORATION.  i_Delta^* of a divisor of ZEROS is not the
# divisor of zeros of the restriction: {psi_1 = -psi_2} passes through (P,P) at
# every pole P of psi, where the two poles cancel.  Without it deg D''(b,z) comes
# out as 2 deg psi instead of 0, and D''(b,z) reaches the place at infinity --
# which is why the direct Neron symbol here needs the projective chart
# (t : w : 1) = (1 : w/t : 1/t).
#
# WHAT THE GATE FINDS.  The resulting admissibility criterion is entirely local
# (group (A)), and solving it by hand gives a SINGLE representative admissible
# at ALL NINE points -- no per-point choice, which is what PLAN section 1-4
# had budgeted for:
#
#     psi = (t+3) w  :  Z''_{(t+3)w} is admissible for every one of the nine.
#
# and eight more like it.  With it, the last two local heights of E093 that were
# still measurements become exact:
#
#     q_3((0,0)) = 1/2 ,  q_2((0,0)) = -1/4 ,  q_ell(sigma b) = 0 .
#
# Every evaluation is done twice (the direct Neron symbol over the eight number
# fields of the closed points of D''; and D'' = div(g) + E_0 with E_0 on the nine
# rational points, run through the regular models of E125/E128--E130), and
# against up to five independent cycle representatives.
#
# Run:  sage check-gamma-free.sage       (a few minutes; no Magma)

import sys, time

load("liu-model-lib.sage")

FAIL = []
NCHECK = [0]


def check(cond, msg):
    NCHECK[0] += 1
    ok = bool(cond)
    print("   %s %s" % ("[ok] " if ok else "[FAIL]", msg))
    if not ok:
        FAIL.append(msg)
    sys.stdout.flush()
    return ok


def info(msg):
    print("       -- %s" % msg)
    sys.stdout.flush()


# ===========================================================================
# The curve, its nine rational points, sigma.
# ===========================================================================

Kt = FunctionField(QQ, 'T')
T = Kt.gen()
Rz = PolynomialRing(Kt, 'W')
W = Rz.gen()
KX = Kt.extension(W ** 4 - 6 * (T - 1) ** 2 * W ** 2 + 27 * T ** 4 - 108 * T, 'wf')
wf = KX.gen()
tf = KX(T)

PTS = [("(1,3)", QQ(1), QQ(3)), ("(1,-3)", QQ(1), QQ(-3)),
       ("(-1,3)", QQ(-1), QQ(3)), ("(-1,-3)", QQ(-1), QQ(-3)),
       ("(-2,6)", QQ(-2), QQ(6)), ("(-2,-6)", QQ(-2), QQ(-6)),
       ("(-1/11,15/11)", QQ(-1) / 11, QQ(15) / 11),
       ("(-1/11,-15/11)", QQ(-1) / 11, QQ(-15) / 11),
       ("(0,0)", QQ(0), QQ(0))]
NM = [n for (n, _, _) in PTS]
COORD = {n: (a, b) for (n, a, b) in PTS}
NAME = {(a, b): n for (n, a, b) in PTS}
SIGMA = {n: NAME[(COORD[n][0], -COORD[n][1])] for n in NM}
BNAME = "(1,3)"
PAIRS = [("(1,3)", "(1,-3)"), ("(-1,3)", "(-1,-3)"), ("(-2,6)", "(-2,-6)"),
         ("(-1/11,15/11)", "(-1/11,-15/11)")]


def pt_place(nm):
    t0, w0 = COORD[nm]
    for pl in (tf - t0).divisor_of_zeros().support():
        if pl.degree() != 1:
            continue
        L, frm, to = pl.residue_field()
        if QQ(to(wf)) == w0:
            return pl
    raise ValueError("no place for %s" % nm)


PLC = {n: pt_place(n) for n in NM}
PL = {n: PLC[n].divisor() for n in NM}
ZERO = 0 * PL[BNAME]
R_DIV = wf.divisor_of_zeros()                      # R = Fix(sigma) = div_0(w)
INF = tf.divisor_of_poles()
SIGHOM = KX.hom([-wf])                             # sigma on the function field


def val_at(f, nm):
    L, frm, to = PLC[nm].residue_field()
    try:
        return QQ(to(f))
    except (TypeError, ValueError):
        return None


def ordv(f, nm):
    """ord_nm(f): >0 a zero, <0 a pole, 0 a unit."""
    return f.valuation(PLC[nm])


def ram(psi, nm):
    c = val_at(psi, nm)
    if c is None:
        return psi.divisor_of_poles().multiplicity(PLC[nm])
    return (psi - KX(c)).divisor_of_zeros().multiplicity(PLC[nm])


# ---------------------------------------------------------------------------
# E133's representative Z'_psi = k Gamma_sigma - C_psi + (trivial).
# ---------------------------------------------------------------------------

class Rep(object):
    def __init__(self, psi, inv, name):
        self.psi, self.inv, self.name = psi, inv, name
        self.k = 2 if inv else 3
        self.Rpsi = psi.differential().divisor() + 2 * psi.divisor_of_poles()
        self.CD = self.Rpsi - (R_DIV if inv else ZERO)
        self._pull = {}

    def pull(self, nm):
        if nm not in self._pull:
            c = val_at(self.psi, nm)
            D = (self.psi - KX(c)).divisor_of_zeros() - PL[nm]
            if self.inv:
                D = D - PL[SIGMA[nm]]
            self._pull[nm] = D
        return self._pull[nm]

    def D(self, zn):
        Dv = self.k * R_DIV - self.CD
        for nm in (BNAME, zn):
            Dv = Dv - (self.k * PL[SIGMA[nm]] - self.pull(nm))
        return Dv

    def avoids_diagonal(self, zn):
        for nm in (BNAME, zn):
            if SIGMA[nm] == nm:
                return False
            if ram(self.psi, nm) != 1:
                return False
            if val_at(self.psi, nm) is None:
                return False
        return True

    def usable(self, zn):
        Dv = self.D(zn)
        return (self.avoids_diagonal(zn)
                and Dv.multiplicity(PLC[zn]) == 0
                and Dv.multiplicity(PLC[BNAME]) == 0)


REP_T = Rep(tf, True, "Z'_t")
REP_P = Rep(tf + 2 * wf, False, "Z'_{t+2w}")
USABLE133 = [n for n in NM if REP_T.usable(n)]


# ---------------------------------------------------------------------------
# E135's representative Z''_psi = - C_2 - 2 C''_psi + (trivial), psi anti-inv.
# ---------------------------------------------------------------------------

class Rep2(object):
    def __init__(self, psi, name):
        assert SIGHOM(psi) == -psi, "psi is not sigma-anti-invariant"
        self.psi, self.name = psi, name
        self.dpsi = psi.divisor_of_poles().degree()
        self.CD = psi.divisor_of_zeros() + psi.divisor_of_poles() - R_DIV
        self._pull, self._D = {}, {}

    def pull(self, nm):
        """i_x^*C''_psi = psi^*(psi(sigma x)) - (sigma x)."""
        s = SIGMA[nm]
        if s not in self._pull:
            c = val_at(self.psi, s)
            self._pull[s] = (self.psi - KX(c)).divisor_of_zeros() - PL[s]
        return self._pull[s]

    def D(self, zn):
        if zn not in self._D:
            Dv = -REP_T.CD - 2 * self.CD
            for nm in (BNAME, zn):
                Dv = Dv + REP_T.pull(nm) + 2 * self.pull(nm)
            self._D[zn] = Dv
        return self._D[zn]

    def avoids_diagonal(self, zn):
        for nm in (BNAME, zn):
            if REP_T.CD.multiplicity(PLC[nm]):
                return False
            if self.CD.multiplicity(PLC[nm]):
                return False
            if val_at(self.psi, nm) is None:
                return False
        return True

    def usable(self, zn):
        Dv = self.D(zn)
        return (self.avoids_diagonal(zn)
                and Dv.multiplicity(PLC[zn]) == 0
                and Dv.multiplicity(PLC[BNAME]) == 0)


REP_W2 = Rep2(wf, "Z''_w")
REP_TW2 = Rep2(tf * wf, "Z''_tw")
MASTER = Rep2((tf + 3) * wf, "Z''_{(t+3)w}")
ALT = Rep2((tf * tf - tf + 1) * wf, "Z''_{(t^2-t+1)w}")


# ===========================================================================
# (A)  STAGE 0 -- the admissibility criterion, and it is purely local.
# ===========================================================================

def coeff_local(psi, zn, x0):
    """the coefficient of (x0) in D''_psi(b,z), from LOCAL data only:
         D'' = -i_D^*C_2 - 2 i_D^*C'' + sum_{x in {b,z}} [i_x^*C_2 + 2 i_x^*C''],
         i_D^*C_2   = div_0(w^2 - 3(t-1)^2)              (E133 group (B)),
         i_D^*C''   = div_0(psi) + div_inf(psi) - R,
         i_x^*C_2   = t^*(t(x)) - (x) - (sigma x),
         i_x^*C''   = psi^*(psi(sigma x)) - (sigma x),  psi(sigma x) = -psi(x)."""
    tx0 = COORD[x0][0]
    c = -ordv(wf ** 2 - 3 * (tf - 1) ** 2, x0)
    c -= 2 * (abs(ordv(psi, x0)) - ordv(wf, x0))
    for x in (BNAME, zn):
        c += (ordv(tf - COORD[x][0], x0) - (1 if x0 == x else 0)
              - (1 if x0 == SIGMA[x] else 0))
        c += 2 * (ordv(psi + val_at(psi, x), x0) - (1 if x0 == SIGMA[x] else 0))
    return c


def usable_local(psi, zn):
    """PLAN section 1-2's criterion, made complete and stated locally."""
    for x in (BNAME, zn):
        if val_at(psi, x) is None:
            return False
        tx, wx = COORD[x]
        if wx ** 2 == 3 * (tx - 1) ** 2:            # (x,x) in C_2
            return False
        if ordv(psi, x) != (1 if SIGMA[x] == x else 0):   # (x,x) in C''_psi
            return False
    return all(coeff_local(psi, zn, x0) == 0 for x0 in (BNAME, zn))


def group_A(FAMILY):
    print("(A) STAGE 0: THE ADMISSIBILITY CRITERION IS LOCAL, AND IT IS RIGHT")
    info("Balakrishnan--Dogra QC1 section 6.4 asks that Z meet X_1, X_2, Delta "
         "properly AND avoid (b,b) and (z,z); E133 group (A) showed the second "
         "clause is what makes the local height representative-independent, and "
         "measured the failure when it is dropped.  For Z''_psi the whole clause "
         "-- together with |D''(b,z)| avoiding {z,b} -- reduces to orders of "
         "explicit functions at rational points:")
    info("   (x,x) not in C_2      <=>  w(x)^2 != 3(t(x)-1)^2 ,")
    info("   (x,x) not in C''_psi  <=>  ord_x(psi) = ord_x(R)  [= 1 at a "
         "sigma-fixed x, 0 elsewhere] ,")
    info("   and coeff_{x_0} D''  =  -ord(w^2-3(t-1)^2) - 2[ord(psi) - ord(w)] "
         "+ sum_{x in {b,z}} ( [ord(t-t(x)) - 1_{x_0=x} - 1_{x_0=sigma x}] "
         "+ 2[ord(psi+psi(x)) - 1_{x_0=sigma x}] ).")
    info("PLAN section 1-2 had only the two diagonal conditions and the single "
         "coefficient e_psi(sigma b) = 1.  The complete criterion has one more "
         "term, ord_{x_0}(psi + psi(x)) with x the OTHER point: psi(z) = -psi(b) "
         "puts b into i_2^*C''_psi.  That is why psi = w fails at t = -1 as well "
         "as at sigma b (w(-1,-3) = -3 = -w(b)), and why psi = tw fails at "
         "(-1,3).  The gate checks the criterion against the divisors, not the "
         "other way round.")
    n_agree, n_true = 0, 0
    for (nm_, rep) in FAMILY:
        for zn in NM:
            a = usable_local(rep.psi, zn)
            b = rep.usable(zn)
            if a != b:
                check(False, "   criterion disagrees: %s at z=%s (local %s, "
                             "divisor %s)" % (nm_, zn, a, b))
            n_agree += 1
            n_true += 1 if b else 0
    check(True, "*** the local criterion and the full divisor computation agree "
                "in ALL %d cases (%d family members x 9 points), %d of them "
                "admissible.  The criterion is not a restatement: the left side "
                "reads five valuations at rational points, the right side builds "
                "D''(b,z) as a divisor on the function field and inspects its "
                "support ***" % (n_agree, len(FAMILY), n_true))
    check(sorted(USABLE133) == sorted([n for n in NM
                                       if n not in ("(0,0)", SIGMA[BNAME])]),
          "and for the record E133's Z'_t is admissible at exactly the seven "
          "points it reported, the missing two being z = (0,0) and z = sigma b")
    for rep, want in [(REP_W2, "(0,0)"), (REP_TW2, SIGMA[BNAME])]:
        check(rep.usable(want) and not REP_T.usable(want),
              "*** %s IS admissible at z = %s, where every E133 representative "
              "failed ***" % (rep.name, want))


# ===========================================================================
# (B)  STAGE 1 -- div(psi_1 + psi_2) = Gamma_sigma + C''_psi.
# ===========================================================================

def group_B(FAMILY):
    print("(B) STAGE 1: div(psi_1+psi_2) = Gamma_sigma + C''_psi, MULTIPLICITY 1")
    info("psi o sigma = -psi, so (psi_1+psi_2)(P,sigma P) = psi(P) - psi(P) = 0: "
         "Gamma_sigma is a component.  Delta is not, because (psi_1+psi_2)|_Delta "
         "= 2 psi, not identically 0.")
    for (nm_, rep) in FAMILY:
        check(SIGHOM(rep.psi) == -rep.psi and rep.psi != 0,
              "   %-22s psi o sigma = -psi and psi != 0" % nm_)
    check(SIGHOM(tf) == tf and SIGHOM(wf) == -wf,
          "   (sigma is w -> -w, and t generates the invariants Q(E))")
    info("tau = id x sigma is an automorphism of X x X with tau(Delta) = "
         "Gamma_sigma and (psi_1+psi_2) o tau = psi_1 - psi_2.  So tau carries "
         "div(psi_1-psi_2) to div(psi_1+psi_2) MULTIPLICITY BY MULTIPLICITY, and "
         "the multiplicity 1 of Delta in the first (E133 group (B): the factors "
         "of the fibre polynomial are pairwise coprime) becomes the multiplicity "
         "1 of Gamma_sigma in the second.  [T]")
    info("i_Delta^* and i_x^* of it.  For a rational function F on X x X whose "
         "restriction is neither 0 nor identically infinite, i^*div(F) = "
         "div(F|). Restricting psi_1+psi_2:")
    info("   to Delta      : 2 psi          -> i_Delta^* div(psi_1+psi_2) = div(psi)")
    info("   to {b} x X    : psi + psi(b)   -> i_1^* div(psi_1+psi_2) = "
         "div(psi - psi(sigma b))")
    info("The POLE divisor is pr_1^*div_inf(psi) + pr_2^*div_inf(psi) (the two "
         "families of components are distinct, so no cancellation), whence")
    info("   i_Delta^* div_0(psi_1+psi_2) = div(psi) + 2 div_inf(psi) "
         "= div_0(psi) + div_inf(psi),")
    info("   i_1^*     div_0(psi_1+psi_2) = div(psi-psi(sigma b)) + div_inf(psi) "
         "= psi^*(psi(sigma b))   (b not a pole).")
    info("Subtracting i_Delta^*Gamma_sigma = R (Delta and Gamma_sigma meet "
         "transversally at each fixed point, where d(sigma) = -1) and "
         "i_1^*Gamma_sigma = (sigma b) (Gamma_sigma is a graph, so it meets every "
         "fibre once, transversally) gives the two boxed formulas.  [T]")
    for (nm_, rep) in FAMILY:
        d = rep.dpsi
        check(rep.psi.divisor_of_zeros().degree() == d
              and rep.CD.degree() == 2 * d - 4,
              "   %-22s deg psi = %-2s, deg i_Delta^*C'' = %-2s = 2 deg psi - 4 "
              "= (Gamma_sigma + C'').Delta - Gamma_sigma.Delta" % (nm_, d, 2 * d - 4))
        for nm in (BNAME, "(-2,6)"):
            check(rep.pull(nm).degree() == d - 1,
                  "   %-22s deg i_x^*C'' = %s = deg psi - 1 at x = %s"
                  % (nm_, d - 1, nm))
    info("*** THE POLE TERM IS LOAD-BEARING.  Drop div_inf(psi) from i_Delta^*C'' "
         "and deg D''(b,z) comes out 2 deg psi instead of 0.  Geometrically "
         "{psi_1 = -psi_2} passes through (P,P) at every pole P of psi, where "
         "the two poles cancel; PLAN section 1-2 wrote the criterion only for "
         "non-poles and so did not see it. ***")
    for (nm_, rep) in FAMILY:
        bad = [zn for zn in NM if rep.D(zn).degree() != 0]
        check(not bad, "   %-22s deg D''(b,z) = 0 at all nine z" % nm_)
    check(R_DIV.degree() == 4 and R_DIV == SIGHOM(wf).divisor_of_zeros(),
          "R = div_0(w) has degree 4: the four fixed points of sigma, of which "
          "(0,0) is the only rational one")


# ===========================================================================
# (C)  The class is unchanged: [Z''] = [Z_c], m = 0, D'' - D' principal.
# ===========================================================================

def gF(rep, zn):
    """THE CONNECTING FUNCTION, EXPLICITLY.  Z''_psi = Z'_t - 2 div(F) with
    F = psi_1 + psi_2, and D of a principal divisor is
        D(div F) = div( F|_Delta / [(F o i_1)(F o i_2)] ),
    whose three restrictions are 2 psi, psi(b) + psi and psi + psi(z).  So

        D''_psi(b,z) - D'_t(b,z) = -2 div(g_F),
        g_F = 2 psi / [ (psi + psi(b)) (psi + psi(z)) ] .

    No Riemann--Roch is needed anywhere: the function is written down."""
    psi = rep.psi
    return (2 * psi / ((psi + KX(val_at(psi, BNAME)))
                       * (psi + KX(val_at(psi, zn)))))


def principal(A):
    if A.degree() != 0 or A.dimension() < 1:
        return None
    bs = A.basis_function_space()
    if len(bs) != 1:
        return None
    g = 1 / bs[0]
    return g if g.divisor() == A else None


def group_C(FAMILY):
    print("(C) THE CLASS IS UNCHANGED: [Z''] = [Z'] = [Z_c], AND m'' = 0")
    info("Z''_psi = Z'_t - 2 div(psi_1+psi_2) differs from E133's cycle by a "
         "PRINCIPAL divisor on X x X, so it induces the same map on divisor "
         "classes and has the same intersection numbers with X_1, X_2, Delta.  "
         "In particular m = Z.(X_1+X_2-Delta) = 0 is inherited from E127(a), and "
         "no basepoint term appears.")
    dD, gsD, c2D, trivD = -4, 4, 8, 4 + 4
    zc = {'X1': 1 + 3, 'X2': 1 + 3, 'D': dD + 3 * gsD}
    check(zc['X1'] + zc['X2'] - zc['D'] == 0,
          "   Z_c = Delta + 3 Gamma_sigma has m = %s + %s - %s = 0"
          % (zc['X1'], zc['X2'], zc['D']))
    for (nm_, rep) in FAMILY:
        d = rep.dpsi
        # Z'' = -C_2 - 2 C'' + (trivial):  trivial = pr_i^*(INF) + 2 pr_i^*div_inf(psi)
        x1 = -2 - 2 * (d - 1) + (4 + 2 * d)
        x2 = x1
        dd = -c2D - 2 * (2 * d - 4) + trivD + 2 * 2 * d
        check(x1 == zc['X1'] and x2 == zc['X2'] and dd == zc['D'],
              "   %-22s Z''.X_1 = %s, Z''.X_2 = %s, Z''.Delta = %s -- the same "
              "three numbers as Z_c, so m'' = 0" % (nm_, x1, x2, dd))
    info("and the connecting function is EXPLICIT.  D of a principal divisor "
         "div(F) is div( F|_Delta / [(F o i_1)(F o i_2)] ), and F = psi_1+psi_2 "
         "restricts to 2 psi, psi(b)+psi, psi+psi(z), so")
    info("      D''_psi(b,z) - D'_t(b,z) = -2 div(g_F),   "
         "g_F = 2 psi / [(psi + psi(b))(psi + psi(z))] .")
    nprin = 0
    for (nm_, rep) in FAMILY:
        for zn in NM:
            A = rep.D(zn) - REP_T.D(zn)
            ok = (A == -2 * gF(rep, zn).divisor())
            check(ok, "   %-22s z=%-15s D'' - D' = -2 div(g_F), as divisors"
                      % (nm_, zn))
            nprin += 1 if ok else 0
    check(nprin == len(FAMILY) * 9,
          "*** all %d differences D'' - D' are EXHIBITED as -2 div(g_F): the "
          "moved cycle computes the SAME divisor class, which is why stages "
          "3a/3b test the geometry and not the bookkeeping.  This is stronger "
          "than a Riemann--Roch existence test, and it re-derives the three "
          "pullback formulas of group (B) independently -- if any of them were "
          "wrong the identity would fail ***" % nprin)
    nrr = 0
    for (nm_, rep) in FAMILY[:1]:
        for zn in ("(0,0)", SIGMA[BNAME]):
            g = principal(rep.D(zn) - REP_T.D(zn))
            ok = g is not None and g.divisor() == -2 * gF(rep, zn).divisor()
            check(ok, "   %-22s z=%-15s Riemann--Roch over Q finds the same "
                      "function (independent route)" % (nm_, zn))
            nrr += 1


# ===========================================================================
# (D)  STAGE 2 -- the admissibility table, and the single representative.
# ===========================================================================

def group_D(FAMILY, SINGLE):
    print("(D) STAGE 2: WHICH REPRESENTATIVES ARE ADMISSIBLE WHERE")
    print("      %-24s %s" % ("representative", "".join("%-8s" % COORD[n][0]
                                                        for n in NM)))
    rows = [("Z'_t (E133)", REP_T), ("Z'_{t+2w} (E133)", REP_P)] + \
           [(nm_, r) for (nm_, r) in FAMILY]
    for nm_, rep in rows:
        print("      %-24s %s" % (nm_, "".join(
            "%-8s" % ("ok" if rep.usable(n) else "--") for n in NM)))
    sys.stdout.flush()
    check(not REP_T.usable("(0,0)") and not REP_T.usable(SIGMA[BNAME])
          and not REP_P.usable("(0,0)") and not REP_P.usable(SIGMA[BNAME]),
          "E133's two representatives fail at exactly z = (0,0) and z = sigma b")
    check(all(MASTER.usable(zn) for zn in NM),
          "*** %s IS ADMISSIBLE AT ALL NINE POINTS.  PLAN section 1-4 budgeted "
          "for a per-point choice of representative (Z''_w at (0,0), Z''_tw at "
          "sigma b) because section 1-3 found no single psi; solving the "
          "criterion of group (A) instead of guessing gives one ***" % MASTER.name)
    check(len(SINGLE) >= 5,
          "   and it is not isolated: %d of the tested psi = h(t) w are "
          "admissible at all nine, namely h = %s"
          % (len(SINGLE), ", ".join(h for (h, _) in SINGLE)))
    info("the criterion explains the failures exactly: psi = h(t) w is "
         "admissible everywhere iff h(t_x) != 0 at the five t-values, h'(1) != 0 "
         "(so that e_psi(b) = 1), and w(z)^2 h(t_z)^2 != w(b)^2 h(1)^2 for "
         "t_z = -1, -2, -1/11.  h = t-1 fails everywhere (psi(b) = 0); h = t+5 "
         "fails only at t = -2 because 36*9 = 9*36; h = t fails at (0,0) and "
         "(-1,3) as PLAN section 1-3 found.")
    info("Gamma_sigma and Delta are both absent from Z''_psi = -C_2 - 2C''_psi "
         "+ (trivial): Delta is not a component of div(psi_1+psi_2) nor of "
         "div(t_1-t_2) - Delta - Gamma_sigma - (trivial) = C_2, and Gamma_sigma "
         "cancels between 2 Gamma_sigma and 2 div(psi_1+psi_2).")


# ===========================================================================
# Evaluation (1): the direct Neron symbol at a good prime.
# ===========================================================================

def vval(x, ell):
    return Infinity if x == 0 else QQ(x).valuation(ell)


_PC, _PA = {}, {}


def proj_coords(pl):
    """(X:Y:Z) = (t:w:1) at the closed point pl, scaled to be regular and
    nonzero -- D''(b,z) reaches the place at infinity, where (t:w:1) =
    (1 : w/t : 1/t) and w/t tends to a root of y^4 - 6y^2 + 27.

    The dict is a convenience, not a speedup: Sage already caches
    pl.residue_field() (it hands back the SAME object, and maximal_order is
    computed once per field and then free -- measured).  What is genuinely
    expensive is that ONE maximal_order call, 5.5 s for a degree-11 residue
    field here and over a minute for the worst of them, and no caching removes
    it.  That is why method (1) is capped by deg psi in group (E) instead."""
    if pl in _PC:
        return _PC[pl]
    L, frm, to = pl.residue_field()
    for s in (KX(1), 1 / tf, 1 / wf, tf / wf, wf / tf, 1 / (tf * wf)):
        try:
            v = [to(s * tf), to(s * wf), to(s)]
        except (TypeError, ValueError, ZeroDivisionError):
            continue
        if any(a != 0 for a in v):
            _PC[pl] = (L, v)
            return _PC[pl]
    raise ValueError("no projective chart at %s" % pl)


PLIST = [2, 3] + [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]


def integral_model(L):
    """a monic INTEGRAL G with root m*theta, theta the generator of L.

    L.defining_polynomial() is monic but not always integral (three of the
    residue fields here are not), and it is not L.pari_polynomial() either, so
    an element's coefficient vector may NOT be fed to an nf built on the latter
    -- that would return wrong valuations silently.  G(Y) = m^n g(Y/m)."""
    g = L.defining_polynomial()
    n = g.degree()
    assert g.is_monic(), "defining polynomial is not monic"
    m = ZZ(1)
    for i in range(n):
        c = QQ(g[i])
        if c == 0:
            continue
        for (pp, e) in ZZ(c.denominator()).factor():
            k = -(-e // (n - i))                       # ceil(e/(n-i))
            m = m * pp ** max(0, k - m.valuation(pp))
    Ry = PolynomialRing(QQ, 'y')
    Y = Ry.gen()
    G = Ry(m ** n * g(Y / m))
    assert G.is_monic() and all(a in ZZ for a in G.list()), "G is not integral"
    return G, m


_NF = {}


def nf_of(pl, L):
    """nfinit([G, PLIST]): an order maximal ONLY at the primes we evaluate at.

    This is the point of routing through PARI.  Sage's primes_above always
    builds the FULL ring of integers, whose cost is the factorisation of the
    polynomial discriminant -- 6 s at 332 bits, over 600 s at 3261 bits, and
    with no bound in general.  The restricted order needs no factorisation at
    all: under a second at the worst closed point.

    WHY THE SUBSTITUTION IS LEGITIMATE.  An order O with O (x) Z_p = O_K (x) Z_p
    ("p-maximal", equivalently p does not divide [O_K : O]) has the same
    semilocal ring at p as O_K.  Hence the primes above p correspond
    bijectively, with the same e and f, and for x in K^* the valuation v_P(x)
    -- determined by the completion K_P, which depends only on that
    localisation -- is unchanged.  [T]

    NOTHING GLOBAL IS INHERITED: the class group, the unit group, and the
    factorisation of primes OUTSIDE PLIST may all be wrong, and PARI warns that
    an uncertified nf "may cause routines using it to fail randomly".  We use
    only idealprimedec and nfeltval, and only at primes in PLIST.  delta_orbit
    asserts that at the point of use, and group (E2) certifies the p-maximality
    itself with nfcertify."""
    if pl not in _NF:
        G, m = integral_model(L)
        _NF[pl] = (pari.nfinit([G, PLIST]), m)
    return _NF[pl]


def to_pari(a, m):
    Ry = PolynomialRing(QQ, 'y')
    Y = Ry.gen()
    return pari(Ry(a.polynomial()(Y / m)))


def primes_above(pl, L, ell):
    key = (pl, ell)
    if key not in _PA:
        _PA[key] = [(Pp, Pp.residue_class_degree()) for Pp in L.primes_above(ell)]
    return _PA[key]


def delta_orbit(P, pl, ell):
    """sum over the primes above ell of f_P times the Neron symbol, via the
    restricted order.  delta_orbit_sage below is the answer key."""
    tP, wP = P
    L, v = proj_coords(pl)
    if L is QQ or L == QQ:
        u = [QQ(tP), QQ(wP), QQ(1)]
        v = [QQ(a) for a in v]
        mn = [u[i] * v[j] - u[j] * v[i] for i in range(3) for j in range(i + 1, 3)]
        return (min(vval(m, ell) for m in mn)
                - min(vval(a, ell) for a in u) - min(vval(a, ell) for a in v))
    assert ell in PLIST, (
        "ell = %s is not in PLIST: the order is maximal only at PLIST, so a "
        "valuation at any other prime would be silently wrong" % ell)
    nf, m = nf_of(pl, L)
    u = [L(tP), L(wP), L(1)]
    mn = [u[i] * v[j] - u[j] * v[i] for i in range(3) for j in range(i + 1, 3)]
    up, vp, mp = [[to_pari(a, m) for a in lst if a != 0] for lst in (u, v, mn)]
    assert up and vp and mp, "a coordinate vector vanished identically"
    tot = 0
    for pr in nf.idealprimedec(ell):
        f = ZZ(pr[3])
        tot += f * (min(ZZ(nf.nfeltval(a, pr)) for a in mp)
                    - min(ZZ(nf.nfeltval(a, pr)) for a in up)
                    - min(ZZ(nf.nfeltval(a, pr)) for a in vp))
    return tot


def delta_orbit_sage(P, pl, ell):
    tP, wP = P
    L, v = proj_coords(pl)
    if L is QQ or L == QQ:
        u = [QQ(tP), QQ(wP), QQ(1)]
        v = [QQ(a) for a in v]
        mn = [u[i] * v[j] - u[j] * v[i] for i in range(3) for j in range(i + 1, 3)]
        return (min(vval(m, ell) for m in mn)
                - min(vval(a, ell) for a in u) - min(vval(a, ell) for a in v))
    u = [L(tP), L(wP), L(1)]
    tot = 0
    for (Pp, f) in primes_above(pl, L, ell):

        def ov(a, Pp=Pp):
            return Infinity if a == 0 else a.valuation(Pp)
        mn = [u[i] * v[j] - u[j] * v[i] for i in range(3) for j in range(i + 1, 3)]
        tot += f * (min(ov(a) for a in mn)
                    - min(ov(a) for a in u) - min(ov(a) for a in v))
    return tot


def height_direct(rep, zn, ell):
    tot = 0
    for pl, m in rep.D(zn).list():
        if m == 0:
            continue
        tot += m * (delta_orbit(COORD[zn], pl, ell)
                    - delta_orbit(COORD[BNAME], pl, ell))
    return tot


# ===========================================================================
# Evaluation (2): D''(b,z) = div(g) + E_0, E_0 on the nine rational points.
# ===========================================================================

GENS = [(1, 1, 0, 0, 2, 2, -1, -1, -4), (0, 2, 0, 6, 0, 2, -2, -2, -6),
        (0, 0, 1, 1, 1, 1, -1, -1, -2), (0, 0, 0, 8, 2, 6, -4, -4, -8),
        (0, 0, 0, 0, 4, 4, -2, -2, -4)]
LAT = matrix(ZZ, GENS)
SIGA = [(1, 1, 1, 0, 2), (1, 0, 0, 1, 4), (2, 2, 0, 0, 0), (1, 2, 2, -1, 0)]


def sigvec(a):
    v = [0] * 9
    for i, (p, q) in enumerate(PAIRS):
        v[NM.index(p)] += a[i]
        v[NM.index(q)] += a[i]
    v[NM.index("(0,0)")] += a[4]
    return vector(ZZ, v)


def dvec(v):
    return sum((ZZ(v[i]) * PL[NM[i]] for i in range(9)), ZERO)


_RR = {}


def rational_reps(rep, zn, nmax=4):
    """(tag, E_0, g) with div(g) = D''_psi(b,z) - E_0.  The auxiliary divisor
    E_0 and the connecting function for E133's D'_t are computed ONCE per z (the
    only Riemann--Roch in the gate) and then transported to every Z''_psi by
    g = g' / g_F^2, since D'' - D' = -2 div(g_F)."""
    out = []
    for (tag, E0, gp) in e0_reps(zn, nmax):
        g = gp / gF(rep, zn) ** 2
        if g.divisor() != rep.D(zn) - E0:
            check(False, "transport of E_0 failed for %s at z=%s"
                         % (rep.name, zn))
            continue
        out.append((tag, E0, g))
    return out


def e0_reps(zn, nmax=4):
    if zn not in _RR:
        _RR[zn] = _rational_reps(REP_T, zn, nmax)
    return _RR[zn]


def _rational_reps(rep, zn, nmax):
    """E_0 on the nine rational points, avoiding z and b, with
    div(g) = D''(b,z) - E_0.  E133 used a fixed list of four candidates; for
    z = sigma b none of them avoids {z,b}, so we solve the two integrality
    conditions in the relation lattice instead."""
    ib, iz = NM.index(BNAME), NM.index(zn)
    Dv = rep.D(zn)
    M = matrix(ZZ, [[LAT[i, ib], LAT[i, iz]] for i in range(LAT.nrows())])
    base_v, g0 = None, None
    for a in SIGA:
        u = sigvec(a)
        u[ib] -= 1
        u[NM.index(SIGMA[BNAME])] -= 3
        u[iz] -= 1
        u[NM.index(SIGMA[zn])] -= 3
        try:
            c = M.solve_left(vector(ZZ, [-u[ib], -u[iz]]))
        except ValueError:
            continue
        if any(x not in ZZ for x in c):
            continue
        w = u + vector(ZZ, [ZZ(x) for x in c]) * LAT
        if w[ib] or w[iz]:
            continue
        g = principal(Dv - dvec(w))
        if g is None:
            continue
        base_v, g0 = w, g
        break
    if base_v is None:
        return []
    out = [("base", dvec(base_v), g0)]
    K = M.kernel().basis_matrix()
    if K.nrows():
        S = (K * LAT).LLL()
        rows = sorted((r for r in S.rows() if r != 0),
                      key=lambda r: max(abs(c) for c in r))
        rows = [r for r in rows if max(abs(c) for c in r) <= 8]
        for r in rows[:nmax - 1]:
            w = base_v + r
            g = principal(Dv - dvec(w))
            if g is not None:
                out.append(("+rel" + str(list(r)), dvec(w), g))
    return out


def gval(g, nm, ell):
    return val_at(g, nm).valuation(ell)


def plane_contact(n1, n2, ell):
    if n1 == n2:
        return None
    t1, w1 = COORD[n1]
    t2, w2 = COORD[n2]
    u = [t1, w1, QQ(1)]
    v = [t2, w2, QQ(1)]
    mn = [u[i] * v[j] - u[j] * v[i] for i in range(3) for j in range(i + 1, 3)]
    return (min(vval(m, ell) for m in mn)
            - min(vval(a, ell) for a in u) - min(vval(a, ell) for a in v))


# ===========================================================================
# (E)  STAGE 3a -- the good primes, where the answer is known to be 0.
# ===========================================================================

GOOD = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
SAGE_BUDGET = 90        # seconds allowed to the answer-key route per place

def group_E(FAMILY):
    print("(E) STAGE 3a: THE GOOD PRIMES -- h_ell(z-b,D''(b,z)) MUST BE 0")
    info("Balakrishnan--Dogra QC1 Theorem 1.2(i): h_v vanishes at a prime of "
         "potential good reduction.  This runs BEFORE ell = 2, 3 (Commandment "
         "II): the answer here is known in advance and independent of E093.")
    info("method (1) runs for EVERY representative, including deg psi = 12.  It "
         "used to be capped at deg psi <= 8 because Sage's primes_above builds "
         "the full ring of integers, whose cost is factoring the polynomial "
         "discriminant: 6 s at 332 bits and over 600 s at 3261 bits, with no "
         "bound in general.  Routing through PARI's nfinit([G, PLIST]) -- an "
         "order maximal only at the primes we evaluate at -- removes the "
         "factorisation entirely (0.7 s worst case) and the cap with it.")
    n1, n2, bad1, bad2, nz, skipped = 0, 0, [], [], 0, []
    for (nm_, rep) in FAMILY:
        t0 = time.time()
        for zn in NM:
            if zn == BNAME or not rep.usable(zn):
                continue
            reps = rational_reps(rep, zn)
            for ell in GOOD:
                h = height_direct(rep, zn, ell)
                n1 += 1
                if h != 0:
                    bad1.append((nm_, zn, ell, h))
                for pl, m in rep.D(zn).list():
                    if m and (delta_orbit(COORD[zn], pl, ell)
                              or delta_orbit(COORD[BNAME], pl, ell)):
                        nz += 1
            for ell in GOOD:
                for (tag, E0, g) in reps:
                    tot = gval(g, zn, ell) - gval(g, BNAME, ell)
                    for n in NM:
                        c = E0.multiplicity(PLC[n])
                        if c:
                            tot += c * (plane_contact(zn, n, ell)
                                        - plane_contact(BNAME, n, ell))
                    n2 += 1
                    if tot != 0:
                        bad2.append((nm_, zn, ell, tag, tot))
        print("       [%-22s %.0f s]" % (nm_, time.time() - t0))
        sys.stdout.flush()
    check(not bad1,
          "*** METHOD (1) (direct Neron symbol): h_ell = 0 EXACTLY in all %d "
          "evaluations, over the %d good primes up to 43 and EVERY admissible "
          "(representative, z) pair -- with %d nonzero orbit contributions, so "
          "the test is not vacuous ***" % (n1, len(GOOD), nz))
    check(not bad2,
          "*** METHOD (2) (D'' = div(g) + E_0 on the nine rational points) "
          "agrees in all %d evaluations.  Below the divisor arithmetic the two "
          "share no code: (1) works with the closed points of D'' over eight "
          "number fields and the place at infinity, (2) replaces D'' by a "
          "function and a rational divisor ***" % n2)
    if bad1:
        info("   method (1) failures: %s" % (bad1[:6],))
    if bad2:
        info("   method (2) failures: %s" % (bad2[:6],))


def group_E2(FAMILY):
    print("(E2) THE RESTRICTED ORDER AGAINST SAGE's FULL RING OF INTEGERS")
    info("delta_orbit sums over idealprimedec of an order maximal only at "
         "PLIST.  That is a different object from Sage's maximal order, so it "
         "is checked against it at every closed point where Sage's route "
         "finishes inside a %d s budget.  Sage is the ANSWER KEY here, not the "
         "source." % SAGE_BUDGET)
    info("the budget is measured, not predicted: the cost of Sage's route is "
         "the factorisation of a discriminant, and no cheap feature of the "
         "place forecasts it -- an earlier version of this group tried to "
         "guess from the discriminant's bit length and picked wrong, because "
         "the integral model's discriminant is m^{n(n-1)} times the one that "
         "matters.")
    places, seen = [], set()
    for (nm_, rep) in FAMILY:
        for zn in NM:
            for pl, m in rep.D(zn).list():
                if not m or pl in seen:
                    continue
                seen.add(pl)
                L, _v = proj_coords(pl)
                if L is QQ or L == QQ:
                    continue
                places.append((L.degree(), pl, L))
    places.sort(key=lambda r: r[0])
    ncert, uncert = 0, []
    for d, pl, L in places:
        nf, _m = nf_of(pl, L)
        ents = [ZZ(x) for x in nf.nfcertify()]
        bad = [(ell, e) for ell in PLIST for e in ents if e % ell == 0]
        if bad:
            uncert.append((d, bad))
        ncert += 1
    check(not uncert,
          "*** p-MAXIMALITY CERTIFIED at every prime we evaluate at, for all %d "
          "closed points: no prime of PLIST divides any entry of nfcertify(nf). "
          "That is PARI's own criterion -- idealprimedec is trustworthy at a "
          "prime not dividing an entry of that output -- so the restricted "
          "order gives the same primes above ell, with the same e and f, and "
          "the same valuations, as the true ring of integers.  Under 1 ms "
          "each ***" % ncert)
    info("what is NOT inherited: the class group, the unit group, and the "
         "factorisation of primes outside PLIST.  The gate uses none of them, "
         "and delta_orbit asserts ell in PLIST at the point of use.")
    nag, ndis, nnz, hard = 0, 0, 0, []
    for d, pl, L in places:
        vals = [(zn, ell, delta_orbit(COORD[zn], pl, ell))
                for zn in NM for ell in GOOD]
        nnz += sum(1 for (_z, _e, a) in vals if a != 0)
        t0 = time.time()
        try:
            alarm(SAGE_BUDGET)
            for (zn, ell, a) in vals:
                b = delta_orbit_sage(COORD[zn], pl, ell)
                if a == b:
                    nag += 1
                else:
                    ndis += 1
                    check(False, "   MISMATCH deg %s z=%s ell=%s: restricted "
                                 "%s, Sage %s" % (d, zn, ell, a, b))
            cancel_alarm()
        except AlarmInterrupt:
            cancel_alarm()
            hard.append(d)
            info("   degree %-3s Sage's answer-key route did not finish in "
                 "%d s; the restricted order evaluated all %d values"
                 % (d, SAGE_BUDGET, len(vals)))
    check(ndis == 0 and nag > 3000,
          "*** the restricted order reproduces Sage's ring of integers in ALL "
          "%d comparisons (%d of the %d closed points x nine z x %d good "
          "primes), with %d nonzero values over all points so the check is not "
          "vacuous ***"
          % (nag, len(places) - len(hard), len(places), len(GOOD), nnz))
    check(len(hard) > 0,
          "*** and it evaluates the %d closed point(s) Sage cannot reach at all "
          "(degree %s): there its route must factor a polynomial discriminant "
          "of over 3200 bits, which did not finish in 600 s in a separate "
          "measurement and need not finish at all.  The restricted order needs "
          "no factorisation ***"
          % (len(hard), ", ".join(str(x) for x in hard)))


# ===========================================================================
# (F)  STAGE 3b -- ell = 3, then ell = 2.
# ===========================================================================

def build_round1(ell, hpoly=None):
    B = LiuBase(ell) if hpoly is None else LiuBase(ell, hpoly)
    Rs = PolynomialRing(B.O, 's')
    t = Rs.gen()
    secs = [(nm, t0, w0 ** 2, w0) for (nm, t0, w0) in PTS]
    LC = LineCover(B, -6 * (t - 1) ** 2, 27 * t * (t ** 3 - 4), 1,
                   sections=secs, all_rational=False, next_cover=True)
    return LC, LC.resolution()


def section_nodes(res2):
    out = {}
    for nd in res2.regular:
        for Pt in nd.pts:
            assert Pt.name not in out, "the section %s is tracked twice" % Pt.name
            out[Pt.name] = (nd, Pt)
    return out


def build_models():
    MODELS = {}
    for ell, hp, P in [(3, PolynomialRing(QQ, 'th').gen() ** 2 + 1, 12),
                       (2, None, 10)]:
        t0 = time.time()
        LC, res1 = build_round1(ell, hp)
        res2, lab, eps = round2(res1, P=P)
        comps, Ms, good = analyse(res2, P=P)
        assert len(good) == 1, "ell = %s: %s matrices" % (ell, len(good))
        ch, M, mu, gen, cps, rep = good[0]
        pc = point_components(res2, cps, P=P)
        base = pc[BNAME]['comp']
        sbase = pc[SIGMA[BNAME]]['comp']
        rest = sorted(set(pc[nm]['comp'] for nm in NM) - {base, sbase})
        order = [base, sbase] + rest
        MODELS[ell] = {'M': M, 'mu': mu, 'pc': pc, 'sec': section_nodes(res2),
                       'Lam': local_pairing(M, mu, order, base),
                       'cls': {nm: order.index(pc[nm]['comp']) for nm in NM}}
        print("   [regular model at ell = %d built in %.0f s]"
              % (ell, time.time() - t0))
        sys.stdout.flush()
    return MODELS


def contact(MODELS, ell, n1, n2):
    if n1 == n2:
        return None
    sec, pc = MODELS[ell]['sec'], MODELS[ell]['pc']
    if (pc[n1]['node'], pc[n1]['red']) != (pc[n2]['node'], pc[n2]['red']):
        return ZZ(0)
    nd1, Pt = sec[n1]
    nd2, Q = sec[n2]
    assert nd1 is nd2
    return ZZ(min(vval(Pt.s - Q.s, ell), vval(Pt.t - Q.t, ell),
                  vval(Pt.y - Q.y, ell)))


def lamform(MODELS, ell, c1, c2):
    L = MODELS[ell]['Lam']
    n = L.nrows()
    return sum(c1.get(i, 0) * c2.get(j, 0) * L[i, j]
               for i in range(n) for j in range(n))


def q_model(MODELS, rep, zn, ell, E0, g):
    cls = MODELS[ell]['cls']
    vg = gval(g, zn, ell) - gval(g, BNAME, ell)
    inter = 0
    c2 = {}
    for n in NM:
        c = E0.multiplicity(PLC[n])
        if not c:
            continue
        inter += c * (contact(MODELS, ell, zn, n) - contact(MODELS, ell, BNAME, n))
        c2[cls[n]] = c2.get(cls[n], 0) + c
    c1 = {cls[zn]: 1}
    c1[cls[BNAME]] = c1.get(cls[BNAME], 0) - 1
    return vg, inter, lamform(MODELS, ell, c1, c2)


MEASURED = {3: {"(1,3)": QQ(0), "(1,-3)": QQ(0),
                "(-1,3)": QQ(1) / 2, "(-1,-3)": QQ(1) / 2,
                "(-2,6)": QQ(0), "(-2,-6)": QQ(0),
                "(-1/11,15/11)": QQ(0), "(-1/11,-15/11)": QQ(0),
                "(0,0)": QQ(1) / 2},
            2: {"(1,3)": QQ(0), "(1,-3)": QQ(0),
                "(-1,3)": QQ(0), "(-1,-3)": QQ(0),
                "(-2,6)": -QQ(1) / 4, "(-2,-6)": -QQ(1) / 4,
                "(-1/11,15/11)": QQ(0), "(-1/11,-15/11)": QQ(0),
                "(0,0)": -QQ(1) / 4}}


def group_F(MODELS, FAMILY):
    print("(F) STAGE 3b: ell = 3, THEN ell = 2 -- THE EXACT VALUES AT ALL NINE")
    info("h_ell(z-b,D'')/log ell = v_ell(g(z)/g(b)) + (bar z - bar b . bar E_0) "
         "+ Lambda(z-b,E_0), on E125/E128--E130's regular model, where every "
         "horizontal divisor is a rational section.")
    derived = {}
    for ell in (3, 2):
        print("   --- ell = %d ---" % ell)
        for zn in NM:
            if zn == BNAME:
                derived[(ell, zn)] = QQ(0)
                continue
            vals, tags = [], []
            for (nm_, rep) in FAMILY:
                if not rep.usable(zn):
                    continue
                for (tag, E0, g) in rational_reps(rep, zn):
                    vg, inter, LL = q_model(MODELS, rep, zn, ell, E0, g)
                    vals.append(vg + inter + LL)
                    tags.append("%s/%s" % (nm_, tag))
                    info("   z=%-15s %-28s v(g)=%-4s inter=%-4s Lambda=%-7s q=%s"
                         % (zn, "%s %s" % (nm_, tag), vg, inter, LL,
                            vg + inter + LL))
            check(len(set(vals)) == 1 and len(vals) >= 3,
                  "   z=%-15s the %d (representative, E_0) pairs give the SAME "
                  "q_%d = %s.  They shift weight between v(g), the horizontal "
                  "term and Lambda -- and between different cycles -- so this "
                  "would fail if the sign of Lambda, the contact convention or "
                  "the pullback formulas were wrong"
                  % (zn, len(vals), ell, vals[0] if vals else "?"))
            derived[(ell, zn)] = vals[0] if vals else None
    for ell in (3, 2):
        got = [(zn, derived[(ell, zn)], MEASURED[ell][zn]) for zn in NM]
        check(all(a == b for (_, a, b) in got),
              "*** ell = %d: THE EXACT q_%d AGREES WITH E093's MEASUREMENT AT "
              "ALL NINE POINTS: %s ***"
              % (ell, ell, ", ".join("t=%s%s -> %s"
                                     % (COORD[z][0], "+" if COORD[z][1] >= 0 else "-", a)
                                     for (z, a, _) in got)))
    check(derived[(3, "(0,0)")] == QQ(1) / 2 and derived[(2, "(0,0)")] == -QQ(1) / 4,
          "*** z = (0,0), THE SIGMA-FIXED POINT: q_3 = 1/2 and q_2 = -1/4, "
          "DERIVED.  E127(k) and E132 could not reach it at all -- (z,z) lies on "
          "Gamma_sigma, so no representative of the form k Gamma_sigma - C_psi "
          "is admissible there ***")
    check(derived[(3, SIGMA[BNAME])] == QQ(0)
          and derived[(2, SIGMA[BNAME])] == QQ(0),
          "*** z = sigma b = (1,-3): q_3 = q_2 = 0, DERIVED.  Here z - b = -n_b "
          "is sigma-anti-invariant and E093 measured 0; the value is now exact ***")
    check(all(derived[(ell, zn)] == MEASURED[ell][zn]
              for ell in (2, 3) for zn in USABLE133),
          "and the seven values E133 already derived are reproduced unchanged by "
          "the new cycles -- five independent representatives, one answer")
    return derived


# ===========================================================================
# (G)  Negative controls.
# ===========================================================================

def group_G(MODELS, derived, FAMILY):
    print("(G) WHY THE REPRESENTATIVES AGREE, AND EXACTLY WHEN THEY DO NOT")
    info("E133 group (A) measured the ratio g(z)/g(b) between two "
         "representatives and found the law [e_2(z)e_1(b)]/[e_1(z)e_2(b)].  "
         "Here the connecting function is explicit, so the law is a two-line "
         "computation instead of a limit:")
    info("      g_F(b) = 2 psi(b) / [ 2 psi(b) . (psi(b)+psi(z)) ] "
         "= 1 / (psi(b)+psi(z)) ,")
    info("      g_F(z) = 2 psi(z) / [ (psi(z)+psi(b)) . 2 psi(z) ] "
         "= 1 / (psi(z)+psi(b)) ,")
    info("      hence  g_F(z)/g_F(b) = 1  whenever psi(b), psi(z) and "
         "psi(b)+psi(z) are all nonzero.   [T]")
    info("So h_ell(z-b, D''_psi) = h_ell(z-b, D'_t) at EVERY ell, for every "
         "anti-invariant psi, as long as those three quantities do not vanish "
         "-- and those are precisely conditions (alpha) and (gamma) of the "
         "criterion in group (A).  The agreement seen in group (F) is not a "
         "coincidence; it is this identity.")
    nid, nfail, where = 0, 0, {}
    for (nm_, rep) in FAMILY:
        psi = rep.psi
        for zn in NM:
            pb, pz = val_at(psi, BNAME), val_at(psi, zn)
            g = gF(rep, zn)
            if pb == 0 or pz == 0 or pb + pz == 0:
                nfail += 1
                where.setdefault(nm_, []).append(zn)
                continue
            ok = (val_at(g, BNAME) == 1 / (pb + pz)
                  and val_at(g, zn) == 1 / (pb + pz))
            if not ok:
                check(False, "   %s at z=%s: g_F(z) != g_F(b)" % (nm_, zn))
            nid += 1
    check(True, "*** g_F(z) = g_F(b) = 1/(psi(b)+psi(z)) in all %d cases where "
                "the three quantities are nonzero; in the remaining %d the "
                "function itself is 0 or infinite at z or b ***" % (nid, nfail))
    check(sorted(where.get(MASTER.name, [])) == sorted(["(0,0)", SIGMA[BNAME]]),
          "*** AND FOR THE MASTER REPRESENTATIVE THE PROVISO FAILS AT EXACTLY "
          "TWO POINTS, z = (0,0) (where psi(z) = 0) and z = sigma b (where "
          "psi(b) + psi(z) = 0) -- E133's two orphans, and no others.  So the "
          "identity transports E133's seven values and CANNOT transport the "
          "other two: the value at (0,0) and at sigma b really did need a cycle "
          "free of Gamma_sigma, and is not a restatement of what E133 knew ***")
    for (nm_, rep) in FAMILY:
        info("   %-22s proviso fails at %s"
             % (nm_, ", ".join(where.get(nm_, [])) or "no z"))
    info("the vanishing locus is exactly the inadmissibility of group (A): "
         "psi(x) = 0 puts (x,x) on C''_psi, and psi(b) + psi(z) = 0 puts b into "
         "i_2^*C''_psi (equivalently z into i_1^*C''_psi).")
    print("(G2) NEGATIVE CONTROL: WHAT AN INADMISSIBLE Z'' ACTUALLY DOES")
    nbad = 0
    for (nm_, rep) in FAMILY:
        for zn in NM:
            if rep.usable(zn):
                continue
            Dv = rep.D(zn)
            cz, cb = Dv.multiplicity(PLC[zn]), Dv.multiplicity(PLC[BNAME])
            diag = not rep.avoids_diagonal(zn)
            pz, pb = val_at(rep.psi, zn), val_at(rep.psi, BNAME)
            check((cz or cb or diag)
                  and cz == coeff_local(rep.psi, zn, zn)
                  and cb == coeff_local(rep.psi, zn, BNAME),
                  "   %-22s z=%-15s %s coefficients (z,b) = (%s,%s), matching "
                  "the local criterion; psi(b)+psi(z) = %s"
                  % (nm_, zn,
                     "(z,z) on C''_psi;" if diag else "|D''| meets {z,b}:",
                     cz, cb, (pb + pz) if (pb is not None and pz is not None)
                     else "?"))
            nbad += 1
    check(nbad > 0,
          "*** %d inadmissible (representative, z) pairs, and in every one the "
          "local height is not merely wrong but UNDEFINED: either (z,z) lies on "
          "a component of Z'' or |D''(b,z)| meets {z,b}, so the "
          "disjoint-support formula has nothing to compute.  That is the same "
          "obstruction E132 met with Z_c, one level further out ***" % nbad)
    check(not REP_T.usable("(0,0)"),
          "and E133's Z'_t at z = (0,0) is not merely inconvenient: (z,z) lies "
          "ON Gamma_sigma, a component of Z'_t, so i_Delta^*Z'_t is not defined "
          "there -- which is the whole reason for E135.  NOTE the identity above "
          "does NOT rescue it: g_F(z)/g_F(b) = 1 transports a value between two "
          "ADMISSIBLE representatives, and Z'_t is not one at (0,0)")


# ===========================================================================
# (H)  The search of PLAN section 1-5.
# ===========================================================================

def single_search():
    Pt = PolynomialRing(QQ, 'x')
    x = Pt.gen()
    cands = [("%d" % 1, Pt(1)), ("t", x), ("t^2+1", x ** 2 + 1),
             ("t^2-t+1", x ** 2 - x + 1)]
    cands += [("t%+d" % c, x + c) for c in range(-6, 7) if c != 0]
    out, tested = [], []
    for (nm_, h) in cands:
        rep = Rep2(h(tf) * wf, "Z''_{(%s)w}" % nm_)
        us = [n for n in NM if rep.usable(n)]
        tested.append((nm_, rep, len(us)))
        if len(us) == 9:
            out.append((nm_, rep))
    return out, tested


def group_H(SINGLE, TESTED):
    print("(H) PLAN SECTION 1-5: IS THERE A SINGLE psi GOOD AT ALL NINE POINTS?")
    info("PLAN section 1-5 left this undecided and section 1-4 arranged to do "
         "without it.  Group (A)'s criterion answers it by inspection: psi = "
         "h(t) w is admissible at all nine iff h has no zero at t = 1, -1, -2, "
         "-1/11, 0; h'(1) != 0; and 9 h(1)^2 differs from 9 h(-1)^2, 36 h(-2)^2 "
         "and (225/121) h(-1/11)^2.")
    Pt = PolynomialRing(QQ, 'x')
    x = Pt.gen()
    for (nm_, h, want) in [("t-1", x - 1, False), ("t", x, False),
                           ("t+5", x + 5, False), ("t+3", x + 3, True),
                           ("t^2-t+1", x ** 2 - x + 1, True)]:
        hv = {n: h(COORD[n][0]) for n in NM}
        pred = (all(hv[n] != 0 for n in NM)
                and h.derivative()(QQ(1)) != 0
                and all(COORD[n][1] ** 2 * hv[n] ** 2
                        != COORD[BNAME][1] ** 2 * hv[BNAME] ** 2
                        for n in ("(-1,3)", "(-2,6)", "(-1/11,15/11)")))
        got = [t for (t, r, k) in TESTED if t == nm_]
        gotall = [k == 9 for (t, r, k) in TESTED if t == nm_]
        check(pred == want and (not gotall or gotall[0] == want),
              "   h = %-9s predicted %-5s, found %-5s"
              % (nm_, want, gotall[0] if gotall else "?"))
    check(len(SINGLE) >= 5,
          "*** %d of the %d tested psi are admissible at all nine points: h = %s.  "
          "So PLAN section 1-4's per-point choice of representative is NOT needed, "
          "and the per-point construction survives only as an independent check "
          "in groups (E) and (F) ***"
          % (len(SINGLE), len(TESTED), ", ".join(h for (h, _) in SINGLE)))
    info("counts over the whole family: %s"
         % ", ".join("%s:%d" % (t, k) for (t, r, k) in TESTED))


# ===========================================================================
# (I)  Regression.
# ===========================================================================

def group_I(MODELS, derived):
    print("(I) THE PUBLISHED NUMBERS ARE UNCHANGED")
    check(MODELS[2]['Lam'] == matrix(QQ, [[0, 0, 0], [0, QQ(1) / 2, QQ(1) / 4],
                                          [0, QQ(1) / 4, QQ(7) / 8]]),
          "Lambda_2 is E104's / E128(g)'s matrix")
    check(MODELS[3]['Lam'] == matrix(QQ, [[0, 0, 0], [0, 1, QQ(1) / 2],
                                          [0, QQ(1) / 2, QQ(3) / 4]]),
          "Lambda_3 is E125(g)'s / E128(h)'s matrix")
    E104 = sorted([sorted(["(1,3)", "(-1,3)", "(-1/11,-15/11)"]),
                   sorted(["(1,-3)", "(-1,-3)", "(-1/11,15/11)"]),
                   sorted(["(-2,6)", "(-2,-6)", "(0,0)"])])
    E125 = sorted([sorted(["(1,3)", "(-2,-6)", "(-1/11,15/11)"]),
                   sorted(["(1,-3)", "(-2,6)", "(-1/11,-15/11)"]),
                   sorted(["(-1,3)", "(-1,-3)", "(0,0)"])])
    for ell, want, src in [(2, E104, "E104 / E127(r) / E128(f)"),
                           (3, E125, "E125(c) / E128(h)")]:
        part = {}
        for nm in NM:
            part.setdefault(MODELS[ell]['cls'][nm], []).append(nm)
        check(sorted(sorted(v) for v in part.values()) == want,
              "the partition of the nine points at ell = %d is %s's" % (ell, src))
    m2, s = ZZ(16848), ZZ(8424)
    check(s == m2 / 2 and m2 == 2 ** 4 * 3 ** 4 * 13,
          "E127(d)'s scale s = -lambda_Z/2 = 8424 = m_2/2 is unchanged")
    check(-derived[(3, "(-1,3)")] * s == -m2 / 4
          and -derived[(2, "(-2,6)")] * s == m2 / 8,
          "*** E133 group (J)'s two constants are reproduced by the new cycles: "
          "c_3 = -(m_2/4) log_13(3) = -4212 log_13(3) and c_2 = +(m_2/8) "
          "log_13(2) = +2106 log_13(2).  E135 moves no published number: the "
          "generators of E093's Upsilon sit on t = -1 and t = -2, both already "
          "settled by E133 ***")
    check(derived[(3, "(0,0)")] == derived[(3, "(-1,3)")]
          and derived[(2, "(0,0)")] == derived[(2, "(-2,6)")],
          "*** and the sigma-fixed point carries EXACTLY c_3 and c_2, not some "
          "other pair: q_3(0,0) = q_3(t=-1) = 1/2 and q_2(0,0) = q_2(t=-2) = "
          "-1/4 on the nose, so h_3(0,0) = c_3 and h_2(0,0) = c_2 with no "
          "appeal to the sign convention at all.  That is E093's pattern "
          "(j_3,j_2) = (1,1) at t = 0, the point realising the FOURTH element "
          "c_3 + c_2 of Upsilon -- and it is the one point E133 could not "
          "reach ***")
    for ell, twin in [(3, "(-1,3)"), (2, "(-2,6)")]:
        cls = MODELS[ell]['cls']
        check(cls["(0,0)"] == cls[twin],
              "   ell = %d: (0,0) and t = %s lie on the SAME component, so "
              "component-constancy of h_%d predicts the equality above; the "
              "derivation confirms it independently"
              % (ell, COORD[twin][0], ell))
    same = sum(1 for ell in (2, 3) for a in NM for b_ in NM
               if a < b_ and MODELS[ell]['cls'][a] == MODELS[ell]['cls'][b_]
               and derived[(ell, a)] == derived[(ell, b_)])
    tot = sum(1 for ell in (2, 3) for a in NM for b_ in NM
              if a < b_ and MODELS[ell]['cls'][a] == MODELS[ell]['cls'][b_])
    check(same == tot and tot >= 12,
          "*** COMPONENT-CONSTANCY OF h_ell, CHECKED: in all %d pairs of the "
          "nine rational points that share a component (over both bad primes) "
          "the derived q_ell agree.  That is the property E104 needs for the "
          "UPPER bound |Upsilon_2| <= 3, verified here at nine points rather "
          "than assumed -- [E: %d pairs], not a proof, since Upsilon is a "
          "statement about all of C_4(Q_ell) ***" % (tot, tot))
    info("(0,0) still does not enter Balakrishnan--Dogra's X' (E127(k)): the "
         "elliptic term is undefined there because n_z = (z) - (sigma z) = 0.  "
         "What is derived here is its local height, not its membership.")
    check(all(derived[(ell, zn)] == MEASURED[ell][zn]
              for ell in (2, 3) for zn in NM),
          "*** EVERY local height of E093 at ell = 2 and ell = 3 is now DERIVED "
          "from a cycle representative that contains neither Delta nor "
          "Gamma_sigma.  The table has no measurements left in it ***")


# ===========================================================================

def main():
    t00 = time.time()
    print("=" * 74)
    print("=== check-gamma-free.sage --- E135: a cycle representative free  ===")
    print("=== of BOTH Delta and Gamma_sigma, and the last two local heights ===")
    print("=" * 74)
    def timed(fn, *a):
        t0 = time.time()
        fn(*a)
        print("   [%.0f s]" % (time.time() - t0))
        sys.stdout.flush()

    t0 = time.time()
    SINGLE, TESTED = single_search()
    print("   [search of PLAN section 1-5: %.0f s]" % (time.time() - t0))
    sys.stdout.flush()
    FAMILY = [(MASTER.name, MASTER), (ALT.name, ALT),
              (REP_W2.name, REP_W2), (REP_TW2.name, REP_TW2)]
    # group (A) tests the criterion against the divisors on the WHOLE search
    # family, not just the four representatives the later groups use.
    WIDE = FAMILY + [(r.name, r) for (_, r, _) in TESTED]
    timed(group_A, WIDE)
    timed(group_B, FAMILY)
    timed(group_C, FAMILY)
    timed(group_D, FAMILY, SINGLE)
    timed(group_E, FAMILY)
    timed(group_E2, FAMILY)
    MODELS = build_models()
    tF = time.time()
    derived = group_F(MODELS, FAMILY)
    print("   [%.0f s]" % (time.time() - tF))
    timed(group_G, MODELS, derived, FAMILY)
    timed(group_H, SINGLE, TESTED)
    timed(group_I, MODELS, derived)
    print("=" * 74)
    print("E135 GATE: %s   (%d checks, %d failures, %.0f s)"
          % ("GREEN" if not FAIL else "*** RED ***", NCHECK[0], len(FAIL),
             time.time() - t00))
    for m in FAIL:
        print("   FAILED: %s" % m)
    sys.stdout.flush()
    sys.exit(int(1 if FAIL else 0))


main()
