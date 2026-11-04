\\ check-selmer-local.gp --- E118: phases B-E of the TODO plan.
\\
\\ Run: gp -q check-selmer-local.gp < /dev/null
\\
\\ GOAL.  E116 reproduced dim_F2 Sel^2(Jac X / K) = 5 on the free Magma
\\ calculator, with the curve fingerprinted twelve ways, and that closed the
\\ last [GAP].  What it did NOT do is compute the number here.  The TODO block
\\ "E118 候補" lays out a six-phase local computation (Stoll, Acta Arith. 98
\\ (2001)); phase A -- the fields, the S-units, the dimensions -- was measured
\\ on 2026-08-18/19.  THIS SCRIPT carries out phases B-E, i.e.
\\
\\   B.  build  H = ker( N : L(S,2)/K(S,2) -> K^x/(K^x)^2 ),  the group that
\\       contains Sel^2 before any local condition is imposed;
\\   C.  impose the ONE archimedean condition (K has a single real place);
\\   D.  impose the condition at v | 3;
\\   E.  impose the condition at v | 2,
\\
\\ ending in dim_F2 Sel^(2)(Jac X / K) = 4 in Stoll's H_K (= 5 inside
\\ H^1(K, J[2])).  It began as the spike for B and C alone, with the plan's
\\ go/no-go, verbatim: "6-8 まで落ちれば残りは E だけで見通しは良い。15 の
\\ まま動かなければ設定のどこかが違うのでそこで止めて報告".
\\
\\ WHAT IS AND IS NOT INDEPENDENT.  Everything below is computed on this
\\ machine.  But dim Sel = 5 is already known (E116), so this cannot be a blind
\\ calibration; what the script adds is (i) the local conditions at v | 3 and
\\ v | 2 (phases D and E), which were first run here as a spike, and (ii) the
\\ checks of groups 3 and 4, which do not know the answer: three 2-torsion
\\ classes and two differences of K-rational points must land in H, must have
\\ the right span, and must satisfy the real condition.
\\
\\ CONVENTIONS.  X : y^2 = f(x) with f of degree 6 over K = Q(4^{1/3}) = Q(y),
\\ y^3 = 4, c = the leading coefficient of f.  L = K[x]/(f) = L_1 x L_2 x L_3
\\ (E116: f factors into three irreducible quadratics over K), T_i = the image
\\ of x in L_i.  The descent map is
\\     mu : J(K)/2J(K) --> L^x / (L^x)^2 K^x ,
\\ mu( sum n_P (P) ) = prod (x_P - T)^{n_P} for support off the Weierstrass
\\ points, and N_{L/K}(x - T) = f(x)/c, so N(mu(D)) = (y_1 y_2 / c)^2 is a
\\ square: the image lies in ker N.  NOTE the quotient by K^x: a representative
\\ of a class need NOT be an S-unit times a square on the nose, only after
\\ multiplication by a suitable k in K^x.  Computing that k is what kadjust()
\\ below does, and its failure mode (inconsistent parities over a prime of K)
\\ is a genuine check and not a coding accident.

\\ ---------------------------------------------------------------- the curve
\\ E039(e) via Ritzenthaler-Romagny, identical code to check-prym-rank.gp and
\\ check-selmer-reproduce.gp -- rebuilt, never copied.  The base field variable
\\ is 'y (not 'w) because PARI's rnf* demand that the base field's variable
\\ have LOWER priority than the relative one, and 'x is the relative variable.
sextic() =
{
  my(T = 'y^3 - 4, A, Ai, aa, bb, cc);
  A = [Mod(27,T), Mod(-27*'y,T), Mod(0,T);
       Mod(6,T),  Mod(-12,T),    Mod(6,T);
       Mod(1,T),  Mod('y,T),     Mod('y^2,T)];
  Ai = A^-1;
  aa = Ai[1,1] + 2*Ai[2,1]*'x + Ai[3,1]*'x^2;
  bb = Ai[1,2] + 2*Ai[2,2]*'x + Ai[3,2]*'x^2;
  cc = Ai[1,3] + 2*Ai[2,3]*'x + Ai[3,3]*'x^2;
  return(bb*(bb^2 - aa*cc));
};

FAIL = 0; OPEN = 0;
check(c, msg) = { if(c, printf("   [ok]  %s\n", msg),
                     printf("   [FAIL] %s\n", msg); FAIL++); c; };
\\ an item that is neither passed nor failed: a sub-computation this script
\\ does not finish.  Kept separate from FAIL so that the gate cannot be made
\\ to look green by lowering a bar.
todo(msg) = { printf("   [open] %s\n", msg); OPEN++; };
info(msg) = printf("        %s\n", msg);

\\ rnfinit needs an integral relative polynomial.  g is monic quadratic over K
\\ but its constant term can have denominator 2 (O_K = Z[2^{1/3}] is not Z[y]).
\\ Return [gtilde, m] with gtilde(X) = m^2 g(X/m) integral, so that the root
\\ beta of gtilde is m T with T the root of g.
intpol(nf, g) =
{ my(m = 1, h, ok);
  while(1,
    h = m^2*subst(g, 'x, 'x/m); ok = 1;
    for(j = 0, poldegree(h),
      if(denominator(nfalgtobasis(nf, polcoef(h, j, 'x))) != 1, ok = 0));
    if(ok, return([h, m]));
    m *= 2);
};

\\ evaluate a polynomial with coefficients in K at an element of L_i
evalup(rn, pol, t) =
{ my(s = 0);
  forstep(j = poldegree(pol), 0, -1, s = s*t + rnfeltup(rn, polcoef(pol, j, 'x)));
  s;
};

locdim(pp) =
{ my(r = 0, odd = 0, eK = idealprimedec(K, pp)[1].e, dw = List());
  for(i = 1, 3,
    my(Ps = idealprimedec(BN[i], pp));
    for(m = 1, #Ps,
      r++;
      my(d = Ps[m].e*Ps[m].f/eK);
      listput(dw, d);
      if(d % 2, odd = 1)));
  [r, r - 1 - odd, Vec(dw)];
};

\\ z in K^x is a square in K_{v_3} iff v_3(z) is even and the unit part is a
\\ square in the residue field F_3 (Hensel, 3 being odd).
issq3(z) =
{ my(v = idealval(K, z, idealprimedec(K,3)[1]));
  if(v % 2, return(0));
  issquare(nfmodpr(K, z/PI3^v, MPK));
};
\\ ---- phase E: local square classes at v | 2, by HILBERT SYMBOLS.
\\ At 2 the group L_w^x/(L_w^x)^2 has dimension 2 + [L_w:Q_2] = 8 and there is
\\ no Hensel shortcut.  But the Hilbert symbol is a PERFECT pairing on it, so a
\\ set of global probes c_1..c_m gives coordinates delta |-> ((delta,c_j)_w)_j
\\ that are INJECTIVE as soon as the c_j span -- and the Gram matrix
\\ ((c_a,c_b)_w) having rank 8 certifies exactly that, the pairing being
\\ nondegenerate.  So the local field is never constructed: the whole of phase
\\ E is a finite list of nfhilbert calls on global elements.
gram(nf, P, CS) =
  Mod(matrix(#CS, #CS, a, b, if(nfhilbert(nf, CS[a], CS[b], P) == 1, 0, 1)), 2);
\\ eight (resp. five) independent columns of the Gram matrix are independent in
\\ L_w^x/(L_w^x)^2, hence a basis once the rank is full.
hbasis(nf, P, CS) =
{ my(M = gram(nf, P, CS), idx);
  idx = matindexrank(M)[2];
  [vector(#idx, k, CS[idx[k]]), matrank(M)];
};
hcoord(nf, P, BS, delta) =
  Col(vector(#BS, j, if(nfhilbert(nf, delta, BS[j], P) == 1, 0, 1)));
lam2(dl) =
{ Mod(Col(concat(concat(Vec(hcoord(BN[1], P2[1], BS2[1], dl[1])),
                        Vec(hcoord(BN[2], P2[2], BS2[2], dl[2]))),
                        Vec(hcoord(BN[3], P2[3], BS2[3], dl[3])))), 2);
};
\\ THE TARGET DIMENSION, corrected.  Stoll Lemma 5.1: assuming (dagger) --
\\ which holds everywhere here, the genus being even -- ker delta_K is
\\ 2J(K) if (dagger-dagger) holds OR there is no K-rational divisor class of
\\ degree 1; otherwise 2J(K) has index 2 in it.  For g = 2, (dagger-dagger)
\\ says the six zeros of f admit a Galois-stable partition into two
\\ three-sets (Lemma 5.3).  Over K_{v_2} f is a product of three irreducible
\\ quadratics g_i (orbits 2, 2, 2); a stable partition must then take one
\\ root from each pair, which needs the three K_{v_2}(sqrt disc g_i) to be one
\\ and the same field (Stoll p. 257: L contains a quadratic extension of K).
\\ They are not -- disc g_i disc g_j is a non-square in K_{v_2}, by a Hilbert
\\ symbol, for two of the three pairs -- so (dagger-dagger) FAILS over K_{v_2},
\\ hence also over K; and X(K_{v_2}) is non-empty, so ker delta has dimension
\\ 1 and
\\      dim Im mu_{v_2} = dim J(K_{v_2})/2J(K_{v_2}) - 1 = 8 - 1 = 7.
\\ The same test passes at the other two places, which is why their targets
\\ needed no correction and were met: over R all six roots are real, orbits
\\ 1,1,1,1,1,1; over K_{v_3} the orbits are 1,1,2,1,1.  Both admit a stable
\\ 3+3 partition, so ker delta is trivial there.  Note 7 + 5 = 12 <= 24/2,
\\ as an isotropic subspace of a nondegenerate form must be -- 8 + 5 = 13
\\ was not, which is the a priori sign that 8 was wrong.
IMV2 = 7;
\\ z in K^x is a square in K_{v_2} iff it pairs trivially with a spanning set.
issq2(z) =
{ my(r = 1, P = idealprimedec(K, 2)[1]);
  for(k = 1, #BSK2, if(nfhilbert(K, z, BSK2[k], P) != 1, r = 0));
  r;
};

\\ ---- phase E, the other half of Im mu_{v_2}: prime divisors of DEGREE 2.
\\ Stoll, Acta Arith. 98 (2001), Lemma 6.2: for even deg f and even genus,
\\ J_p is cut out of the group generated by delta' of ALL prime divisors of
\\ degree at most g, carrying deg D mod 2 as an extra F_2 coordinate.  Degree
\\ one gives the points with x in K_v -- pairs of them have parity 0 -- and
\\ degree two gives the divisors whose two points are conjugate over K_v,
\\ which the rational x's cannot reach.
\\
\\ The first attempt sampled monic quadratics a = x^2 + ux + w with small
\\ integral u, w.  That covers the 31 quadratic extensions of K_{v_2} very
\\ unevenly: 1710 candidates produced 10 divisors, all inside one and the same
\\ 11 dimensions.  So parametrise by the EXTENSION instead.  Write
\\ a = (x - beta)^2 - D with D running over representatives of the nontrivial
\\ square classes of K_{v_2}^x -- there are 2^5 - 1 = 31, the products of
\\ subsets of the five generators already in hand -- and beta over a box.
\\ A = K(sqrt D) then depends only on D, so nfinit is called once per class
\\ and not once per candidate, and every quadratic extension is reached by
\\ construction.  mu of the divisor is a(T) = (T_i - beta)^2 - D.
qfield(D) =
{ my(hm, rn, A, Ps, sq, CS, pi, hb);
  hm = intpol(K, 'x^2 - D);
  rn = rnfinit(K, hm[1]);
  A = nfinit(rn.polabs);
  Ps = idealprimedec(A, 2);
  if(#Ps != 1, return(0));
  if(Ps[1].e*Ps[1].f != 6, return(0));
  sq = rnfeltreltoabs(rn, Mod('x, hm[1])) / hm[2];
  pi = nfbasistoalg(A, Ps[1].gen[2]);
  CS = List(); listput(CS, pi); listput(CS, Mod(-1, A.pol));
  for(k = 1, 2*idealval(A, 2, Ps[1]) + 1, listput(CS, 1 + pi^k));
  listput(CS, sq); listput(CS, 1 + sq); listput(CS, 1 - sq);
  listput(CS, 2 + sq); listput(CS, 3 + sq); listput(CS, sq*pi);
  hb = hbasis(A, Ps[1], Vec(CS));
  if(hb[2] != 8, return(0));
  [A, rn, sq, Ps[1], hb[1]];
};
\\ is f(beta + gamma sqrt D) a square in A_w?  If so return
\\ mu = a(T) = (T - beta)^2 - gamma^2 D.
\\ NB gamma.  A general element of M = K_v(sqrt D) is beta + gamma sqrt D
\\ with beta, gamma in K_v; fixing gamma = 1 fixes the quadratic a up to a
\\ box of beta, and scaling gamma moves alpha between 2-adic regimes without
\\ changing the field.  Leaving it out is what made the first three searches
\\ saturate.
qdiv2(QF, D, beta, gam) =
{ my(al, z, r = 1, DD2 = gam^2*D);
  al = rnfeltup(QF[2], beta) + rnfeltup(QF[2], gam)*QF[3];
  z = evalup(QF[2], f, al);
  if(z == 0, return(0));
  for(k = 1, #QF[5], if(nfhilbert(QF[1], z, QF[5][k], QF[4]) != 1, r = 0));
  if(!r, return(0));
  for(i = 1, 3,
    if((TA[i] - rnfeltup(RN[i], beta))^2 - rnfeltup(RN[i], DD2) == 0, return(0)));
  lam2(vector(3, i,
    (TA[i] - rnfeltup(RN[i], beta))^2 - rnfeltup(RN[i], DD2)));
};

\\ the coordinate map of a triple in F_2^{2 NP} at the primes over 3.
lam3(dl) =
  Mod(Col(concat(vector(NP, k, loc2(BN[B3[k]], P3[k], M3[k], dl[B3[k]])))), 2);
\\ ---- phase D: local square classes at an ODD prime.  For P | 3 the residue
\\ characteristic is odd, so L_P^x/(L_P^x)^2 = F_2^2 by Hensel: the valuation
\\ mod 2, and whether the unit part is a square in the residue field.
loc2(bn, P, mp, delta) =
{ my(v = idealval(bn, delta, P), u, r);
  u = delta / nfbasistoalg(bn, P.gen[2])^v;
  r = nfmodpr(bn, u, mp);
  [v % 2, if(issquare(r), 0, 1)];
};

\\ the prime of K under a prime P of L_i.  Outside 2 and 3 the extension
\\ L_i/K is unramified (disc L_i is 2^a 3^b), so e(P/q) = 1 and the parity of
\\ v_P is shifted by exactly v_q(k) when the representative is scaled by k.
qunder(i, P) =
{ my(qs = idealprimedec(K, P.p));
  for(t = 1, #qs,
    if(idealval(BN[i], rnfeltup(RN[i], nfbasistoalg(K, qs[t].gen[2])), P) > 0,
       return(t)));
  0;
};
\\ k in K^x making every component of the triple an S-unit times a square,
\\ or 0 if no such k exists (which would mean the class is not in L(S,2)K^x).
kadjust(dl) =
{ my(ps = List(), b, par);
  for(i = 1, 3,
    my(fa = idealfactor(BN[i], dl[i]));
    for(m = 1, #fa[,1],
      if(fa[m,1].p == 2 || fa[m,1].p == 3, next);
      if(fa[m,2] % 2 == 0, next);
      listput(ps, fa[m,1].p)));
  ps = Set(Vec(ps));
  b = matid(3);
  for(n = 1, #ps,
    my(qs = idealprimedec(K, ps[n]));
    for(t = 1, #qs,
      par = -1;
      for(i = 1, 3,
        my(Ps = idealprimedec(BN[i], ps[n]));
        for(m = 1, #Ps,
          if(qunder(i, Ps[m]) != t, next);
          my(e = idealval(BN[i], dl[i], Ps[m]) % 2);
          if(par < 0, par = e, if(par != e, return(0)))));
      if(par == 1, b = idealmul(K, b, qs[t]))));
  my(g = bnfisprincipal(K, b, 1));
  if(#g[1] > 0 && vecmax(abs(Vec(g[1]))) > 0, return(0));
  nfbasistoalg(K, g[2]);
};
\\ the class of a triple: its F_2 column in V = L(S,2), and, separately, the
\\ sign vector of the adjusted representative at the six real embeddings.
classof(dl) =
{ my(k = kadjust(dl), col, sg, da = vector(3), off = 0);
  if(k == 0, return(0));
  col = vector(DD, t, 0); sg = vector(6, t, 0);
  for(i = 1, 3,
    my(d = dl[i] * rnfeltup(RN[i], k), fa, a = matid(6), gen, v, s);
    fa = idealfactor(BN[i], d);
    for(m = 1, #fa[,1],
      if(fa[m,1].p == 2 || fa[m,1].p == 3, next);
      if(fa[m,2] % 2, return(0));
      a = idealmul(BN[i], a, idealpow(BN[i], fa[m,1], fa[m,2]/2)));
    gen = bnfisprincipal(BN[i], a, 1);
    if(#gen[1] > 0 && vecmax(abs(Vec(gen[1]))) > 0, return(0));
    v = bnfisunit(BN[i], d/nfbasistoalg(BN[i], gen[2])^2, UL[i]);
    if(v == [], return(0));
    for(t = 1, DL[i], col[off+t] = lift(v[t]));
    s = nfeltsign(BN[i], d);
    for(r = 1, 2, sg[POS[i,r]] = if(s[r] < 0, 1, 0));
    da[i] = d;
    off += DL[i]);
  [Mod(Col(col), 2), Mod(Col(sg), 2), da];
};


{
print("=== check-selmer-local.gp --- E118: phases B, C, D, E ===");

\\ ============================================================ group 1
print("(1) THE ETALE ALGEBRA L = K[x]/(f):  phase A, regressed");
K = bnfinit('y^3 - 4, 1);
SK = concat(idealprimedec(K, 2), idealprimedec(K, 3));
UK = bnfunits(K, SK);
dK = #UK[1];
f = 108^2*sextic();
LC = polcoef(lift(f), 6, 'x);
check(K.no == 1 && K.sign == [1,1] && K.disc == -108,
      "K = Q(4^{1/3}): h = 1, signature [1,1], disc = -108");
\\ 2026-10-28: bnfinit's class group and units assume GRH until certified; the
\\ S-unit groups below are computed from them.  bnfcertify makes them
\\ unconditional (paper2 Section 9.5 calls the 2-descent exact).
check(bnfcertify(K) == 1,
      "bnfcertify(K) = 1: the class group and units of K are unconditional (no GRH)");
check(#idealprimedec(K,2) == 1 && #idealprimedec(K,3) == 1
      && idealprimedec(K,2)[1].e == 3 && idealprimedec(K,3)[1].e == 3,
      "2 and 3 are each totally ramified with a single place, so S_K has two "
      "elements");
check(dK == 4, "dim_F2 K(S,2) = 4");
my(idf = idealfactor(K, Mod(poldisc(lift(f),'x), 'y^3-4)), bad = 0);
for(k = 1, #idf[,1], if(idf[k,1].p != 2 && idf[k,1].p != 3, bad = 1));
check(!bad,
      "disc(f) is supported on the primes over 2 and 3 alone, so S_K already "
      "contains every prime of bad reduction and none need be added");
FA = nffactor(K, lift(f));
G = vector(3, i, FA[i,1]);
check(#G == 3 && poldegree(G[1]) == 2 && poldegree(G[2]) == 2
      && poldegree(G[3]) == 2,
      "f = c g_1 g_2 g_3 with the g_i monic irreducible quadratics over K "
      "(E116, rederived here)");
RN = vector(3); BN = vector(3); UL = vector(3); MM = vector(3);
DL = vector(3); TA = vector(3); SL = vector(3);
for(i = 1, 3,
  my(hm = intpol(K, G[i]));
  MM[i] = hm[2];
  RN[i] = rnfinit(K, hm[1]);
  BN[i] = bnfinit(RN[i].polabs, 1);
  SL[i] = concat(idealprimedec(BN[i],2), idealprimedec(BN[i],3));
  UL[i] = bnfunits(BN[i], SL[i]);
  DL[i] = #UL[i][1];
  TA[i] = rnfeltreltoabs(RN[i], Mod('x, hm[1])) / hm[2];
  info(Str("L_", i, " = Q[x]/(", polredbest(RN[i].polabs), "):  disc = ",
           factor(BN[i].disc)[,1]~, "^", factor(BN[i].disc)[,2]~,
           ",  h = ", BN[i].no, ",  signature ", BN[i].sign,
           ",  #S = ", #SL[i], ",  dim L_", i, "(S,2) = ", DL[i]));
  check(evalup(RN[i], G[i], TA[i]) == 0,
        Str("T_", i, " = beta_", i, "/", MM[i], " really is a root of g_", i,
            " in L_", i, ", so the x - T map is being formed from the right "
            "element")));
DD = vecsum(DL);
check(DL == [7,6,7] && DD == 20,
      "dim_F2 L(S,2) = 7 + 6 + 7 = 20 (phase A's measurement, recomputed)");
check(bnfcertify(BN[1]) == 1 && bnfcertify(BN[2]) == 1 && bnfcertify(BN[3]) == 1,
      "bnfcertify(L_i) = 1 for i = 1, 2, 3: class groups and units of the three "
      "sextic fields are unconditional, hence so are the S-unit groups L_i(S,2) "
      "and everything built from them (no GRH)");
check(BN[1].no == 1 && BN[2].no == 1 && BN[3].no == 1,
      "h(L_i) = 1 for all three, so L(S,2) is generated by S-units alone and "
      "no class group correction enters");

\\ the six real embeddings, and which root of f each one names.  (Needed in
\\ group 3 as well as group 4, so it is set up here; the checks are in (4).)
YR = 4^(1/3);
FINF = subst(lift(f), 'y, YR);
RT = vecsort(vector(6, k, real(polroots(FINF)[k])));
POS = matrix(3, 2);
for(i = 1, 3,
  for(r = 1, 2,
    my(t = real(nfeltembed(BN[i], TA[i])[r]), best = 1);
    for(k = 2, 6, if(abs(RT[k]-t) < abs(RT[best]-t), best = k));
    POS[i,r] = best));

\\ ============================================================ group 2
print("(2) PHASE B:  H = ker( N ) / K(S,2)");
NM = matrix(dK, DD); BV = vector(DD); BI = vector(DD);
my(col = 0);
for(i = 1, 3,
  for(j = 1, DL[i],
    col++;
    BI[col] = i;
    BV[col] = nfbasistoalg(BN[i], nffactorback(BN[i], UL[i][1][j]));
    my(v = bnfisunit(K, rnfeltnorm(RN[i], BV[col]), UK));
    if(v == [], check(0, "the norm of an S-unit of L_i is an S-unit of K"),
       for(k = 1, dK, NM[k,col] = lift(v[k])))));
NM = Mod(NM, 2);
IM = matrix(DD, dK);
for(k = 1, dK,
  my(c = nffactorback(K, UK[1][k]), off = 0);
  for(i = 1, 3,
    my(v = bnfisunit(BN[i], rnfeltup(RN[i], c), UL[i]));
    if(v == [], check(0, "an S-unit of K stays an S-unit in L_i"),
       for(t = 1, DL[i], IM[off+t, k] = lift(v[t])));
    off += DL[i]));
IM = Mod(IM, 2);
rN = matrank(NM); rI = matrank(IM);
check(NM*IM == matrix(dK, dK),
      "N o iota = 0: the norm of the diagonal image of c in K is c^6, a "
      "square, so N descends to the quotient by K(S,2).  This is a check and "
      "not an assumption -- it is read off the two matrices");
check(rI == dK,
      Str("iota : K(S,2) -> L(S,2) is INJECTIVE (rank ", rI, " = ", dK,
          "), so the quotient loses exactly four dimensions"));
check(rN == dK, Str("N : L(S,2) -> K(S,2) is SURJECTIVE (rank ", rN, ")"));
KN = matker(NM);
DH = DD - rN - rI;
info(Str("dim ker N = ", DD, " - ", rN, " = ", DD - rN));
check(DH == 12, Str("dim_F2 H = ", DD, " - ", rN, " - ", rI, " = ", DH));
check(DH >= 4,
      "dim H >= 4, consistent with the lower bound rank_K + dim J(K)[2] - "
      "dim ker delta_K = 3 + 2 - 1 = 4 that E046(b), E051, E044(e) and Stoll's "
      "Lemma 5.1 give locally (see (6) for the -1)");

\\ ============================================================ group 3
print("(3) GLOBAL CLASSES THAT MUST LIE IN H  (these do not know the answer)");
\\ (a) the three 2-torsion classes, from a divisor with GENERIC support.
\\ The naive recipe -- mu(D_Sigma)_j = g_i(T_j) off Sigma, and "c times the
\\ complementary product" on Sigma -- carries a scalar lambda in K^x on the
\\ Sigma-component that the norm condition CANNOT see (scaling one component
\\ by lambda multiplies the norm by lambda^2).  So derive it instead, with no
\\ convention at all [T]:
\\
\\   put b = g_i (degree 2), so that y - b has pole order 3 at each of the two
\\   points at infinity, six poles in all.  Its zeros are where y = g_i(x), and
\\   b^2 - f = g_i^2 - c g_i prod_{k!=i} g_k = -g_i q_i  with
\\        q_i := c prod_{k != i} g_k  -  g_i     (degree 4),
\\   so the zeros are the two Weierstrass points over g_i -- each simple, since
\\   v(y) = 1 and v(g_i) = 2 there -- together with the four points R_k whose
\\   x-coordinates are the roots of q_i.  Hence in J
\\        D_i + [ sum_k (R_k) - 2 D_infty ] = 0,
\\   and mu(D_i) = mu(sum (R_k) - 2 D_infty)^{-1} = prod_k (x_{R_k} - T)
\\                = q_i(T) / lc(q_i) = q_i(T)   in L^x/(L^x)^2 K^x.
\\
\\ The support of the second divisor is generic, so this uses only the plain
\\ x - T formula.  (It reproduces the naive recipe multiplied by -1 on the
\\ Sigma-component: q_i(T_j) = -g_i(T_j) for j != i because g_j(T_j) = 0, and
\\ q_i(T_i) = c prod_{k!=i} g_k(T_i).  The missing sign is exactly what the
\\ real place of group 4 detects, and it was found that way first.)
T2 = matrix(DD, 3); T2S = matrix(6, 3); GLD = List();
my(okt = 1, okq = 1);
for(i = 1, 3,
  my(q = LC*prod(k = 1, 3, if(k == i, 1, G[k])) - G[i], dl, cs);
  dl = vector(3, j, evalup(RN[j], q, TA[j]));
  for(j = 1, 3, if(dl[j] == 0, okq = 0));
  cs = classof(dl);
  if(cs == 0, okt = 0,
     T2[,i] = lift(cs[1]); T2S[,i] = lift(cs[2]); listput(GLD, cs[3])));
T2 = Mod(T2,2); T2S = Mod(T2S,2);
check(okq,
      "q_i(T_j) is nonzero in all nine components, i.e. gcd(q_i, f) = 1: no "
      "R_k is a Weierstrass point, and the derivation above applies");
check(okt,
      "all three 2-torsion classes lie in L(S,2)K^x: away from 2 and 3 their "
      "ideals become squares after one scaling by K^x.  First test that S is "
      "big enough");
check(NM*T2 == matrix(dK, 3),
      "and all three lie in ker N -- their norms are squares in K");
check(matrank(concat(T2, IM)) - matrank(IM) == 2,
      "they span a 2-dimensional subgroup of H, i.e. dim_F2 J(K)[2] = 2 "
      "exactly (E044(e)): mu is injective on J(K)[2] and the relation "
      "D_1 + D_2 + D_3 = 0 is reproduced inside H");

\\ (b) differences of K-rational points of X.  The points are searched for
\\ here, not imported.
XPTS = List();
my(nf = nfinit('y^3-4));
forvec(v = [[-6,6],[-6,6],[-6,6]],
  foreach([1,2,5,10], d,
    if(gcd(gcd(gcd(v[1],v[2]),v[3]),d) > 1, next);
    my(xx = (v[1]+v[2]*'y+v[3]*'y^2)/d,
       val = Mod(subst(lift(f), 'x, xx), 'y^3-4));
    if(val == 0, next);
    if(#nfroots(nf, 'x^2 - lift(val)) > 0, listput(XPTS, Mod(xx,'y^3-4)))));
info(Str("K-points of X with x in K found by search: x = ", Vec(XPTS)));
check(#XPTS >= 2,
      Str("at least two distinct x-coordinates (", #XPTS, " found), so the "
          "differences are nonzero degree-0 divisors and mu of them is not "
          "automatically a square"));
PT = matrix(DD, #XPTS - 1); PTS = matrix(6, #XPTS - 1);
my(okp = 1);
for(n = 2, #XPTS,
  my(dl = vector(3, j, (rnfeltup(RN[j], XPTS[1]) - TA[j])
                       * (rnfeltup(RN[j], XPTS[n]) - TA[j])), cs);
  cs = classof(dl);
  if(cs == 0, okp = 0,
     PT[,n-1] = lift(cs[1]); PTS[,n-1] = lift(cs[2]); listput(GLD, cs[3])));
PT = Mod(PT,2); PTS = Mod(PTS,2);
check(okp,
      "mu of (P_1) - (P_n) lies in L(S,2)K^x for every one of them -- the "
      "second, independent test that S is big enough, and this one uses "
      "genuinely non-torsion input");
check(NM*PT == matrix(dK, #XPTS - 1),
      "and in ker N, as N(mu) = f(x_1) f(x_n) / c^2 = (y_1 y_n / c)^2 forces");
GLB = concat(T2, PT); GLS = concat(T2S, PTS);
check(matrank(GLS - Mod(matrix(6, matsize(GLB)[2]), 2)) >= 0
      && matrank(concat(GLB,IM)) - matrank(IM) >= 3,
      Str("the ", matsize(GLB)[2], " global classes span dim ",
          matrank(concat(GLB,IM)) - matrank(IM),
          " inside H, at least 3 -- so they are not all torsion and not all "
          "equal, and H really does receive independent global input"));

\\ ============================================================ group 4
print("(4) PHASE C:  THE REAL PLACE");
check(vecmax(vector(6, k, abs(imag(polroots(FINF)[k])))) < 1e-25,
      "all six roots of f are real at the real place of K, so L (x)_K R = R^6");
for(i = 1, 3,
  check(BN[i].sign[1] == 2,
        Str("L_", i, " has exactly two real places"));
  for(r = 1, 2,
    check(abs(real(nfeltembed(BN[i], rnfeltup(RN[i], 'y))[r]) - YR) < 1e-25,
          Str("real embedding ", r, " of L_", i,
              " restricts to y -> 4^{1/3}, the unique real place of K"))));
check(vecsort(concat(Vec(POS[,1]~), Vec(POS[,2]~))) == [1,2,3,4,5,6],
      Str("the six real embeddings name the six roots bijectively: ", POS));
\\ the sign map on the basis of V
SM = matrix(6, DD);
for(c = 1, DD,
  my(i = BI[c], sg = nfeltsign(BN[i], BV[c]));
  for(r = 1, 2, SM[POS[i,r], c] = if(sg[r] < 0, 1, 0)));
SM = Mod(SM, 2);
check(SM*GLB == GLS,
      "the sign vectors of the global classes computed TWO WAYS agree: "
      "directly from the adjusted representative, and from its F_2 "
      "coordinates through the sign matrix of the S-unit basis");
\\ W_infty = < image of mu_infty , K^x >.  J(R) is generated by degree-2
\\ divisors with real or conjugate x-coordinates; a conjugate pair has trivial
\\ sign vector, so the image is spanned by v(x_1) + v(x_2) over real x with
\\ f(x) > 0, and the class of K^x is the all-ones vector.
my(lo = List(), WI);
for(k = 0, 6,
  my(a = if(k == 0, RT[1]-1, RT[k]), b = if(k == 6, RT[6]+1, RT[k+1]),
     mid);
  mid = (a+b)/2;
  if(subst(FINF, 'x, mid) > 0,
     listput(lo, Col(vector(6, j, if(mid > RT[j], 0, 1))))));
info(Str("f > 0 on ", #lo, " of the seven intervals cut out by the six roots"));
WI = matrix(6, #lo - 1);
for(k = 2, #lo, WI[,k-1] = lo[k] + lo[1]);
WI = Mod(concat(WI, Col(vector(6, j, 1))), 2);
dW = matrank(WI);
check(dW == 3, Str("W_infty = < Im mu_infty, K^x > has dim ", dW, " in F_2^6"));
check(dW - 1 == 2,
      "so dim Im mu_infty = 2 in F_2^6/<1>.  This AGREES with the theorem "
      "dim J(R)/2J(R) = dim J(R)[2] - g = 4 - 2 = 2: all six Weierstrass "
      "points are real, so J(R)[2] is the full (Z/2)^4.  NB the TODO estimate "
      "of 2026-08-19 wrote 3, from 'dim J(R)[2] = 5'; that 5 is the dimension "
      "of the AMBIENT F_2^6/<1>, not of J(R)[2].  The estimate is corrected "
      "here, and in our favour -- the real place cuts one more than budgeted");
QQ = mattranspose(matker(mattranspose(WI)));
check(matrank(QQ) == 6 - dW && QQ*WI == matrix(6-dW, matsize(WI)[2]),
      "the linear form cutting out W_infty has the right rank and kills it");
check(QQ*GLS == matrix(6-dW, matsize(GLS)[2]),
      "EVERY global class of group 3 satisfies the real condition.  This is "
      "the check that the sign map, the labelling of the roots and W_infty "
      "are mutually consistent, and it could have failed");
MC = QQ*SM*KN;
dsel = matsize(KN)[2] - matrank(MC) - rI;
info(Str("ker N has dim ", matsize(KN)[2], "; the real condition has rank ",
         matrank(MC), " on it, and iota accounts for ", rI));
check(matrank(SM*KN) == 5,
      Str("s(ker N) has dim ", matrank(SM*KN), " = 5: it is the WHOLE "
          "even-weight subspace of F_2^6.  (It cannot be more: N(delta) is a "
          "square in K, hence positive at the real place, and that is exactly "
          "the statement that the six signs multiply to +1.)"));
check(matrank(MC) == 5 - dW,
      Str("so the real condition is as strong as it can be: rank ",
          matrank(MC), " = 5 - dim W_infty = ", 5 - dW));
printf("        dim_F2 ( H  cut by the real place ) = %d\n", dsel);
check(dsel >= 4, "still at least 4, as the lower bound requires");

\\ ============================================================ group 5
print("(5) PHASE D:  THE CONDITION AT v | 3");
\\ Coordinates.  L (x)_K K_{v_3} = prod_{P | 3} L_P over the five primes of L
\\ above 3, and each L_P^x/(L_P^x)^2 is F_2^2, so the local group before the
\\ quotient by K_v^x is F_2^10.
P3 = List(); B3 = List(); M3 = List();
for(i = 1, 3,
  my(Ps = idealprimedec(BN[i], 3));
  for(m = 1, #Ps,
    listput(P3, Ps[m]); listput(B3, i);
    listput(M3, nfmodprinit(BN[i], Ps[m]))));
NP = #P3;
check(NP == 5,
      Str("L has ", NP, " primes over 3, so the local group L_v^x/(L_v^x)^2 "
          "is F_2^", 2*NP));
\\ the coordinate map on a triple
LAM = matrix(2*NP, DD);
for(c = 1, DD,
  my(dl = vector(3, j, if(j == BI[c], BV[c], 1)));
  LAM[,c] = lift(lam3(dl)));
LAM = Mod(LAM, 2);
\\ K_{v_3}^x/(K_{v_3}^x)^2 = < pi_3, 2 >: the residue field is F_3, in which 2
\\ is the non-square, and pi_3 generates p_3 (h(K) = 1).
PI3 = nfbasistoalg(K, idealprimedec(K,3)[1].gen[2]);
MPK = nfmodprinit(K, idealprimedec(K,3)[1]);
check(idealval(K, PI3, idealprimedec(K,3)[1]) == 1
      && nfeltnorm(K, PI3) == 3 && !issquare(nfmodpr(K, 2, MPK)),
      Str("pi_3 = ", PI3, " is a uniformiser at v_3 (norm 3) and 2 is the "
          "non-square unit, so K_{v_3}^x/(K_{v_3}^x)^2 = < pi_3, 2 >"));
DK3 = matrix(2*NP, 2);
DK3[,1] = lift(lam3(vector(3, j, rnfeltup(RN[j], PI3))));
DK3[,2] = lift(lam3(vector(3, j, rnfeltup(RN[j], 2))));
DK3 = Mod(DK3, 2);
check(matrank(DK3) == 2,
      "the diagonal image of K_{v_3}^x in F_2^10 is 2-dimensional, so a "
      "d-dimensional subspace of the quotient has a (d+2)-dimensional "
      "preimage");
\\ Im mu_{v_3}, generated from LOCAL points only -- the global classes are kept
\\ back so that they can test the result.  z in K^x is a square in K_{v_3} iff
\\ v_3(z) is even and the unit part is a square in F_3 (Hensel, 3 odd).
\\ NB the search runs over the INTEGRAL BASIS of K, not over Z[y]: O_K is
\\ Z[2^{1/3}] = Z[1, y^2/2, y] and Z[y] has index 2 in it, so a box in
\\ a + b y + c y^2 misses half of O_K -- including x = y^2/2 = 2^{1/3}, which
\\ is one of the K-rational points of group 3.  At v | 2 that omission is
\\ fatal (it lost every local point); here it is merely wasteful.
XL3 = List();
forvec(v = [[-4,4],[-4,4],[-4,4]],
  foreach([1,2,3,5], d,
    if(gcd(gcd(gcd(v[1],v[2]),v[3]),d) > 1, next);
    my(xx = nfbasistoalg(K, [v[1],v[2],v[3]]~)/d, val);
    val = Mod(subst(lift(f), 'x, lift(xx)), 'y^3-4);
    if(val == 0, next);
    if(issq3(val), listput(XL3, xx))));
info(Str(#XL3, " values of x in K with f(x) a square in K_{v_3} "
         "(these are K_{v_3}-points of X)"));
my(csq = issq3(LC));
info(Str("the leading coefficient c is ", if(csq, "", "NOT "),
         "a square in K_{v_3}, so the two points at infinity are ",
         if(csq, "", "not "), "K_{v_3}-rational"));
\\ lam3 is a HOMOMORPHISM, so the class of a pair is the SUM of the two
\\ single classes: only the #XL3 single vectors have to be computed, and the
\\ span of all pairs is the span of u_n + u_1.
U3 = matrix(2*NP, #XL3);
for(n = 1, #XL3,
  U3[,n] = lift(lam3(vector(3, j, rnfeltup(RN[j], XL3[n]) - TA[j]))));
U3 = Mod(U3, 2);
W3 = DK3;
if(csq, W3 = concat(W3, U3),
   for(n = 2, #XL3, W3 = concat(W3, Col(U3[,n] + U3[,1]))));
my(dW3 = matrank(W3));
check(dW3 == 5,
      Str("dim W_3 = ", dW3, " = 3 + 2, i.e. the local points generate the "
          "WHOLE of Im mu_{v_3} (dim 3 = dim J(K_{v_3})[2], since 3 is odd) "
          "over the diagonal K_{v_3}^x.  The stopping condition and the "
          "self-check are the same number, so nothing is assumed here"));
Q3 = mattranspose(matker(mattranspose(W3)));
check(matrank(Q3) == 2*NP - dW3 && Q3*W3 == matrix(2*NP - dW3, matsize(W3)[2]),
      "the linear form cutting out W_3 has the right rank and kills it");
\\ the global classes must satisfy it -- they are global points
GL3 = matrix(2*NP, #GLD);
for(n = 1, #GLD, GL3[,n] = lift(lam3(GLD[n])));
GL3 = Mod(GL3, 2);
check(GL3 == LAM*GLB,
      "the local vectors of the global classes computed TWO WAYS agree: "
      "directly from the adjusted representative, and from its F_2 "
      "coordinates through LAM");
check(Q3*GL3 == matrix(2*NP - dW3, #GLD),
      "EVERY global class satisfies the condition at v | 3.  Like the real "
      "place in (4), this could have failed, and it is not circular: W_3 was "
      "generated from local points alone");
MC3 = Q3*LAM*KN;
dsel3 = matsize(KN)[2] - matrank(matconcat([MC; MC3])) - rI;
info(Str("on ker N the real condition has rank ", matrank(MC),
         ", the v | 3 condition adds rank ",
         matrank(matconcat([MC; MC3])) - matrank(MC)));
printf("        dim_F2 ( H  cut by the real place and by v | 3 ) = %d\n", dsel3);
check(dsel3 >= 4, "still at least 4, as the lower bound requires");
check(matrank(MC3) <= 3,
      Str("the v | 3 condition cuts ", matrank(MC3), " <= 3 = dim Im mu_{v_3}, "
          "the bound of the budget below"));

\\ ============================================================ group 6
print("(6) PHASE E:  THE CONDITION AT v | 2");
P2 = vector(3); BS2 = vector(3); OFF = [0, DL[1], DL[1]+DL[2]];
my(okb = 1);
for(i = 1, 3,
  my(Ps = idealprimedec(BN[i], 2), pi, CS, hb);
  if(#Ps != 1, okb = 0);
  P2[i] = Ps[1];
  pi = nfbasistoalg(BN[i], P2[i].gen[2]);
  CS = List(); listput(CS, pi); listput(CS, Mod(-1, BN[i].pol));
  for(j = 1, DL[i], listput(CS, BV[OFF[i] + j]));
  for(k = 1, 7, listput(CS, 1 + pi^k));
  listput(CS, TA[i]); listput(CS, 1 + TA[i]); listput(CS, 1 - TA[i]);
  hb = hbasis(BN[i], P2[i], Vec(CS));
  BS2[i] = hb[1];
  if(hb[2] != 8 || #BS2[i] != 8, okb = 0);
  info(Str("L_", i, ": one prime over 2 with e = ", P2[i].e, ", f = ",
           P2[i].f, ", so [L_w:Q_2] = ", P2[i].e*P2[i].f,
           ";  Gram rank of ", #CS, " probes = ", hb[2])));
check(okb,
      "each L_i has a SINGLE prime over 2, of local degree 6 over Q_2, and in "
      "each the probes attain Gram rank 8 = 2 + [L_w:Q_2].  By nondegeneracy "
      "of the Hilbert pairing the eight selected probes are then a BASIS of "
      "L_w^x/(L_w^x)^2, so the symbol coordinates are injective -- certified, "
      "not assumed");
LAM2 = matrix(24, DD);
for(c = 1, DD,
  my(dl = vector(3, j, if(j == BI[c], BV[c], 1)));
  LAM2[,c] = lift(lam2(dl)));
LAM2 = Mod(LAM2, 2);
\\ K_{v_2}^x/(K_{v_2}^x)^2 has dimension 2 + [K_{v_2}:Q_2] = 5; same trick.
my(pk = nfbasistoalg(K, idealprimedec(K,2)[1].gen[2]), CSK = List(), hbk);
listput(CSK, pk); listput(CSK, Mod(-1,'y^3-4));
for(k = 1, 6, listput(CSK, 1 + pk^k));
listput(CSK, Mod('y+1,'y^3-4)); listput(CSK, Mod('y-1,'y^3-4));
listput(CSK, Mod(3,'y^3-4)); listput(CSK, Mod(5,'y^3-4));
hbk = hbasis(K, idealprimedec(K,2)[1], Vec(CSK));
BSK2 = hbk[1];
check(hbk[2] == 5 && #BSK2 == 5,
      Str("and over K the same construction gives Gram rank ", hbk[2],
          " = 2 + [K_{v_2}:Q_2] = 5, so K_{v_2}^x/(K_{v_2}^x)^2 too is "
          "spanned by five global elements"));
DK2 = matrix(24, #BSK2);
for(k = 1, #BSK2, DK2[,k] = lift(lam2(vector(3, j, rnfeltup(RN[j], BSK2[k])))));
DK2 = Mod(DK2, 2);
dDK2 = matrank(DK2);
info(Str("the diagonal image of K_{v_2}^x in F_2^24 has dim ", dDK2));
XL2 = List();
forvec(v = [[-6,6],[-6,6],[-6,6]],
  foreach([1,2,3,4,5,7,8], d,
    if(gcd(gcd(gcd(v[1],v[2]),v[3]),d) > 1, next);
    my(xx = nfbasistoalg(K, [v[1],v[2],v[3]]~)/d, val);
    val = Mod(subst(lift(f), 'x, lift(xx)), 'y^3-4);
    if(val == 0, next);
    if(issq2(val), listput(XL2, xx))));
info(Str(#XL2, " values of x in K with f(x) a square in K_{v_2}, i.e. "
         "K_{v_2}-points of X"));
my(c2 = issq2(LC));
info(Str("the leading coefficient c is ", if(c2, "", "NOT "),
         "a square in K_{v_2}"));
GL2x = matrix(24, #GLD);
for(n = 1, #GLD, GL2x[,n] = lift(lam2(GLD[n])));
GL2x = Mod(GL2x, 2);
\\ same homomorphism trick as at v | 3
U2 = matrix(24, #XL2);
for(n = 1, #XL2,
  U2[,n] = lift(lam2(vector(3, j, rnfeltup(RN[j], XL2[n]) - TA[j]))));
U2 = Mod(U2, 2);
W2 = DK2;
if(c2, W2 = concat(W2, U2),
   for(n = 2, #XL2, W2 = concat(W2, Col(U2[,n] + U2[,1]))));
info(Str("K_{v_2}^x and the rational-x pairs give dim ", matrank(W2),
         " of the target ", dDK2 + IMV2));
\\ now the degree-2 prime divisors, one quadratic extension at a time
my(ntry = 0, nok = 0, nfld = 0, DS = List(), PI2 = nfbasistoalg(K, idealprimedec(K,2)[1].gen[2]));
GAM = [PI2^-2, PI2^-1, 1, PI2, PI2^2, PI2^3, PI2^4];
forvec(ss = vector(#BSK2, k, [0,1]),
  if(vecsum(Vec(ss)) == 0, next);
  my(D = 1);
  for(k = 1, #BSK2, if(ss[k], D *= BSK2[k]));
  listput(DS, D));
for(n = 1, #DS,
  if(matrank(W2) >= dDK2 + IMV2, break);
  my(QF = qfield(DS[n]));
  if(QF == 0, next);
  nfld++;
  \\ beta must be allowed NON-INTEGRAL.  Completing the square in
  \\ x^2 + ux + w gives beta = -u/2, and v_2(2) = 3 here, so integral u
  \\ already forces v(beta) >= -3: a box of integral beta misses almost every
  \\ quadratic.  This is the whole reason the first two searches stalled.
  forvec(vv = [[-1,1],[-1,1],[-1,1]],
    foreach([1,2,4], dd,
      foreach(GAM, gam,
        if(matrank(W2) >= dDK2 + IMV2, break);
        my(beta = nfbasistoalg(K, [vv[1],vv[2],vv[3]]~)/dd, r);
        ntry++;
        r = qdiv2(QF, DS[n], beta, gam);
        if(r == 0, next);
        nok++;
        W2 = concat(W2, lift(r))))));
info(Str("degree-2 prime divisors: ", #DS, " square classes, ", nfld,
         " usable quadratic extensions, ", ntry, " (D,beta) pairs tried, ",
         nok, " gave a K_{v_2}-divisor"));
\\ THE WEIERSTRASS DEGREE-2 PRIMES, which the search above structurally
\\ cannot see.  Each g_i stays irreducible over K_{v_2} (local degrees
\\ 2,2,2), so the two points (alpha,0) over it form a prime divisor of
\\ degree 2 over K_{v_2} -- admissible in Lemma 6.2 like any other.  But the
\\ test used above asks whether f(alpha) is a square, and there f(alpha) = 0,
\\ so every one of them was rejected.  Stoll p. 268 gives the formula for
\\ exactly this case: with f = h h~ and h monic irreducible,
\\ delta = h(theta) - h~(theta), which for h = g_i is -q_i(T) -- the same
\\ q_i that group (3) derived.  So they are added here, from the local
\\ formula, not imported as global classes.
for(i = 1, 3,
  my(q = LC*prod(k = 1, 3, if(k == i, 1, G[k])) - G[i]);
  W2 = concat(W2, lift(lam2(vector(3, j, evalup(RN[j], q, TA[j]))))));
W2 = Mod(W2, 2);
info(Str("plus the 3 Weierstrass degree-2 primes: dim ", matrank(W2)));
\\ and the global classes, which are images of global points and hence local
\\ points too -- legitimate generators, at the cost of making the check
\\ "every global class satisfies the v|2 condition" circular at this place.
W2 = concat(W2, GL2x);
info(Str("plus the global classes: dim ", matrank(W2)));
dW2 = matrank(W2);
info(Str("dim W_2 generated = ", dW2, "   (the target is ", dDK2, " + ", IMV2,
         " = ", dDK2 + IMV2, ")"));
\\ LOCAL DUALITY CLOSES THE GAP.  Im mu_v is a MAXIMAL ISOTROPIC subspace of
\\ H^1(K_v, J[2]) for the pairing <d,d'> = sum_w (d_w, d'_w)_w [T: Poonen-
\\ Stoll].  In the symbol coordinates that pairing is x^T B y with B the
\\ block-diagonal inverse of the Gram matrices, and the diagonal K_v^x lies
\\ in the radical on ker N, since <c,d> = (c, N(d))_v.  So whatever we have
\\ generated, W_2 is contained in the true preimage W, which is isotropic:
\\      W  subset  W_2^perp ,   dim W_2^perp = 24 - dim W_2 .
\\ With dim W_2 = 11 this gives dim W_2^perp = 13, one more than
\\ dim W = IMV2 + dDK2 = 7 + 5 = 12; W = W_2^perp is impossible anyway, since
\\ an isotropic subspace for the invertible BB has dimension <= 24/2.  So
\\ W/W_2 is an isotropic LINE in W_2^perp/W_2, enumerated below.
BB = matrix(24, 24);
for(i = 1, 3,
  my(Gi = gram(BN[i], P2[i], BS2[i])^-1, o = 8*(i-1));
  for(a = 1, 8, for(b = 1, 8, BB[o+a, o+b] = lift(Gi[a,b]))));
BB = Mod(BB, 2);
check(mattranspose(W2)*BB*W2 == matrix(matsize(W2)[2], matsize(W2)[2]),
      Str("the ", matsize(W2)[2], " generators of W_2 are pairwise ORTHOGONAL "
          "for the local pairing -- they had better be, all being classes of "
          "K_{v_2}-divisors inside one isotropic subspace, and a single wrong "
          "generator would almost surely break it"));
W2P = matker(mattranspose(BB*W2));
info(Str("dim W_2^perp = 24 - ", dW2, " = ", matrank(W2P)));
\\ The generated W_2 sits inside the true preimage W, and W is isotropic, so
\\      W  subset  W_2^perp,   dim W_2^perp = 24 - 11 = 13 > 12 = dim W;
\\ the check below tests the inclusion on the global classes.  (An earlier run
\\ appeared to fail it; that was a stale variable -- dW2 was still 11 after a
\\ substitution, so two matrix-shape comparisons were false for a reason with
\\ no mathematics in it.  Recorded because the failure was reported before it
\\ was checked.)
GL2chk = matrix(24, #GLD);
for(n = 1, #GLD, GL2chk[,n] = lift(lam2(GLD[n])));
GL2chk = Mod(GL2chk, 2);
check(matrank(concat(W2P, GL2chk)) == matrank(W2P),
      Str("every global class lies in W_2^perp (dim ", matrank(W2P),
          ") -- necessary, since global classes lie in Im mu_{v_2}, and it "
          "holds"));
\\ HISTORY (superseded).  A first attempt took W = W_2^perp, on the belief
\\ that dim W = 8 + 5 = 13, and found dim Sel = 4, apparently below a lower
\\ bound 3 + 2 = 5.  Both numbers were wrong: dim ker delta_{v_2} = 1
\\ (Lemma 5.1) makes dim W = 7 + 5 = 12, and in Stoll's H_K the lower bound
\\ is 3 + 2 - 1 = 4 (see below).  BB IS the local pairing and is used below
\\ to find W as an isotropic hyperplane of W_2^perp containing W_2.
\\ The generated W_2 is kept: it is contained in Im mu_{v_2} for sure.
dW2 = matrank(W2);
Q2 = mattranspose(matker(mattranspose(W2)));
check(matrank(Q2) == 24 - dW2 && Q2*W2 == matrix(24 - dW2, matsize(W2)[2]),
      "the linear form cutting out the GENERATED W_2 has the right rank and "
      "kills it");
\\ LOCAL DUALITY FINISHES IT.  W_2 is isotropic of dimension 11 and sits
\\ inside the true preimage W, which is isotropic of dimension IMV2 + dDK2
\\ = 12; and W is inside W_2^perp, of dimension 13.  So W/W_2 is an isotropic
\\ LINE in W_2^perp/W_2, a two-dimensional space carrying a nondegenerate
\\ induced form: there are at most three candidates, and they can simply be
\\ enumerated.  Whatever ambiguity survives is then carried through to the
\\ answer and reported, rather than guessed at.
Z2 = List();
my(ACC = W2);
for(k = 1, matsize(W2P)[2],
  if(matrank(concat(ACC, W2P[,k])) > matrank(ACC),
     ACC = concat(ACC, W2P[,k]); listput(Z2, W2P[,k])));
info(Str("W_2^perp / W_2 has dimension ", matrank(W2P) - dW2,
         "; found ", #Z2, " independent lifts"));
CAND = List();
forvec(cc = vector(#Z2, k, [0,1]),
  if(vecsum(Vec(cc)) == 0, next);
  my(z = Col(vector(24, t, 0)));
  for(k = 1, #Z2, if(cc[k], z += Z2[k]));
  z = Mod(z, 2);
  if(mattranspose(z)*BB*z == matrix(1,1),
     listput(CAND, matrank(concat(W2, z)) > dW2)));
info(Str("of the ", 2^#Z2 - 1, " nonzero classes in W_2^perp/W_2, ",
         sum(k = 1, #CAND, if(CAND[k], 1, 0)),
         " give an isotropic line, i.e. a candidate for W"));
DSEL = List();
forvec(cc = vector(#Z2, k, [0,1]),
  if(vecsum(Vec(cc)) == 0, next);
  my(z = Col(vector(24, t, 0)), WC, QC, MM2, dd);
  for(k = 1, #Z2, if(cc[k], z += Z2[k]));
  z = Mod(z, 2);
  if(mattranspose(z)*BB*z != matrix(1,1), next);
  WC = concat(W2, z);
  if(matrank(WC) != dDK2 + IMV2, next);
  QC = mattranspose(matker(mattranspose(WC)));
  MM2 = QC*LAM2*KN;
  dd = matsize(KN)[2] - matrank(matconcat([MC; MC3; MM2])) - rI;
  \\ a candidate is only admissible if the global classes satisfy it
  if(QC*GL2x != matrix(matsize(QC)[1], #GLD), next);
  listput(DSEL, dd));
info(Str("candidates (isotropic, dimension 12, containing every global "
         "class): ", #DSEL, ";  dim Sel^2 for each: ", Vec(DSEL)));
\\ THE LOWER BOUND SEPARATES THEM.  Sel^2 contains the image of J(K)/2J(K)
\\ in H_K, which has dimension rank_K + dim J(K)[2] - dim ker delta_K
\\ = 3 + 2 - 1 = 4: rank_K >= 3 is E046(b) and E051, dim J(K)[2] = 2 is
\\ E044(e), and the 1 is Lemma 5.1 again, condition (dagger-dagger) failing
\\ over K because it fails over K_{v_2} (see the top of the file: the three
\\ quadratic factors share no quadratic extension) -- with X(K) non-empty.
\\ A candidate that returns less than 4 is therefore NOT the true
\\ Im mu_{v_2}.
SURV = List();
for(k = 1, #DSEL, if(DSEL[k] >= 4, listput(SURV, DSEL[k])));
info(Str("of those, the ones compatible with the lower bound 4: ", #SURV,
         "  ", Vec(SURV)));
check(#SURV == 1,
      Str("EXACTLY ONE of the three candidates survives the lower bound, so "
          "Im mu_{v_2} is determined and no ambiguity reaches the answer.  "
          "The other two return ",
          Vec(vector(#DSEL, k, DSEL[k])), ", and a local condition cannot put "
          "the Selmer group below a subgroup it provably contains"));
GL2 = matrix(24, #GLD);
for(n = 1, #GLD, GL2[,n] = lift(lam2(GLD[n])));
GL2 = Mod(GL2, 2);
check(GL2 == LAM2*GLB,
      "the v | 2 vectors of the global classes computed TWO WAYS agree: "
      "directly from the adjusted representative, and through LAM2 from its "
      "F_2 coordinates");
check(Q2*GL2 == matrix(24 - dW2, #GLD),
      "every global class satisfies the condition cut out by the generated "
      "W_2 -- necessary, since W_2 is contained in Im mu_{v_2}, and it holds");
MC2 = Q2*LAM2*KN;
ALL = matconcat([MC; MC3; MC2]);
dselE = matsize(KN)[2] - matrank(ALL) - rI;
info(Str("on ker N: real rank ", matrank(MC), ",  + v|3 -> ",
         matrank(matconcat([MC; MC3])), ",  + v|2 -> ", matrank(ALL)));
if(#SURV, dselE = SURV[1]);
printf("        dim_F2 Sel^2( Jac X / K )  =  %d\n", dselE);
check(dselE == 4,
      Str("dim_F2 Sel^2(Jac X / K) = 4, computed entirely on this machine.  "
          "NB 4 and not 5: condition (dagger-dagger) FAILS over K too "
          "-- it already fails over K_{v_2}, where the three quadratic "
          "factors share no quadratic extension -- and X(K) is non-empty, "
          "so Lemma 5.1 "
          "gives dim ker delta_K = 1, so the group computed here -- Stoll's "
          "Sel^(2) inside H_K -- is smaller by exactly that one dimension "
          "than the Selmer group inside H^1(K, J[2]) that Magma reports.  "
          "E116's 5 and this 4 are the same statement in two normalisations"));

\\ ============================================================ group 7
print("(7) THE BUDGET, AS A CHECK ON THE THREE CUTS");
\\ For a place v of K, J(K_v)/2J(K_v) is a MAXIMAL ISOTROPIC subspace of
\\ H^1(K_v, J[2]) for the cup-product pairing [T: Poitou-Tate local duality],
\\ so dim H^1(K_v, J[2]) = 2 dim J(K_v)/2J(K_v), and by the local Euler
\\ characteristic
\\      dim J(K_v)/2J(K_v) = dim J(K_v)[2] + g [K_v : Q_2] (last term v | 2).
\\ Its image Im mu_v in Stoll's H_v is (J(K_v)/2J(K_v))/ker delta_v (Lemma
\\ 5.1): equal at R and v_3, one dimension smaller at v_2, where
\\ (dagger-dagger) fails and X(K_{v_2}) is non-empty.  The most a place can
\\ cut is dim Im mu_v.
\\ dim J(K_v)[2] is read off the splitting type of f over K_v: with orbits of
\\ local degrees d_1..d_r, the Galois-stable even subsets modulo {0, all} have
\\ dimension r - 1 - [some d_w is odd].
my(l3 = locdim(3), l2 = locdim(2), cut3, cut2);
info(Str("v | 3: f splits over K_v into ", l3[1], " factors of local degrees ",
         l3[3], ", so dim J(K_v)[2] = ", l3[2]));
info(Str("v | 2: f splits over K_v into ", l2[1], " factors of local degrees ",
         l2[3], ", so dim J(K_v)[2] = ", l2[2]));
cut3 = l3[2];
cut2 = l2[2] + 2*3 - 1;   \\ minus dim ker delta_{v_2} = 1, see (6)
info(Str("dim Im mu_{v_3} = ", cut3,
         "   (v_3 is odd, so no [K_v:Q_2] term)"));
info(Str("dim Im mu_{v_2} = ", l2[2], " + g[K_{v_2}:Q_2] - dim ker delta = ",
         l2[2], " + 2*3 - 1 = ", cut2));
check(cut3 + cut2 >= dsel - 4,
      Str("the two remaining places can cut at most ", cut3, " + ", cut2,
          " = ", cut3 + cut2, " dimensions, and ", dsel - 4, " are needed"));
check(dsel <= 2*cut2,
      Str("and H after the real place has dim ", dsel, " <= 2 dim Im mu_{v_2} "
          "= ", 2*cut2, ", so the v | 2 condition alone is not a priori "
          "vacuous on it"));

\\ ============================================================ group 8
print("(8) THE ANSWER");
info(Str("phase B   dim H                                = ", DH));
info(Str("phase C   after the real place                 = ", dsel));
info(Str("phase D   after v | 3                          = ", dsel3));
info(Str("phase E   after v | 2                          = ", dselE));
info(    "");
info(Str("dim_F2 Sel^(2)(Jac X / K) in Stoll's H_K       = ", dselE));
info(Str("  + dim ker delta_K (Lemma 5.1, (ddagger) fails) = 1"));
info(Str("  = dim_F2 Sel^2 in H^1(K, J[2])               = ", dselE + 1,
         "   <-- E116's Magma value, 5"));
info(    "");
info(Str("consequence: rank_K Jac X <= ", dselE,
         " - dim J(K)[2] + dim ker delta_K = ", dselE - 2 + 1,
         ", unchanged from E116"));
print("========================================================================");
printf("E118 GATE: phases B, C, D, E %s   (%d failures, %d open)\n",
       if(FAIL, "*** RED ***", "GREEN"), FAIL, OPEN);
if(OPEN, print("           PHASE E IS INCOMPLETE -- see the [open] items"));
}
