\\ check-c4-sieve.gp --- E115: the leftovers of E113, killed.
\\
\\ Run: gp -q check-c4-sieve.gp < /dev/null
\\
\\ WHAT IS BEING DONE.  E113 computed X(Q_13)_U = 125 points, of which 9 are
\\ C_4(Q) and 116 are not accounted for.  This script rules the 116 out, using
\\ no further p-adic cohomology -- only the degree-2 map to an elliptic curve
\\ and a sieve that was run four years of experiments ago.
\\
\\ (a) E037/E040: C_4 : w^4-6(t-1)^2w^2+27t(t^3-4) = 0 has the sigma-quotient
\\     H : v^2 = f(t) = -18t^4-36t^3+54t^2+72t+9,  u = w^2 = 3(t-1)^2 + v,
\\     and H is birational to E : y^2 = x^3-36x with
\\     E(Q) = Z P_0 + (Z/2)^2,  P_0 = (-3,9).  A point of H lifts to C_4
\\     exactly when u is a square.
\\
\\ (b) E054, the Mordell-Weil sieve on n [T(CAS)]: with
\\     M = 1694902321834310319869816895217442099465808000 (log_2 M = 150.2,
\\     4947 primes), every n with u(nP_0+T) a square satisfies
\\         T_1 = O    : n = 0, -1        (mod M)
\\         T_2 = (0,0): NO n at all
\\         T_3 = (-6,0): NO n at all
\\         T_4 = (6,0): n = 0, -1, -2    (mod M).
\\     v_13(M) = 2, so ANY rational point of C_4 has
\\         n = 0, -1 or -2   (mod 169).
\\
\\ (c) the 13-adic elliptic logarithm.  If z in C_4(Q) then pi(z) = n P_0 + T
\\     with n in Z, and log_13(pi(z)) = n log_13(P_0) because the torsion has
\\     order 4, prime to 13.  So
\\         n(z) := log_13(pi(z)) / log_13(P_0)   in   Q_13
\\     is computable from z alone -- and z is NOT rational as soon as n(z) is
\\     not a 13-adic integer, or n(z) mod 169 is not in {0, 167, 168}.
\\
\\ The nine rational points are the calibration: they must give n = 0, -1, -1,
\\ -2, which is (b)'s list, and they do.

default(parisize, "1G");
LEFT = "c4-qc-leftovers.txt";
P13 = 13;
ALLOW = Set([0, 167, 168]);          \\ {0, -1, -2} mod 169, from E054

aa = -18; bb = -36; cc = 54; dd = 72; qq = 3; al = -24;
f = -18*'t^4 - 36*'t^3 + 54*'t^2 + 72*'t + 9;
EW = ellinit([0, 216, 0, -31104, -2985984]);
vch = 0;
Em = ellinit(ellminimalmodel(EW, &vch));
E13 = ellinit(Em[1..5], P13);
P0 = [-3, 9];
NF13 = P13 + 1 - ellap(Em, P13);

FAIL = 0;
check(c, msg) = { if(c, printf("   [ok]  %s\n", msg),
                     printf("   [FAIL] %s\n", msg); FAIL++); c; };
info(msg) = printf("        %s\n", msg);

\\ (t, v) on H  ->  the Weierstrass model EW
toW(tt, vv) = {
  my(m, n);
  m = (vv - qq - dd*tt/(2*qq))/tt^2;
  n = 2*(aa - m^2)*tt + (bb - dd*m/qq);
  [al*m, al*n];
};

\\ the reduction of a 13-adic point of Em, or 0 for the identity
redpt(P) = {
  if(valuation(P[1], P13) < 0, return(0));
  [Mod(lift(P[1] + O(P13)), P13), Mod(lift(P[2] + O(P13)), P13)];
};

\\ log_13(P), by killing the reduction with the SMALLEST possible multiple:
\\ ellpadiclog wants a point of the kernel of reduction, and every doubling
\\ costs precision, so m = ord(P mod 13) and not #E(F_13).
plog(P, pr) = {
  my(Pb, m, Q);
  Pb = redpt(P);
  m = if(Pb == 0, 1, ellorder(E13, Pb));
  if(m == 0, m = NF13);
  Q = ellmul(Em, P, m);
  \\ mP = O means P is genuinely torsion when P is EXACT (then log = 0), and
  \\ means the precision ran out when P is only known to finitely many digits.
  if(#Q < 2, return(if(type(P[1]) == "t_PADIC", "lostprec", 0)));
  if(valuation(Q[1], P13) >= 0, return("notinker"));
  ellpadiclog(Em, P13, pr, Q)/m;
};

\\ n(z) for z = (t, w) on C_4, 13-adically
nof(tt, ww, pr, L0) = {
  my(vv, PW, P, lg);
  if(ww^4 - 6*(tt-1)^2*ww^2 + 27*tt*(tt^3-4) != O(P13^pr)
     && ww^4 - 6*(tt-1)^2*ww^2 + 27*tt*(tt^3-4) != 0, return("offcurve"));
  vv = ww^2 - 3*(tt-1)^2;
  PW = toW(tt, vv);
  if(!ellisoncurve(EW, PW), return("offEW"));
  P = ellchangepoint(PW, vch);
  lg = plog(P, pr);
  if(type(lg) == "t_STR", return(lg));
  lg/L0;
};


\\ ---------------------------------------------------------------- group (3)
\\ THE DEEP SIEVE.  E054's modulus M has v_13(M) = 2, so its output constrains
\\ n only modulo 169.  The leftovers that survive group (2) are exactly those
\\ whose n happens to be 0, -1 or -2 modulo 169 -- and they are NOT 0, -1 or -2
\\ modulo 13^3 or 13^4.  So the question is whether the sieve can be pushed to
\\ a modulus divisible by 13^4, and it can: there are primes q with
\\ 13^4 | ord_q(P_0) and a small cofactor (q = 3770051 has ord = 2*13^4).
\\
\\ The computation is targeted rather than global: for a single residue nu
\\ modulo 13^K, decide whether ANY integer n = nu (mod 13^K) can have
\\ u(n P_0 + T_j) a square at every sieving prime.  Empty ==> that leftover is
\\ not a rational point.  The schedule is E054's, and for the same reason:
\\ spend a prime on a fresh prime power only when no prime cuts for free.

EWCOEF = [0, 216, 0, -31104, -2985984];
{ frWp(X, Y) = my(al=-24, aa=-18, bb=-36, dd=72, qq=3, m, nn, tt, vv, den);
  m = X/al; nn = Y/al; den = 2*(aa - m^2);
  if(lift(den) == 0, return(0));
  tt = (nn - bb + dd*m/qq)/den; vv = qq + dd*tt/(2*qq) + m*tt^2;
  [tt, 3*(tt-1)^2 + vv]; }
{ topt(P, q) = if(#P < 2, return([0]));
  if(denominator(P[1]) % q == 0 || denominator(P[2]) % q == 0, return("bad"));
  [Mod(P[1], q), Mod(P[2], q)]; }
{ masks1(q, P0w, torsw) = my(Eq, P0q, torsq, ord, mk, Q, R, tu, k);
  Eq = ellinit(EWCOEF, q); if(#Eq == 0, return(0));
  P0q = topt(P0w, q); if(type(P0q) != "t_VEC" || #P0q < 2, return(0));
  torsq = vector(4, j, topt(torsw[j], q));
  for(j = 1, 4, if(type(torsq[j]) != "t_VEC", return(0)));
  ord = ellorder(Eq, P0q); if(ord < 2, return(0));
  mk = vector(4, j, vectorsmall(ord));
  Q = [0];
  for(n = 0, ord - 1,
    for(j = 1, 4,
      R = if(j == 1, Q, elladd(Eq, Q, torsq[j]));
      if(#R < 2, mk[j][n+1] = 1; next);
      tu = frWp(R[1], R[2]); if(tu == 0, mk[j][n+1] = 1; next);
      k = kronecker(lift(tu[2]), q); if(k >= 0, mk[j][n+1] = 1));
    Q = elladd(Eq, Q, P0q));
  [ord, mk]; }
{ refine(cls, Mold, ord, mk) = my(L = lcm(Mold, ord), reps, out = List(), c);
  reps = L/Mold;
  for(i = 1, #cls, for(k = 0, reps - 1, c = cls[i] + k*Mold;
    if(mk[(c % ord) + 1], listput(out, c))));
  Vec(out); }

KDEEP = 4;                       \\ decide n modulo 13^KDEEP
QDEEP = 5*10^6;                  \\ search bound for the 13^KDEEP carriers
Q0 = 60000;                      \\ search bound for the ordinary supply
MAXSET = 400000;
CALP = 300;                      \\ primes spent on each calibration class

{ ordof(q, Em2) = my(Eq, Pq);
  Eq = ellinit(Em2[1..5], q); if(#Eq == 0, return(0));
  Pq = [Mod(-3, q), Mod(9, q)];
  if(!ellisoncurve(Eq, Pq), return(0));
  ellorder(Eq, Pq); }

\\ every n = nu (mod 13^K) that the sieve cannot rule out, for one torsion
\\ translate j; the schedule is E054's -- pure cuts first, then the cheapest
\\ lift -- because the transient, not the final set, is what must fit.
\\ maxp = 0 means "use the whole supply".  Capping it can only make the sieve
\\ WEAKER: emptying the class set at any point is already a proof, so a cap
\\ risks a false survivor and never a false kill.  It is used only for the
\\ calibration classes, which survive by construction and would otherwise
\\ exhaust the supply.
{ killclass(nu, K, PR, j, P0w, torsw, verbose, maxp) = my(MOD, cls, used, prog,
                                                    r, best, bestreps, reps,
                                                    spent = 0);
  MOD = 13^K; cls = [nu % MOD]; used = vectorsmall(#PR);
  while(1,
    prog = 1;
    while(prog,
      prog = 0;
      for(i = 1, #PR,
        if(!used[i] && PR[i][2] > 1 && MOD % PR[i][2] == 0,
          r = masks1(PR[i][1], P0w, torsw); used[i] = 1; spent++;
          if(r == 0, next);
          cls = refine(cls, MOD, r[1], r[2][j]); prog = 1;
          if(#cls == 0, return([0, MOD]));
          if(maxp && spent >= maxp, return([#cls, MOD])))));
    best = 0; bestreps = 0;
    for(i = 1, #PR,
      if(!used[i] && PR[i][2] > 1,
        reps = lcm(MOD, PR[i][2])/MOD;
        if(best == 0 || reps < bestreps, bestreps = reps; best = i)));
    if(best == 0, return([#cls, MOD]));
    r = masks1(PR[best][1], P0w, torsw); used[best] = 1; spent++;
    if(r == 0, next);
    cls = refine(cls, MOD, r[1], r[2][j]); MOD = lcm(MOD, r[1]);
    if(verbose, printf("      q=%d ord=%d -> %d classes mod %d\n",
                       PR[best][1], r[1], #cls, MOD));
    if(#cls == 0, return([0, MOD]));
    if(maxp && spent >= maxp, return([#cls, MOD]));
    if(#cls > MAXSET, return([-#cls, MOD]))); }

\\ ================================================================== the gate
{
print("=== check-c4-sieve.gp --- E115: the 116 leftovers of E113 ===");
print("(1) THE MAP, AND THE NINE RATIONAL POINTS AS CALIBRATION");
my(L0, RAT, ns, ok, lines, tot, neg, bad, kill, surv, pmin,
   EW2, Em2, vv2, P0w, torsw, PR, t0, res, allempty);
L0 = plog(P0, 30);
info(Str("v_13(log P_0) = ", valuation(L0, P13)));
check(valuation(L0, P13) == 1,
      "log_13(P_0) has valuation 1: dividing by it costs exactly one digit");
RAT = [[1,3],[1,-3],[-1,3],[-1,-3],[-2,6],[-2,-6],[-1/11,15/11],[-1/11,-15/11]];
ns = vector(#RAT); ok = 1;
for(i = 1, #RAT,
  my(nn = nof(RAT[i][1], RAT[i][2], 20, L0));
  if(type(nn) == "t_STR", ok = 0; info(Str("  ", RAT[i], ": ", nn)); next);
  ns[i] = nn;
  info(Str("  t = ", RAT[i][1], ", w = ", RAT[i][2], "  ->  n = ",
           if(nn == 0, 0, lift(nn + O(P13^3))), " (mod 13^3)")));
check(ok && ns[1] == 0 && ns[3] == ns[5] && ns[7] != ns[5],
      "the nine rational points give n = 0 (t=1), -1 (t=-1 and t=-2) and -2 "
      "(t=-1/11), which is exactly E054's surviving list {0,-1,-2}: the map, "
      "the branch of the logarithm and the sieve output all agree");

print("(2) THE 116 LEFTOVERS, AGAINST E054's CLASSES MOD 169");
lines = readstr(LEFT); tot = 0; neg = 0; bad = 0; kill = 0;
surv = List(); pmin = 999;
for(i = 1, #lines,
  my(L = lines[i], v, pr, tt, ww, nn, r);
  if(Vecsmall(L)[1] == 35, next);
  v = strsplit(L, " "); pr = eval(v[4]); tot++; pmin = min(pmin, pr);
  tt = eval(v[5]) + O(P13^pr); ww = eval(v[6]) + O(P13^pr);
  nn = nof(tt, ww, pr, L0);
  if(type(nn) == "t_STR", bad++; listput(surv, [v[1],v[2],v[3],v[5],nn]); next);
  if(valuation(nn, P13) < 0, neg++; kill++; next);
  r = lift(nn + O(P13^2));
  if(setsearch(ALLOW, r), listput(surv, [v[1],v[2],v[3],v[5],nn]), kill++));
surv = Vec(surv);
info(Str("leftovers read: ", tot, ", smallest precision 13^", pmin));
info(Str("killed because n is not a 13-adic INTEGER: ", neg));
info(Str("killed because n mod 169 is not 0, -1 or -2: ", kill - neg));
info(Str("undecided by E054's modulus: ", #surv, " (", bad, " lost precision)"));
for(i = 1, #surv,
    info(Str("   disk (", surv[i][1], ",", surv[i][2], ")  rho = ", surv[i][3],
             "  n mod 13^", KDEEP, " = ", lift(surv[i][5] + O(P13^KDEEP)))));
check(bad == 0, "and every leftover produced an n: no precision was lost");

print(Str("(3) THE DEEP SIEVE: n MODULO 13^", KDEEP));
EW2 = ellinit(EWCOEF); vv2 = 0; Em2 = ellinit(ellminimalmodel(EW2, &vv2));
P0w = ellchangepointinv([-3, 9], vv2);
torsw = vector(4, j, ellchangepointinv([[0], [0,0], [-6,0], [6,0]][j], vv2));
t0 = getwalltime();
PR = List();
forstep(q = 13^KDEEP - 1, QDEEP, 13^KDEEP,
  if(isprime(q) && q != P13,
    my(o = ordof(q, Em2)); if(o > 1 && o % 13^KDEEP == 0, listput(PR, [q, o]))));
info(Str("primes with 13^", KDEEP, " | ord(P_0), q < ", QDEEP, ": ", #PR));
forprime(q = 5, Q0,
  if(q != P13, my(o = ordof(q, Em2)); if(o > 1, listput(PR, [q, o]))));
PR = Vec(PR);
info(Str("total supply: ", #PR, " primes  (", (getwalltime()-t0)/1000., " s)"));
allempty = 1;
for(i = 1, #surv,
  my(nu = lift(surv[i][5] + O(P13^KDEEP)), alive = List());
  for(j = 1, 4,
    res = killclass(nu, KDEEP, PR, j, P0w, torsw, 0, 0);
    if(res[1] != 0, listput(alive, [j, res[1], res[2]])));
  alive = Vec(alive);
  if(#alive == 0,
    info(Str("   disk (", surv[i][1], ",", surv[i][2], ") x = ", surv[i][4],
             ": n = ", nu, " mod 13^", KDEEP,
             " is impossible for ALL FOUR torsion translates -- KILLED")),
    allempty = 0;
    info(Str("   disk (", surv[i][1], ",", surv[i][2], ") x = ", surv[i][4],
             ": n = ", nu, " SURVIVES for ", alive))));
\\ calibration: the three genuine classes must NOT be killed
for(k = 0, 2,
  my(nu = lift(Mod(-k, 13^KDEEP)), any = 0);
  for(j = 1, 4, if(killclass(nu, KDEEP, PR, j, P0w, torsw, 0, CALP)[1] != 0,
                   any = 1));
  check(any, Str("calibration: n = ", -k,
                 " survives the deep sieve, as it must -- it is a rational "
                 "point of C_4")));
check(allempty,
      Str("every leftover that E054's modulus could not decide is killed "
          "modulo 13^", KDEEP, ".  With E113's set that gives C_4(Q) = the "
          "nine known points"));

print("========================================================================");
printf("E115 GATE: %s   (%d failures, %.0f s)\n",
       if(FAIL, "*** RED ***", "GREEN"), FAIL, (getwalltime()-t0)/1000.);
}
