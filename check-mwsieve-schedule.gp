\\ check-mwsieve-schedule.gp --- E054, second attempt: WHICH primes to sieve with.
\\
\\ WHY THE FIRST SCHEDULE DIVERGED.  check-mwsieve-cost.gp chose, greedily, the
\\ cheapest set of primes reaching a large modulus M = lcm(ord_p): 349 primes,
\\ log2 M = 328.  The cost model then predicted the surviving set would stay at
\\ 2^1.9 classes, because it assumed each prime CUTS ONE BIT (mask density 1/2,
\\ measured) while M grows by log2(ord_p)/1 bits per prime.  The run refuted it:
\\
\\      after  50 primes: log2 M = 25.9, survivors (j=1,4) = 3720, 9600
\\      after 100 primes: log2 M = 47.4, survivors (j=1,4) = 38400, 370032
\\
\\ i.e. the set GROWS.  The independence assumption is false, and the reason is
\\ structural, not statistical: the information a prime carries is a subset of
\\ Z/ord_p, so ALL the primes sharing a modulus d can never cut more than log2 d
\\ bits in total.  A schedule that spends each prime on a FRESH prime power of M
\\ therefore buys log2(ord_p) bits of modulus while cutting at most one bit.
\\ The cut only saturates when MANY primes share the same modulus.
\\
\\ THE CORRECT SCHEDULE is the opposite of greedy: fix a modest modulus and pour
\\ every available prime into it.  With  USE(X) = { p : ord_p <= X }  and
\\ M(X) = lcm{ ord_p : p in USE(X) }, the budget condition is
\\        |USE(X)|  >>  log2 M(X)  ,
\\ and per prime power the finer condition
\\        #{ p in USE(X) : q^e | ord_p }  >=  e*log2(q) + margin .
\\ This script tabulates both, so the schedule is CHOSEN FROM DATA rather than
\\ from an assumption, and then runs the sieve on the chosen X.

default(parisize, "2G");

EWCOEF = [0, 216, 0, -31104, -2985984];
BSMOOTH = 100;
PMAX = 10^6;
XLIST = [100, 300, 1000, 3000, 10^4];
DOSIEVE = 1;      \\ set to 1 to run the sieve after the diagnostics
BUDGET = 600.0;   \\ seconds allowed for the sieve
TRIMS = 0;
MAXSET = 2000000;

frWQ(X, Y) = {
  my(al = -24, aa = -18, bb = -36, dd = 72, qq = 3, m, nn, tt, vv, den);
  m = X/al; nn = Y/al;
  den = 2*(aa - m^2);
  if(den == 0, return(0));
  tt = (nn - bb + dd*m/qq)/den;
  vv = qq + dd*tt/(2*qq) + m*tt^2;
  return([tt, 3*(tt-1)^2 + vv]);
};

frWp(X, Y) = {
  my(al = -24, aa = -18, bb = -36, dd = 72, qq = 3, m, nn, tt, vv, den);
  m = X/al; nn = Y/al;
  den = 2*(aa - m^2);
  if(lift(den) == 0, return(0));
  tt = (nn - bb + dd*m/qq)/den;
  vv = qq + dd*tt/(2*qq) + m*tt^2;
  return([tt, 3*(tt-1)^2 + vv]);
};

topt(P, p) = {
  if(#P < 2, return([0]));
  if(denominator(P[1]) % p == 0 || denominator(P[2]) % p == 0, return("bad"));
  return([Mod(P[1], p), Mod(P[2], p)]);
};

knownsols(Em, v, P0m, torsm, NB) = {
  my(L = List(), Q, P, Pw, tu, w);
  for(n = -NB, NB,
    Q = if(n == 0, [0], ellmul(Em, P0m, n));
    for(j = 1, 4,
      P = elladd(Em, Q, torsm[j]);
      if(#P < 2, next);
      Pw = ellchangepointinv(P, v);
      tu = frWQ(Pw[1], Pw[2]);
      if(tu == 0, next);
      if(issquare(tu[2], &w), listput(L, [n, j, tu[1], w]))));
  return(Vec(L));
};

supply(Em, PM, B, P0w) = {
  my(L = List(), N, Ep, P0p, ord);
  forprime(p = 5, PM,
    N = if(p % 4 == 3, p + 1, p + 1 - ellap(Em, p));
    if(vecmax(factor(N)[,1]) > B, next);
    Ep = ellinit(EWCOEF, p);
    if(#Ep == 0, next);
    P0p = topt(P0w, p);
    if(type(P0p) != "t_VEC" || #P0p < 2, next);
    ord = ellorder(Ep, P0p);
    if(ord < 2, next);
    listput(L, [p, ord]));
  return(Vec(L));
};

masks1(p, P0w, torsw) = {
  my(Ep, P0p, torsp, ord, mk, Q, R, tu, k);
  Ep = ellinit(EWCOEF, p);
  if(#Ep == 0, return(0));
  P0p = topt(P0w, p);
  if(type(P0p) != "t_VEC" || #P0p < 2, return(0));
  torsp = vector(4, j, topt(torsw[j], p));
  for(j = 1, 4, if(type(torsp[j]) != "t_VEC", return(0)));
  ord = ellorder(Ep, P0p);
  if(ord < 2, return(0));
  mk = vector(4, j, vectorsmall(ord));
  Q = [0];
  for(n = 0, ord - 1,
    for(j = 1, 4,
      R = if(j == 1, Q, elladd(Ep, Q, torsp[j]));
      if(#R < 2, mk[j][n+1] = 1; next);
      tu = frWp(R[1], R[2]);
      if(tu == 0, mk[j][n+1] = 1; next);
      k = kronecker(lift(tu[2]), p);
      if(k >= 0, mk[j][n+1] = 1));
    Q = elladd(Ep, Q, P0p));
  return([ord, mk]);
};

refine(cls, Mold, ord, mk) = {
  my(L = lcm(Mold, ord), reps, out = List(), c);
  reps = L / Mold;
  for(i = 1, #cls,
    for(k = 0, reps - 1,
      c = cls[i] + k * Mold;
      if(mk[(c % ord) + 1], listput(out, c))));
  return(Vec(out));
};

\\ the diagnostic: for a cap X, how much modulus do we get and how many primes
\\ do we have to spend on it -- globally and per prime power.
budget(S, X) = {
  my(U = List(), M = 1, cost = 0, fa, worst = 1000.0, cnt, need, q, e);
  for(i = 1, #S, if(S[i][2] <= X, listput(U, S[i]); M = lcm(M, S[i][2]); cost += S[i][2]));
  if(#U == 0, return(0));
  fa = factor(M);
  for(r = 1, matsize(fa)[1],
    q = fa[r,1]; e = fa[r,2]; cnt = 0;
    for(i = 1, #U, if(U[i][2] % q^e == 0, cnt++));
    need = e * log(q * 1.0) / log(2.0);
    if(cnt / need < worst, worst = cnt / need * 1.0));
  return([#U, cost, log(M * 1.0)/log(2.0), worst]);
};

\\ TRIMMING, the fix.  lcm{ord_p} drags in prime powers carried by one or two
\\ primes, and those can never be saturated: they add bits to M that nothing
\\ cuts.  Keep q^e only when at least  e*log2(q) + MARG  primes carry it, and
\\ then keep only the primes whose ord divides the trimmed modulus.
trim(S, X, marg) = {
  my(U = List(), qs = List(), M0 = 1, V = List(), M = 1, cost = 0, cnt, ee, q);
  for(i = 1, #S, if(S[i][2] <= X, listput(U, S[i])));
  U = Vec(U);
  if(#U == 0, return(0));
  for(i = 1, #U, my(fa = factor(U[i][2])); for(r = 1, matsize(fa)[1], listput(qs, fa[r,1])));
  qs = Set(Vec(qs));
  for(iq = 1, #qs,
    q = qs[iq]; ee = 0;
    for(e = 1, 40,
      cnt = 0;
      for(i = 1, #U, if(U[i][2] % q^e == 0, cnt++));
      if(cnt >= e * log(q*1.0)/log(2.0) + marg, ee = e, break));
    if(ee > 0, M0 *= q^ee));
  for(i = 1, #U, if(M0 % U[i][2] == 0, listput(V, U[i]); M = lcm(M, U[i][2]); cost += U[i][2]));
  return([Vec(V), M, cost]);
};

\\ THE SCHEDULER.  Processing the primes in ord-ascending order blows up: one
\\ prime whose ord introduces a fresh prime power multiplies the surviving set
\\ by reps = lcm(M,ord)/M before anything cuts it back, and the transient, not
\\ the final set, is what has to fit in memory (the ord-ascending run reached
\\ 8 GB and was killed).  So: at every step use up all the primes that cost
\\ NOTHING in modulus (ord | M -- pure cut, halves the set), and only when they
\\ run out spend the prime with the SMALLEST reps.  The set is then always cut
\\ down before it is lifted.  MAXSET is a hard stop, so a bad schedule reports
\\ instead of exhausting the machine.
sieve(U0, P0w, torsw, known, verbose, MAXSET) = {
  my(U, M = 1, cls, res, ord, mk, t0, kn = 0, alive = 0, lg, used = 0,
     avail, nleft, best, bi, reps, peak = 1, i, j);
  U = vecsort(U0, 2);
  nleft = #U;
  avail = vectorsmall(#U);          \\ 0 = unused, 1 = used
  cls = vector(4, j, [0]);
  t0 = getabstime();
  while(nleft > 0,
    \\ (a) all primes whose ord already divides M: pure cut, no lifting
    bi = 0;
    for(i = 1, #U,
      if(avail[i] || M % U[i][2] != 0, next);
      bi = i; break);
    if(bi == 0,
      \\ (b) none left: take the cheapest lift
      best = 0;
      for(i = 1, #U,
        if(avail[i], next);
        reps = lcm(M, U[i][2]) / M;
        if(best == 0 || reps < best, best = reps; bi = i)));
    if(bi == 0, break);
    avail[bi] = 1; nleft--;
    res = masks1(U[bi][1], P0w, torsw);
    if(res == 0, next);
    ord = res[1]; mk = res[2];
    for(j = 1, 4, cls[j] = refine(cls[j], M, ord, mk[j]));
    M = lcm(M, ord);
    used++;
    for(j = 1, 4, if(#cls[j] > peak, peak = #cls[j]));
    if(peak > MAXSET,
      printf("     *** set exceeded MAXSET = %d after %d primes; stopping ***\n", MAXSET, used);
      break);
    if(verbose && used % 100 == 0,
      printf("     %4d primes (ord %6d): log2 M = %6.1f, survivors %d %d %d %d, peak %d  (%s)\n",
             used, ord, log(M*1.0)/log(2.0), #cls[1], #cls[2], #cls[3], #cls[4], peak,
             strtime(getabstime() - t0))));
  lg = log(M * 1.0) / log(2.0);
  for(i = 1, #known,
    kn++;
    if(setsearch(Set(cls[known[i][2]]), known[i][1] % M), alive++));
  return([M, lg, cls, used, alive, kn, getabstime() - t0, peak]);
};

run() = {
  my(EW, Em, v = 0, P0m, torsm, P0w, torsw, known, S, res, r2, X, best = 0, bestX = 0);
  print("=== check-mwsieve-schedule.gp --- E054, choosing the sieve schedule ===");
  print("");
  EW = ellinit(EWCOEF);
  Em = ellinit(ellminimalmodel(EW, &v));
  P0m = [-3, 9];
  torsm = [[0], [0, 0], [-6, 0], [6, 0]];
  P0w = ellchangepointinv(P0m, v);
  torsw = vector(4, j, ellchangepointinv(torsm[j], v));
  \\ PRECONDITIONS.  The sieve quantifies over n P_0 + T, which is all of E(Q)
  \\ only if the rank is 1 and P_0 generates modulo torsion.  Check, do not
  \\ inherit.  (An index divisible only by primes > 10^4 would force
  \\ hat h <= 0.8886/10^8, which no point of this curve has.)
  print("=== 0. preconditions ===");
  res = ellrank(Em);
  printf("  ellrank = %s (lower = upper => rank 1, unconditional)\n", res[1..3]);
  printf("  ellsaturation(P_0, 10^4) = %s, hat h(P_0) = %.4f\n",
         ellsaturation(Em, [P0m], 10^4), ellheight(Em, P0m));
  printf("  torsion %s = (Z/2)^2\n", elltors(Em)[2]);
  known = knownsols(Em, v, P0m, torsm, 5);
  printf("  known solutions (n,j): ");
  for(i = 1, #known, printf("(%d,%d) ", known[i][1], known[i][2]));
  print("");
  print("");

  print("=== 1. supply ===");
  S = supply(Em, PMAX, BSMOOTH, P0w);
  printf("  %d primes p <= %d with #E(F_p) %d-smooth\n", #S, PMAX, BSMOOTH);
  print("");

  print("=== 2. schedule diagnostics: cap X on ord_p ===");
  print("  worst = min over prime powers q^e || M of (#primes carrying q^e)/(e log2 q);");
  print("  the sieve can only saturate a prime power if that ratio exceeds ~1.");
  print("");
  print("        X   #primes    cost (n-values)   log2 M    primes/bit   worst");
  foreach([10, 30, 100, 300, 1000, 3000, 10^4, 3*10^4, 10^5], XX,
    res = budget(S, XX);
    if(res == 0, next);
    printf("   %6d   %7d   %14d   %7.1f   %10.2f   %6.2f\n",
           XX, res[1], res[2], res[3], res[1]/res[3], res[4]));
  print("");

  print("=== 3. after trimming (margin 20 bits per prime power) ===");
  print("        X   #primes    cost (n-values)   log2 M   primes/bit   est. time");
  TRIMS = List();
  foreach(XLIST, XX,
    res = trim(S, XX, 20);
    if(res == 0 || #res[1] == 0, next);
    listput(TRIMS, [XX, res]);
    printf("   %6d   %7d   %14d   %7.1f   %10.2f   %8.1f s\n",
           XX, #res[1], res[3], log(res[2]*1.0)/log(2.0),
           #res[1] / (log(res[2]*1.0)/log(2.0)), 4.0 * res[3] * 7.4 / 10^6));
  TRIMS = Vec(TRIMS);
  print("");
  if(!DOSIEVE, print("=== stopping before the sieve (DOSIEVE = 0) ==="); return(0));

  print("=== 4. the sieve, on the largest trimmed cap within the time budget ===");
  bestX = 0; res = 0;
  for(i = 1, #TRIMS,
    if(4.0 * TRIMS[i][2][3] * 7.4 / 10^6 <= BUDGET, bestX = TRIMS[i][1]; res = TRIMS[i][2]));
  printf("  chosen cap X = %d\n", bestX);
  print("");
  r2 = sieve(res[1], P0w, torsw, known, 1, MAXSET);
  printf("  FINAL: %d primes, log2 M = %.1f, survivors %d %d %d %d, peak %d, time %s\n",
         r2[4], r2[2], #r2[3][1], #r2[3][2], #r2[3][3], #r2[3][4], r2[8], strtime(r2[7]));
  printf("  known solutions surviving: %d of %d\n", r2[5], r2[6]);
  printf("  M = %d\n", r2[1]);
  for(j = 1, 4,
    printf("  T_%d: ", j);
    if(#r2[3][j] == 0, print("empty -- no n at all for this translate"),
      for(i = 1, #r2[3][j],
        my(c = r2[3][j][i], cc = if(c > r2[1]/2, c - r2[1], c));
        printf("n = %d%s ", cc, if(abs(cc) <= 5, "(known)", "(EXTRA)")));
      print("")));
  print("");
  print("=== END ===");
};

run();
