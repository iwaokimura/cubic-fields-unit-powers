\\ check-mwsieve-cost.gp --- COST MODEL for the Mordell-Weil sieve on n
\\ (E040 Next Step (i)).  This script runs NO sieve.  It measures the three
\\ constants the estimate needs, and nothing else:
\\
\\   (1) the per-prime cost  c(p)  of building the condition
\\           S_p^{(j)} = { n mod ord_p : u(n P_0 + T_j) is a square mod p } ,
\\   (2) the density |S_p|/ord_p  (the sieve's strength per prime; expected 1/2),
\\   (3) how many primes are USABLE, i.e. have ord_p dividing a smooth modulus M,
\\       and what modulus M they generate.
\\
\\ WHY (3) IS THE WHOLE QUESTION.  A condition mod ord_p can only be intersected
\\ with knowledge mod M if ord_p | M: if d = gcd(ord_p, M) is a proper divisor,
\\ a class mod d survives unless ALL ord_p/d of its lifts are excluded, which
\\ happens with probability 2^{-ord_p/d} ~ 0.  So the sieve lives on the set of
\\ primes whose order is M-smooth, and the reachable modulus M -- not the CPU --
\\ is what bounds the result.
\\
\\ THE STRUCTURE THAT MAKES THIS CHEAP.  E : y^2 = x^3 - 36x has CM by Z[i]
\\ (j = 1728), so every p = 3 mod 4 is SUPERSINGULAR: a_p = 0 and #E(F_p) = p+1
\\ EXACTLY.  We may therefore CHOOSE the primes: any p = 3 mod 4 with p+1 smooth
\\ is usable, and p+1 is smooth for a computable supply of p.  Section 4 checks
\\ a_p = 0 rather than assuming it.
\\
\\ WHAT THE SIEVE WOULD BUY.  A solution n survives every S_p, so if the
\\ intersection contains only the classes of the known solutions, then any
\\ further solution has |n| >= M - 2.  Current state of knowledge is
\\ [E: |n| <= 400] (E040).  The sieve replaces 400 by M/2.  It does NOT prove
\\ finiteness -- nothing here bounds n from above; that is Chabauty's job.

default(parisize, "512M");

EWCOEF = [0, 216, 0, -31104, -2985984];

\\ H -> Weierstrass was derived in E040 (check-c4-rational.gp); f = -18t^4-36t^3
\\ +54t^2+72t+9 gives (aa,bb,cc,dd,qq) = (-18,-36,54,72,3) and al = -8q = -24.
\\ frW sends a Weierstrass point back to (t, u), u = 3(t-1)^2 + y.
\\ Two versions: over Q (exact ==0 test) and over F_p (lift(...) == 0 test).

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

\\ NB the failure marker is the STRING "bad", not 0: in GP the point at infinity
\\ [0] compares EQUAL to the integer 0, so a guard "if(P == 0, ...)" silently
\\ rejects every torsion translate -- which is exactly what it did on the first
\\ run of this script (all five sample primes reported "unusable").
topt(P, p) = {
  if(#P < 2, return([0]));
  if(denominator(P[1]) % p == 0 || denominator(P[2]) % p == 0, return("bad"));
  return([Mod(P[1], p), Mod(P[2], p)]);
};

\\ ---------------------------------------------------------------- section 1
\\ the solutions we already know, in the coordinates the sieve uses: (n, j)
\\ with j the index of the torsion translate.  A sieve MUST NOT kill these.

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

\\ ---------------------------------------------------------------- section 2
\\ one prime: build the four masks, time it, and check the known solutions
\\ survive.  Returns [ord, density(4), milliseconds, calibration failures].

sieve1(p, P0w, torsw, known) = {
  my(Ep, P0p, torsp, ord, masks, Q, R, tu, k, t0, ms, dens, bad = 0);
  Ep = ellinit(EWCOEF, p);
  if(#Ep == 0, return(0));
  P0p = topt(P0w, p);
  if(type(P0p) != "t_VEC" || #P0p < 2, return(0));
  torsp = vector(4, j, topt(torsw[j], p));
  for(j = 1, 4, if(type(torsp[j]) != "t_VEC", return(0)));
  ord = ellorder(Ep, P0p);
  if(ord == 0, return(0));
  masks = vector(4, j, vectorsmall(ord));
  t0 = getabstime();
  Q = [0];
  for(n = 0, ord - 1,
    for(j = 1, 4,
      R = if(j == 1, Q, elladd(Ep, Q, torsp[j]));
      if(#R < 2, masks[j][n+1] = 1; next);
      tu = frWp(R[1], R[2]);
      if(tu == 0, masks[j][n+1] = 1; next);
      k = kronecker(lift(tu[2]), p);
      if(k >= 0, masks[j][n+1] = 1));
    Q = elladd(Ep, Q, P0p));
  ms = getabstime() - t0;
  dens = vector(4, j, vecsum(Vec(masks[j])) / (1.0 * ord));
  for(i = 1, #known,
    my(n0 = known[i][1], j0 = known[i][2]);
    if(masks[j0][(n0 % ord) + 1] != 1, bad++));
  return([ord, dens, ms, bad]);
};

\\ ---------------------------------------------------------------- section 4
\\ CM: is a_p = 0 for every p = 3 mod 4?  (Checked, not assumed.)

cmcheck(Em, PMAX) = {
  my(bad = 0, cnt = 0);
  forprime(p = 5, PMAX,
    if(p % 4 != 3, next);
    cnt++;
    if(ellap(Em, p) != 0, bad++));
  return([cnt, bad]);
};

\\ ---------------------------------------------------------------- section 5
\\ the supply of usable primes: p with #E(F_p) B-smooth.  Returns the list of
\\ [p, N_p] sorted by p, so the driver can accumulate cost and modulus.

\\ The modulus a prime contributes is the order of P_0, NOT #E(F_p): the sieve
\\ condition on n has period ord_p | N_p, and that same ord_p is the length of
\\ the loop, i.e. the cost.  N_p is used only as a fast smoothness pre-filter.
supply(Em, PMAX, B, P0w) = {
  my(L = List(), N, Ep, P0p, ord);
  forprime(p = 5, PMAX,
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

\\ cumulative table: after adding the i-th usable prime, what is the cost
\\ (sum of ord_p ~ sum of N_p), the modulus M = lcm(N_p), and the excess
\\ k - log2(M)?  The sieve is conclusive when the excess is positive.

cumtable(S) = {
  my(M = 1, tot = 0, out = List(), lg);
  for(i = 1, #S,
    M = lcm(M, S[i][2]);
    tot += S[i][1];
    lg = log(M * 1.0) / log(2.0);
    listput(out, [i, S[i][1], tot, lg, i - lg]));
  return(Vec(out));
};

\\ ---------------------------------------------------------------- section 6
\\ Which SUBSET of the usable primes should one actually run?  Processing all of
\\ them is gross overkill: the modulus M = lcm(ord_p) saturates while the number
\\ of conditions keeps growing, and only  k >= log2 M + margin  is needed.
\\ Greedy: for each prime power q^e || M take the CHEAPEST prime whose ord_p is
\\ divisible by q^e (this reproduces M exactly), then top up with the cheapest
\\ unused primes until the excess reaches the margin.

greedy(S, margin) = {
  my(M = 1, fa, U = List(), used, cost = 0, lg, i, q, e, bestc, besti);
  for(i = 1, #S, M = lcm(M, S[i][2]));
  fa = factor(M);
  used = vectorsmall(#S);
  for(r = 1, matsize(fa)[1],
    q = fa[r,1]; e = fa[r,2]; bestc = 0; besti = 0;
    for(i = 1, #S,
      if(S[i][2] % q^e == 0 && (besti == 0 || S[i][2] < bestc),
         bestc = S[i][2]; besti = i));
    if(besti && !used[besti], used[besti] = 1; listput(U, S[besti]); cost += S[besti][2]));
  lg = log(M * 1.0) / log(2.0);
  for(i = 1, #S,
    if(#U >= lg + margin, break);
    if(!used[i], used[i] = 1; listput(U, S[i]); cost += S[i][2]));
  return([#U, cost, lg, #U - lg, peak(Vec(U))]);
};

\\ The one cost this script does NOT measure directly is the CRT bookkeeping:
\\ carrying the surviving set S mod M_i and lifting it when the modulus grows.
\\ Its size is |S_i| ~ M_i * 2^{-i}, so the peak over the run is 2^{max(log2 M_i
\\ - i)} -- a SCHEDULING quantity, not an arithmetic one.  Processing the chosen
\\ primes in ascending order of ord_p keeps it small; this returns the exponent
\\ so the claim is measured rather than asserted.

peak(U) = {
  my(V, M = 1, mx = 0, lg);
  V = vecsort(U, 2);
  for(i = 1, #V,
    M = lcm(M, V[i][2]);
    lg = log(M * 1.0) / log(2.0) - i;
    if(lg > mx, mx = lg));
  return(mx);
};

\\ ---------------------------------------------------------------- driver

run() = {
  my(EW, Em, v = 0, P0m, torsm, P0w, torsw, known, res, plist, S, T, best, bi);
  print("=== check-mwsieve-cost.gp --- cost model for the MW sieve on n ===");
  print("");
  EW = ellinit(EWCOEF);
  Em = ellinit(ellminimalmodel(EW, &v));
  P0m = [-3, 9];
  torsm = [[0], [0, 0], [-6, 0], [6, 0]];
  P0w = ellchangepointinv(P0m, v);
  torsw = vector(4, j, ellchangepointinv(torsm[j], v));
  printf("  E (minimal) %s,  j = %s,  conductor %d\n", Em[1..5], Em.j, ellglobalred(Em)[1]);
  printf("  P_0 = %s on the minimal model, = %s on the H-model\n", P0m, P0w);
  \\ PRECONDITION.  The sieve quantifies over n P_0 + T, which is all of E(Q)
  \\ only if P_0 generates modulo torsion.  Check, do not assume.
  res = ellrank(Em);
  printf("  ellrank = %s (lower = upper, so rank 1 unconditionally)\n", res[1..3]);
  printf("  ellsaturation(P_0, 100) = %s  <-- P_0 is saturated at all p <= 100\n",
         ellsaturation(Em, [P0m], 100));
  print("");

  print("=== 1. the known solutions, as (n, j) ===");
  known = knownsols(Em, v, P0m, torsm, 5);
  printf("      n   j        t             w\n");
  for(i = 1, #known,
    printf("   %4d %3d   %-12s  %s\n", known[i][1], known[i][2], known[i][3], known[i][4]));
  printf("  %d solutions with |n| <= 5 (E040 found the same set out to |n| = 400)\n", #known);
  print("");

  print("=== 2. per-prime cost and density (the sieve must not kill a solution) ===");
  print("        p      ord_p   density (j=1..4)                 ms    us/class  calib");
  plist = [1019, 4999, 10007, 49999, 100003];
  for(i = 1, #plist,
    res = sieve1(plist[i], P0w, torsw, known);
    if(res == 0, printf("   %8d   unusable\n", plist[i]); next);
    printf("   %8d %8d   %.4f %.4f %.4f %.4f  %7d   %8.3f   %s\n",
           plist[i], res[1], res[2][1], res[2][2], res[2][3], res[2][4],
           res[3], 1000.0 * res[3] / (4.0 * res[1]),
           if(res[4] == 0, "ok", Str("*** ", res[4], " FAILURES ***"))));
  print("");

  print("=== 3. CM structure: a_p = 0 for p = 3 mod 4, so #E(F_p) = p+1 exactly ===");
  res = cmcheck(Em, 20000);
  printf("  %d primes p = 3 mod 4 below 20000, a_p != 0 for %d of them\n", res[1], res[2]);
  print("");

  print("=== 4. supply of usable primes (N_p is B-smooth) ===");
  print("     B    PMAX      #usable   sum of ord_p   log2 lcm(ord_p)");
  foreach([20, 50, 100], B,
    foreach([10^4, 10^5, 10^6], PMAX,
      S = supply(Em, PMAX, B, P0w);
      if(#S == 0, next);
      T = cumtable(S);
      printf("   %4d  %7d   %8d   %12d   %12.2f\n",
             B, PMAX, #S, T[#T][3], T[#T][4])));
  print("");

  print("=== 5. cumulative sieve: cost vs proven range ===");
  print("  k = primes used, cost = sum ord_p (~ elliptic additions / 4),");
  print("  log2 M = log2 lcm(ord_p) = log2 of the proven range, excess = k - log2 M");
  print("  (expected false positives = 4 * 2^{-excess}; conclusive when excess > ~5)");
  print("");
  S = supply(Em, 10^5, 50, P0w);
  T = cumtable(S);
  print("      k      ord_k       cost      log2 M     excess");
  for(i = 1, #T,
    if(i % 25 == 0 || i == #T,
      printf("   %4d   %8d   %9d   %9.2f   %8.2f\n", T[i][1], T[i][2], T[i][3], T[i][4], T[i][5])));
  print("");
  best = 0; bi = 0;
  for(i = 1, #T, if(T[i][5] >= 10 && T[i][4] > best, best = T[i][4]; bi = i));
  if(bi,
    printf("  cheapest operating point with excess >= 10 and M maximal:\n");
    printf("    k = %d primes, cost = %d classes, log2 M = %.2f, excess = %.2f\n",
           bi, T[bi][3], T[bi][4], T[bi][5]);
    printf("    proven range |n| < M/2 = 10^%.1f\n", T[bi][4] * log(2.0) / log(10.0) - 0.3));
  print("");

  print("=== 6. the run one would actually do: greedy subset, margin 20 ===");
  print("  US = measured microseconds per class (section 2); wall time = 4*cost*US");
  print("");
  print("      B    PMAX   primes    cost (n-values)   log2 M   excess   est. time   log2 peak|S|");
  foreach([20, 50, 100], B,
    foreach([10^5, 10^6], PMAX,
      S = supply(Em, PMAX, B, P0w);
      if(#S == 0, next);
      res = greedy(S, 20);
      printf("   %4d %7d   %6d   %14d   %6.1f   %6.1f   %8.1f s   %8.1f\n",
             B, PMAX, res[1], res[2], res[3], res[4], 4.0 * res[2] * 7.3 / 10^6, res[5])));
  print("");
  print("  proven range is |n| < M/2; log2 M = 100 means |n| < 6*10^29.");
  print("");
  print("=== END (no sieve was run; this script only measures constants) ===");
};

run();
