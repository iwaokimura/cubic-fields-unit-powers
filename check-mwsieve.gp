\\ check-mwsieve.gp --- E054: the Mordell-Weil sieve on n (E040 Next Step (i)).
\\
\\ *** SUPERSEDED -- THIS IS THE FAILED ROUTE, KEPT AS THE RECORD (E054(c)). ***
\\ The schedule below (greedy: the cheapest set of primes reaching a large
\\ modulus) DIVERGES -- the surviving set grows, and the run dies at 8 GB.  Its
\\ prediction came from assuming the local conditions are independent, which
\\ they are not.  The script that produces the result is
\\ check-mwsieve-schedule.gp; run that one.  Do not delete this file: E054's
\\ Results (c) quotes its numbers.
\\
\\ THE QUESTION (E040).  C_4 -> E : y^2 = x^3 - 36x is the degree-2 quotient by
\\ Aut(C_4) = Z/2 (E037).  Writing u = w^2 and completing the square turns C_4
\\ into "u is a square" on the genus-1 curve H : y^2 = f(t), and since
\\ E(Q) = Z<P_0> + (Z/2)^2 with P_0 = (-3,9), the rational points of C_4 are
\\        { (n, T) :  u(n P_0 + T)  is a square in Q } .
\\ E040 found four, all with |n| <= 2, and checked |n| <= 400 by brute force.
\\
\\ THE SIEVE.  For a prime p of good reduction, reduction mod p is a group
\\ homomorphism, so n P_0 + T mod p depends only on n mod ord_p, ord_p = the
\\ order of P_0 in E(F_p).  If u is a square in Q then its reduction is a square
\\ in F_p whenever it is a unit there.  Hence, for each torsion translate T_j,
\\        n  admissible  ==>  n mod ord_p  in  S_p^{(j)}
\\             := { m : kronecker(u(m P_0 + T_j), p) >= 0, or u is degenerate } .
\\ Intersecting over many p by CRT confines n to a set of classes mod
\\ M = lcm(ord_p).  A sieve can only produce FALSE POSITIVES -- a genuine
\\ solution survives every S_p -- so the exclusion it outputs is exact.
\\
\\ WHY IT IS CHEAP HERE (cost model: check-mwsieve-cost.gp).  E has CM by Z[i]
\\ (j = 1728), so every p = 3 mod 4 is supersingular: #E(F_p) = p+1 EXACTLY.
\\ The primes may therefore be CHOSEN so that ord_p is smooth, and a greedy
\\ subset of 349 primes reaches log2 M = 328 for ~1.5*10^6 group operations.
\\ Measured constants: 7.4 us per class, density 0.50 per prime, peak surviving
\\ set 2^1.9 (so the CRT bookkeeping is free).
\\
\\ WHAT IT CANNOT DO.  Nothing here bounds n from above, so this does NOT prove
\\ the list of rational points complete; that is Chabauty's job (blocked, E048).
\\ What it does is replace the range |n| <= 400 by |n| < M.
\\
\\ GP GOTCHA (new, cost the first run of the cost model): [0] == 0 is TRUE, so a
\\ guard "if(P == 0, ...)" also rejects the point at infinity.  Use a string
\\ marker and type().

default(parisize, "1G");

EWCOEF = [0, 216, 0, -31104, -2985984];
BSMOOTH = 100;
PMAX = 10^6;
MARGIN = 20;

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

\\ greedy: cover every prime power of M = lcm(ord_p) with the cheapest prime
\\ that carries it, then top up with the cheapest unused primes until there are
\\ log2(M) + MARGIN conditions.  Returns the chosen primes sorted by ord.
choose(S, margin) = {
  my(M = 1, fa, U = List(), used, lg, q, e, bestc, besti);
  for(i = 1, #S, M = lcm(M, S[i][2]));
  fa = factor(M);
  used = vectorsmall(#S);
  for(r = 1, matsize(fa)[1],
    q = fa[r,1]; e = fa[r,2]; bestc = 0; besti = 0;
    for(i = 1, #S,
      if(S[i][2] % q^e == 0 && (besti == 0 || S[i][2] < bestc),
         bestc = S[i][2]; besti = i));
    if(besti && !used[besti], used[besti] = 1; listput(U, S[besti])));
  lg = log(M * 1.0) / log(2.0);
  for(i = 1, #S,
    if(#U >= lg + margin, break);
    if(!used[i], used[i] = 1; listput(U, S[i])));
  return(vecsort(Vec(U), 2));
};

\\ the four masks of one prime: mask[j][m+1] = 1 iff n = m mod ord_p is allowed
\\ for the torsion translate T_j.  Degenerate reductions are KEPT (safe side).
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

\\ lift the surviving classes from modulus Mold to L = lcm(Mold, ord) and keep
\\ those allowed by the mask.
refine(cls, Mold, ord, mk) = {
  my(L = lcm(Mold, ord), reps, out = List(), c);
  reps = L / Mold;
  for(i = 1, #cls,
    for(k = 0, reps - 1,
      c = cls[i] + k * Mold;
      if(mk[(c % ord) + 1], listput(out, c))));
  return(Vec(out));
};

run() = {
  my(EW, Em, v = 0, P0m, torsm, P0w, torsw, known, S, U, M, cls, res, ord, mk,
     t0, tot = 0, kn, alive, extra = 0, lg, i, j);
  print("=== check-mwsieve.gp --- E054: the Mordell-Weil sieve on n ===");
  printf("    parameters: B = %d, p <= %d, margin = %d bits\n", BSMOOTH, PMAX, MARGIN);
  print("");
  EW = ellinit(EWCOEF);
  Em = ellinit(ellminimalmodel(EW, &v));
  P0m = [-3, 9];
  torsm = [[0], [0, 0], [-6, 0], [6, 0]];
  P0w = ellchangepointinv(P0m, v);
  torsw = vector(4, j, ellchangepointinv(torsm[j], v));

  print("=== 0. preconditions ===");
  res = ellrank(Em);
  printf("  rank E(Q): ellrank = %s (lower = upper => rank 1, unconditional)\n", res[1..3]);
  printf("  P_0 saturated: ellsaturation(P_0, 100) = %s\n", ellsaturation(Em, [P0m], 100));
  printf("  torsion %s = (Z/2)^2 (E040's correction to E037)\n", elltors(Em)[2]);
  known = knownsols(Em, v, P0m, torsm, 5);
  printf("  known solutions (n, j): ");
  for(i = 1, #known, printf("(%d,%d) ", known[i][1], known[i][2]));
  print("");
  print("");

  print("=== 1. supply of usable primes ===");
  t0 = getabstime();
  S = supply(Em, PMAX, BSMOOTH, P0w);
  M = 1; for(i = 1, #S, M = lcm(M, S[i][2]));
  printf("  %d primes p <= %d with #E(F_p) %d-smooth   (%s)\n",
         #S, PMAX, BSMOOTH, strtime(getabstime() - t0));
  printf("  lcm of their ord_p has %d bits\n", #binary(M));
  U = choose(S, MARGIN);
  for(i = 1, #U, tot += U[i][2]);
  printf("  greedy subset: %d primes, sum ord_p = %d, largest ord_p = %d\n",
         #U, tot, U[#U][2]);
  print("");

  print("=== 2. the sieve ===");
  t0 = getabstime();
  M = 1;
  cls = vector(4, j, [0]);
  for(i = 1, #U,
    res = masks1(U[i][1], P0w, torsw);
    if(res == 0, next);
    ord = res[1]; mk = res[2];
    for(j = 1, 4, cls[j] = refine(cls[j], M, ord, mk[j]));
    M = lcm(M, ord);
    if(i % 50 == 0,
      printf("   after %3d primes: log2 M = %6.1f, survivors %d %d %d %d   (%s)\n",
             i, log(M*1.0)/log(2.0), #cls[1], #cls[2], #cls[3], #cls[4],
             strtime(getabstime() - t0))));
  lg = log(M * 1.0) / log(2.0);
  printf("   FINAL          : log2 M = %6.1f, survivors %d %d %d %d   (%s)\n",
         lg, #cls[1], #cls[2], #cls[3], #cls[4], strtime(getabstime() - t0));
  print("");

  print("=== 3. result ===");
  printf("  M = %d\n", M);
  printf("  log10 M = %.1f\n", lg * log(2.0)/log(10.0));
  for(j = 1, 4,
    printf("  T_%d: %d surviving class(es) mod M", j, #cls[j]);
    if(#cls[j] == 0, print("   <-- NO n at all: this translate is empty, no range needed"),
      printf(":\n"));
    for(i = 1, #cls[j],
      my(c = cls[j][i], cc = if(c > M/2, c - M, c));
      printf("        n = %d mod M%s\n", cc,
             if(abs(cc) <= 5, Str("   <-- known solution n = ", cc), "   *** UNEXPECTED ***"));
      if(abs(cc) > 5, extra++)));
  print("");

  print("=== 4. calibration: every known solution must survive ===");
  kn = 0; alive = 0;
  for(i = 1, #known,
    kn++;
    my(n0 = known[i][1], j0 = known[i][2], r = n0 % M);
    if(setsearch(Set(cls[j0]), r), alive++,
       printf("  *** LOST (n,j) = (%d,%d) -- THE SIEVE IS WRONG ***\n", n0, j0)));
  printf("  %d of %d known solutions survive\n", alive, kn);
  print("");

  print("=== VERDICT ===");
  if(alive != kn,
    print("  *** CALIBRATION FAILED: nothing above is trustworthy. ***"),
    if(extra == 0,
      printf("  [T(CAS)] The only n with u(n P_0 + T) a square and |n| < %.1e are the\n", M * 1.0);
      print("           four known ones (|n| <= 2).  E040's [E: |n| <= 400] is superseded.");
      print("           Two of the four torsion translates admit NO n whatsoever.");
      print("  [OPEN]   Finiteness.  A sieve gives no upper bound on n; that is what");
      print("           quadratic Chabauty would have to supply (E048: blocked)."),
      print("  Extra classes survived; add more primes from the supply to kill them.")));
};

run();
