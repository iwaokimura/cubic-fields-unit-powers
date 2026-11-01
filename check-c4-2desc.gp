\\ check-c4-2desc.gp --- E042: rank E(K) = 2 for E : y^2 = x^3 - 36x over
\\ K = Q(2^(1/3)), UNCONDITIONALLY.  This closes E041 Next Step (i) and makes
\\ elliptic curve Chabauty at q = 4 available with no appeal to BSD.
\\
\\ WHAT E041 CONCLUDED, AND WHY IT WAS WRONG.  E041(c) recorded
\\        [T(CAS)]  rank E(K) <= 4                    (Simon's 2-descent)
\\ and E041(f) recorded that Sage's rank_bounds() returning (2,2) was a caching
\\ artefact to be ignored.  BOTH READINGS ARE MISTAKEN, and they are the same
\\ mistake twice: the second component returned by a 2-descent is the dimension
\\ of the 2-SELMER GROUP, not a bound on the rank.  The two are related by
\\        0 --> E(K)/2E(K) --> Sel^2(E/K) --> Sha(E/K)[2] --> 0,
\\        dim_F2 E(K)/2E(K) = rank E(K) + dim_F2 E(K)[2],
\\ so the rank bound is  dim Sel^2 MINUS the F_2-rank of the 2-torsion:
\\        rank E(K) <= s - t,     s = dim_F2 Sel^2(E/K),  t = dim_F2 E(K)[2].
\\ Here t = 2 (the 2-torsion of y^2 = x(x-6)(x+6) is rational already over Q),
\\ so s = 4 gives rank <= 2, not 4.  Sage's simon_two_descent() returns the pair
\\ (rank lower bound, s) -- its own documentation says so -- while rank_bounds()
\\ returns (rank lower bound, s - t).  E041 compared the outputs of two functions
\\ with DIFFERENT conventions and diagnosed the discrepancy as a caching bug in
\\ the library.  There is no bug; (2,2) was the correct answer all along.
\\
\\ Since E041(b) proved rank E(K) >= 2 exactly (trace argument, redone in
\\ section 6 below), the rank is exactly 2 and Chabauty's requirement
\\ rank E(K) < [K:Q] = 3 holds unconditionally.
\\
\\ WHAT THIS SCRIPT THEREFORE HAS TO DO.  The mathematical content is one line;
\\ the work is in making sure the line is being read off a computation that
\\ means what we think it means.  So the convention is CALIBRATED, in three
\\ ways, before it is used:
\\   (1) over Q, against PARI's own ellrank -- a different implementation;
\\   (2) over quadratic F = Q(sqrt d), where rank E(F) = rank E(Q) + rank E^(d)(Q)
\\       is known from two ellrank computations over Q and nothing else;
\\   (3) on curves with NONTRIVIAL Sha[2].  This one matters: in every case of
\\       (1) and (2) Sha[2] happens to vanish, so s - t equals the rank there
\\       for a reason that would also hold under the wrong convention.  The
\\       congruent-number curves n = 17, 68, 73 have rank 0 and Sha[2] = (Z/2)^2,
\\       and they separate the two readings: s - t = 2 > 0 = rank, while the
\\       wrong reading would report rank <= 2 as if it were sharp for a curve
\\       ellrank proves has rank 0.  s counts Sha[2]; that is what fixes H1.
\\
\\ ON GRH.  Simon's algorithm needs S-units of K.  For a curve with FULL rational
\\ 2-torsion, bnfellrank dispatches to bnfell2descent_complete, which uses
\\ bnfsunit on K and on no other field (the other branches, which do call bnfinit
\\ on an auxiliary extension, are not taken here).  So the only conditional input
\\ is the class group and unit group of K itself -- and bnfcertify(K) = 1, so the
\\ result is GRH-free.  Section 5 re-derives the same bound through the OTHER
\\ branch of the script (descent via a 2-isogeny, on the isogenous curve), which
\\ is a different algorithm reaching the same number.
\\
\\ The descent itself is Denis Simon's ell.gp (version 06/04/2011), as
\\ distributed with SageMath.  Point the environment variable SIMON_ELL at
\\ your copy, e.g.
\\   SIMON_ELL=$(sage -c "from sage.env import SAGE_EXTCODE; \
\\       print(SAGE_EXTCODE)")/pari/simon/ell.gp
\\
\\ Run as:  SIMON_ELL=... gp -q check-c4-2desc.gp < /dev/null      (~15 s)

SIMON = getenv("SIMON_ELL");
{
if(SIMON == 0 || SIMON == "",
  print("FATAL: set SIMON_ELL to the path of SageMath's simon/ell.gp");
  quit(1));
}
read(SIMON);
\\ parisize MUST be set here and not inside a function: reallocating the stack
\\ ABORTS the computation in progress, and at top level that costs only the one
\\ statement, whereas inside run() it silently kills the whole run -- the stack
\\ warning prints and then nothing else happens, with no error and exit code 0.
default(parisize, 4*10^9);

\\ ell.gp reads these five as globals; default_ell() sets them but also prints,
\\ so set them here and call default_ell only where the point is to vary them.
setparams(deb, l1, l3, ltriv, mprob, lbig) =
{
  DEBUGLEVEL_ell = deb; LIM1 = l1; LIM3 = l3; LIMTRIV = ltriv;
  MAXPROB = mprob; LIMBIGPRIME = lbig;
  return(0);
};

\\ dim_F2 E(F)[2] for E : y^2 = x^3 + a4 x + a6, from the roots of the cubic.
tworank(bnf, E) =
{
  my(n = #nfroots(bnf, x^3 + E[4]*x + E[5]));
  return(if(n == 0, 0, if(n == 1, 1, 2)));
};

banner(s) =
{
  print("");
  print("======================================================================");
  print(" ", s);
  print("======================================================================");
  return(0);
};

\\ ---------------------------------------------------------------- section 0
inputs(bnfK) =
{
  my(nfail = 0, r = nfroots(bnfK, x^3 - 36*x), cert = bnfcertify(bnfK));
  banner("0.  THE FIELD, THE CURVE, AND THE TWO EXACT INPUTS");
  printf("  K = Q(2^(1/3)):  disc = %s,  h = %d,  fundamental unit = %s\n",
         bnfK.disc, bnfK.no, lift(bnfK.fu[1]));
  printf("  bnfcertify(K)  = %d   <== the class group and units are unconditional\n", cert);
  printf("  x^3 - 36x has %d roots in K: %s\n", #r, r~);
  printf("  so t = dim_F2 E(K)[2] = %d\n", tworank(bnfK, [0,0,0,-36,0]));
  printf("  E(K)_tors = %s   (elltors component [2] is the structure)\n",
         elltors(ellinit([0,0,0,-36,0], bnfK))[2]);
  if(cert != 1 || tworank(bnfK, [0,0,0,-36,0]) != 2,
     print("  *** FAIL: the two exact inputs are not what the argument assumes");
     nfail++);
  return(nfail);
};

\\ ---------------------------------------------------------------- section 1
calibQ(bnfQ) =
{
  my(nfail = 0, cur, E, rk, t, s, v);
  banner("1.  CALIBRATION A --- over Q, against PARI's own ellrank");
  print("  H1: s = dim Sel^2, rank <= s - t.     H2: s = dim Sel^2 - t, rank <= s.");
  cur = [[0,0,0,-1,0], [0,0,0,-36,0], [0,0,0,-25,0], [0,0,0,-49,0],
         [0,0,0,-16,0], [0,0,0,144,0], [0,0,0,-4,0], [0,0,0,-9,0],
         [0,0,0,-100,0], [0,0,0,-225,0]];
  for(i = 1, #cur,
    E = cur[i];
    rk = ellrank(ellinit(E));
    t = tworank(bnfQ, E);
    s = bnfellrank(bnfQ, E)[2];
    v = if(rk[1] != rk[2], "rank not pinned by ellrank",
          if(s - t == rk[1], "H1 ok", if(s == rk[1], "H2 ok", "NEITHER")));
    printf("  %-18s rank = %d   t = %d   s = %d   s-t = %d    %s\n", E, rk[1], t, s, s-t, v);
    if(v != "H1 ok", nfail++));
  return(nfail);
};

\\ ---------------------------------------------------------------- section 2
calibquad() =
{
  my(nfail = 0, cur, E, d, r0, r1, F, t, s, rkF, v);
  banner("2.  CALIBRATION B --- over quadratic fields, rank known from Q alone");
  print("  rank E(Q(sqrt d)) = rank E(Q) + rank E^(d)(Q), both by ellrank over Q.");
  cur = [[[0,0,0,-36,0],-1], [[0,0,0,-36,0],2], [[0,0,0,-36,0],-3],
         [[0,0,0,-36,0],5], [[0,0,0,-1,0],-1], [[0,0,0,-1,0],5],
         [[0,0,0,-25,0],-1], [[0,0,0,144,0],-1], [[0,0,0,144,0],2],
         [[0,0,0,-16,0],17], [[0,0,0,-49,0],-1], [[0,0,0,-4,0],3]];
  for(i = 1, #cur,
    E = cur[i][1]; d = cur[i][2];
    r0 = ellrank(ellinit(E));
    r1 = ellrank(ellinit([0, 0, 0, E[4]*d^2, E[5]*d^3]));
    F = bnfinit(y^2 - d, 1);
    t = tworank(F, E);
    s = bnfellrank(F, E)[2];
    rkF = r0[1] + r1[1];
    v = if(r0[1] != r0[2] || r1[1] != r1[2], "rank not pinned by ellrank",
          if(s - t == rkF, "H1 ok", if(s == rkF, "H2 ok", "NEITHER")));
    printf("  %-16s d = %-3d rank E(F) = %d   t = %d   s = %d   s-t = %d    %s\n",
           E, d, rkF, t, s, s-t, v);
    if(v != "H1 ok", nfail++));
  return(nfail);
};

\\ ---------------------------------------------------------------- section 3
calibsha(bnfQ) =
{
  my(nfail = 0, nsha = 0, E, rk, s, ub);
  banner("3.  CALIBRATION C --- the cases that actually separate H1 from H2");
  print("  y^2 = x^3 - n^2 x, n <= 80.  s - t must never drop below the rank, and");
  print("  where Sha[2] != 0 it must exceed it -- that is what distinguishes the");
  print("  two conventions.  ellrank's upper bound is the independent witness.");
  for(n = 1, 80,
    E = [0,0,0,-n^2,0];
    rk = ellrank(ellinit(E));
    s = bnfellrank(bnfQ, E)[2];
    ub = s - 2;
    if(ub < rk[1],
       printf("  *** FAIL n = %d: s-t = %d is below the proved rank %d\n", n, ub, rk[1]);
       nfail++);
    if(rk[1] == rk[2] && ub > rk[1],
       printf("  n = %-3d rank = %d (pinned by ellrank), s-t = %d  ==>  dim Sha[2] = %d\n",
              n, rk[1], ub, ub - rk[1]);
       nsha++));
  printf("  n = 1..80: %d contradictions with ellrank, %d curves exhibiting Sha[2] != 0.\n",
         nfail, nsha);
  print("  So s counts Sha[2] as well as the rank: the convention is H1.");
  if(nsha == 0, print("  *** FAIL: calibration C found no Sha case, so it is not conclusive");
     nfail++);
  return(nfail);
};

\\ ---------------------------------------------------------------- section 4
maincomp(bnfK) =
{
  my(nfail = 0, EK = [0,0,0,-36,0], params, p, res, sref = 0);
  banner("4.  THE COMPUTATION --- rank E(K) <= 2, and its stability");
  print("  s does not depend on how hard one looks for points, so it must not");
  print("  move with the search parameters.  LIMBIGPRIME = 0 turns off the");
  print("  probabilistic tests entirely.");
  params = [[2,4,2,20,0], [5,10,10,20,0], [8,16,16,20,0], [12,24,24,50,0], [2,4,2,20,30]];
  for(i = 1, #params,
    p = params[i];
    setparams(0, p[1], p[2], p[3], p[4], p[5]);
    res = bnfellrank(bnfK, EK);
    printf("  LIM1=%2d LIM3=%2d LIMTRIV=%2d MAXPROB=%2d LIMBIGPRIME=%2d  ->  r >= %d,  s = %d,  rank <= %d\n",
           p[1], p[2], p[3], p[4], p[5], res[1], res[2], res[2] - 2);
    if(i == 1, sref = res[2], if(res[2] != sref, print("  *** FAIL: s is not stable"); nfail++));
    if(res[2] - 2 != 2, print("  *** FAIL: the rank bound is not 2"); nfail++));
  setparams(0, 5, 10, 10, 20, 0);
  return(nfail);
};

\\ ---------------------------------------------------------------- section 5
crosscheck(bnfK) =
{
  my(nfail = 0, Ep = [0,0,0,144,0], t = tworank(bnfK, [0,0,0,144,0]), res);
  banner("5.  CROSS-CHECK --- the same bound through a different algorithm");
  print("  E' : y^2 = x^3 + 144x is 2-isogenous to E over Q, so rank E'(K) = rank E(K).");
  print("  Over K it has only ONE rational 2-torsion point, so the descent takes the");
  print("  other branch of the script: via the 2-isogeny, not the complete 2-descent.");
  res = bnfell2descent_viaisog(bnfK, Ep*Mod(1, bnfK.pol));
  printf("  E'(K)[2]: t = %d,  r >= %d,  s = %d,  rank E'(K) <= %d\n",
         t, res[1], res[2], res[2] - t);
  if(t != 1, print("  *** FAIL: E' was expected to have 2-torsion Z/2 over K"); nfail++);
  if(res[2] - t != 2, print("  *** FAIL: the isogeny descent does not confirm the bound"); nfail++);
  return(nfail);
};

\\ ---------------------------------------------------------------- section 6
lowerbound() =
{
  my(nfail = 0, L, E, rts, u, P2, Tr, R, o1, o2);
  banner("6.  THE LOWER BOUND --- E041(b) redone here, exactly, in gp");
  print("  Gal(L/Q) = S_3 and E(L) tensor Q = 1^a + eps^b + rho^c give");
  print("  rank E(Q) = a and rank E(K) = a + c.  The trace over the three");
  print("  embeddings K -> L is multiplication by 3 on the trivial part and 0 on");
  print("  the rho part, so R := 3P - Tr(P) is non-torsion iff P has a nonzero");
  print("  rho-component.  ellorder is exact, so no regulator is computed.");
  L = nfinit(nfsplitting(y^3 - 2));
  E = ellinit([0,0,0,-36,0], L);
  rts = nfroots(L, x^3 - 2);
  printf("  L = Galois closure: degree %d, disc %s;  x^3-2 has %d roots in L\n",
         poldegree(L.pol), L.disc, #rts);
  u = nfbasistoalg(L, rts[1]);
  P2 = [6*u, -6*u^2 - 12*u + 12];
  if(!ellisoncurve(E, P2), print("  *** FAIL: P_2 is not on E"); nfail++);
  Tr = [0];
  for(i = 1, #rts,
    u = nfbasistoalg(L, rts[i]);
    Tr = elladd(E, Tr, [6*u, -6*u^2 - 12*u + 12]));
  printf("  P_2 = (6w, -6w^2-12w+12) in E(K);  Tr(P_2) = %s  (rational, as it must be)\n",
         lift(Tr));
  R = ellsub(E, ellmul(E, P2, 3), Tr);
  o1 = ellorder(E, R);
  o2 = ellorder(E, [-3, 9]);
  printf("  ellorder(3P_2 - Tr P_2) = %d  and  ellorder((-3,9)) = %d   (0 = infinite order)\n",
         o1, o2);
  printf("  E(L)_tors = %s\n", elltors(E)[2]);
  if(o1 != 0 || o2 != 0, print("  *** FAIL: the lower bound argument does not fire"); nfail++);
  print("  ==> c >= 1 and a >= 1, hence rank E(K) = a + c >= 2.");
  return(nfail);
};

verdict(nfail) =
{
  banner("VERDICT");
  printf("  failures: %d\n", nfail);
  print("");
  print("  [T]       rank E(K) = rank E(Q) + c            (S_3 representation theory)");
  print("  [T(CAS)]  rank E(K) >= 2                       (section 6, exact)");
  print("  [T(CAS)]  dim_F2 Sel^2(E/K) = 4, dim_F2 E(K)[2] = 2, so rank E(K) <= 2");
  print("            (section 4; convention calibrated in 1-3; GRH-free by section 0)");
  print("  =======>  rank E(K) = 2 exactly, unconditionally.");
  print("");
  print("  Elliptic curve Chabauty over K needs rank E(K) < [K:Q] = 3.  It is");
  print("  therefore AVAILABLE, with no appeal to BSD and no numerical L-value.");
  print("  E041(e) is promoted from [C(BSD)]+[E] to [T(CAS)]; E041(c) and E041(f)");
  print("  are corrected -- see the header of this file and E042.");
  return(0);
};

run() =
{
  my(nfail = 0, bnfK, bnfQ);
  setparams(0, 5, 10, 10, 20, 0);
  bnfK = bnfinit(y^3 - 2, 1);
  bnfQ = bnfinit(y, 1);
  nfail += inputs(bnfK);
  nfail += calibQ(bnfQ);
  nfail += calibquad();
  nfail += calibsha(bnfQ);
  nfail += maincomp(bnfK);
  nfail += crosscheck(bnfK);
  nfail += lowerbound();
  verdict(nfail);
  return(nfail);
};

run();
