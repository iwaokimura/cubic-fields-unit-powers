\\ check-composite-q.gp --- E026 (c): the exponent n itself, not only its prime
\\ divisors, by running the E022 machinery at COMPOSITE q.
\\
\\ CONTEXT.  E021/E022 asked, for a PRIME q, whether eta_b = e^q for a unit e > 1.
\\ Newton's identities turn that into an integral point of the plane curve
\\     C_q :  p_q(B,A)^2 - 3 p_q(B,A) + 9 - 3 p_q(A,B) = 0 ,   b = p_q(B,A)/3 - 1 ,
\\ where p_q(A,B) is the sum of the q-th powers of the roots of X^3-BX^2+AX-1.
\\ NOTHING in that construction uses primality of q.  For the sequel's question --
\\ eta_b = eta_0^{n}, what is n? -- one needs exactly the composite q as well, since
\\ n is determined by which prime powers (and which q = 2p) divide it.
\\
\\ WELL-DEFINEDNESS AT EVEN q.  If e^q = eta_b > 1 with e real, then for even q the
\\ sign of e is free; replacing e by -e we may and do take e > 1, so the minimal
\\ polynomial X^3-BX^2+AX-1 (norm +1) is the right normal form for every q.
\\
\\ THE SEARCH.  Exactly as in check-qpow-sieve.gp, and exact (no floating point):
\\   * |A| = |e_2(e)| = |2 e^{1/2} cos(phi) + e^{-1}| <= 2 e^{1/2} + 1 with
\\     e = eta_b^{1/q} and eta_b < P+1 <= 4b^2 (lem:etasize), so a target
\\     |b| <= BT needs only |A| <= AMAX = 2*(4 BT^2)^{1/(2q)} + 1, computed
\\     exactly with sqrtnint;
\\   * A mod 3 is restricted to the classes admissible mod 3 -- recomputed for each
\\     q, since for composite q the mod-3 step of E022(a) is WEAKER: for q = 4 the
\\     admissible classes are (0,0),(1,1),(2,2), not (0,0) alone;
\\   * A mod p must lie in S_p = {a : C_q(a,.) has a root mod p} for 40 primes p;
\\     a sieve only produces false positives, so nothing can be lost;
\\   * each survivor is settled by factoring the integer polynomial C_q(A,.) over Q.
\\
\\ CALIBRATION.  The known exponents for |b| <= 3000 (E024(g)) are n = 4 at
\\ b = 5, 96, -75;  n = 6 at b = 9;  n = 8 at b = -3;  n = 13 at b = 3.  So C_4 must
\\ return b = 5, 96, -75, -3 (the last because 4 | 8), C_6 must return b = 9, and
\\ C_8 must return b = -3.  It does.
\\
\\ Usage:  gp -q check-composite-q.gp        (about a second)

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

pq(q) =
{
  my(v = vector(q+1));
  v[1] = 3; v[2] = B; if(q >= 2, v[3] = B^2 - 2*A);
  for(k = 3, q, v[k+1] = B*v[k] - A*v[k-1] + v[k-2]);
  v[q+1];
}
swapAB(f) = substvec(f, [A,B], [B,A]);
curve(q) = my(PB = swapAB(pq(q))); PB^2 - 3*PB + 9 - 3*pq(q);
admis(q) =
{
  my(PA = pq(q), PB = swapAB(pq(q)), S = List());
  for(ra = 0, 2, for(rb = 0, 2,
    if(substvec(PA,[A,B],[ra,rb]) % 3 == 0 && substvec(PB,[A,B],[ra,rb]) % 3 == 0,
       listput(S, [ra,rb]))));
  Vec(S);
}
smask(C, p) =
{
  my(m = vectorsmall(p));
  for(a = 0, p-1,
    my(F = subst(C, A, Mod(a,p)));
    if(poldegree(F, B) < 1, m[a+1] = 1,
       if(#polrootsmod(F) > 0, m[a+1] = 1)));
  m;
}
exactroots(C, A0) =
{
  my(F = subst(C, A, A0), R = List(), FA);
  if(F == 0, return([]));
  FA = factor(F);
  for(i = 1, matsize(FA)[1],
    my(g = FA[i,1]);
    if(poldegree(g, B) == 1,
      my(c1 = polcoef(g,1,B), c0 = polcoef(g,0,B));
      if(c1 != 0 && (-c0) % c1 == 0, listput(R, (-c0)/c1))));
  Vec(R);
}
\\ returns the sorted set of b found (excluding the degenerate b = 0)
verify(q, BT, plist) =
{
  my(C = curve(q), PB = swapAB(pq(q)), AMAX, RA, masks, surv = List(),
     scanned = 0, t0 = getabstime(), np = #plist, AD = admis(q), out = List());
  AMAX = 2*sqrtnint(4*BT^2, 2*q) + 3;
  RA = Set(vector(#AD, i, AD[i][1]));
  masks = vector(np, i, smask(C, plist[i]));
  for(nA = -AMAX, AMAX,
    if(!setsearch(RA, nA % 3), next);
    scanned++;
    my(ok = 1);
    for(i = 1, np, if(!masks[i][(nA % plist[i]) + 1], ok = 0; break));
    if(ok, listput(surv, nA)));
  print("  q = ", q, "   deg C_q = ", poldegree(C,A), " (deg_B = ", poldegree(C,B),
        ")   admissible (A,B) mod 3: ", AD);
  print("      AMAX = ", AMAX, "   A scanned: ", scanned,
        "   survivors: ", Vec(surv), "   time ", strtime(getabstime()-t0));
  for(i = 1, #surv,
    my(A0 = surv[i], R = exactroots(C, A0));
    for(j = 1, #R,
      my(nB = R[j], uu = substvec(PB,[A,B],[A0,nB]));
      if(uu % 3 == 0,
        my(bb = uu/3 - 1);
        print("        (A,B) = (", A0, ",", nB, ")   b = ", bb,
              if(bb == 0, "   (degenerate: e = 1)", ""));
        if(bb != 0, listput(out, bb)),
        print("        (A,B) = (", A0, ",", nB, ")   3 does not divide p_q(B,A): no b"))));
  vecsort(Vec(out), , 8);
}

\\ NB (gp gotcha): this gp build mis-parses a statement split
\\ across physical lines in a script file unless it is wrapped in braces.  Keep the
\\ two assignments below on one line each.
PLIST = [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181];
BT = 10^12;

print("### composite exponents q: complete exact search for |b| <= ", BT, " ###");
print("    (eta_b = e^q for a unit e > 1  <=>  q | n(b))");
print("");
EXPECT = [[4, [-75,-3,5,96]], [6, [9]], [8, [-3]], [9, []], [12, []], [16, []]];
{
my(bad = 0);
for(i = 1, #EXPECT,
  my(q = EXPECT[i][1], want = vecsort(EXPECT[i][2], , 8));
  my(got = verify(q, BT, PLIST));
  if(got != want, bad++; print("      *** MISMATCH: expected ", want, ", got ", got),
                  print("      => q | n(b) exactly for b in ", got, "   (as expected)"));
  print("");
);
print("  deviations from the calibration list: ", bad);
check(bad == 0, "E026(c): the exact sieve at q=4,6,8,9,12,16 reproduces the exponent table of E024(g) over |b|<=10^12");
}
print("");
print("### CONCLUSION [E: |b| <= ", BT, ", exact] ###");
print("  4 | n(b)  only for b = -75, -3, 5, 96;   6 | n(b)  only for b = 9;");
print("  8 | n(b)  only for b = -3;   and 9, 12, 16 never divide n(b).");
print("  With q = 2 <=> Pell (thm:iff), q = 3 <=> b = 9 (lem:towernocube), and the");
print("  E022 search for q = 5,7,11,13, this gives  n(b) in {1,2,4,6,8,13}  on the");
print("  range -- pending the sweep of the remaining q <= log(4 BT^2)/log(rho) = ");
print("  ", floor(log(4.0*BT^2)/log(polrootsreal(x^3-x-1)[1])), "  (Smyth's bound, check-expo.gp (b)), which is E028.");
printf("\nE026 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);

quit
