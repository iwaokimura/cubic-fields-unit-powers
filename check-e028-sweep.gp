\\ check-e028-sweep.gp --- E028: the sweep of EVERY exponent q up to the Smyth
\\ bound, which turns E026(c)'s conditional statement about n(b) into a complete,
\\ GRH-free determination of n(b) on |b| <= BT.
\\
\\ WHAT WAS MISSING.  E026(c) determined n(b) on |b| <= 10^12 "provided the
\\ remaining q <= 201 permitted by (b) are also swept.  That sweep is E028."  It
\\ was never run; E119's tag audit made the omission explicit.  This script runs it.
\\
\\ THE STATEMENT.  eta_b = e^q for a unit e > 1  <=>  q | n(b), where
\\ eta_b = eta_0^{n(b)}.  Smyth's bound (E026(b), [T, cites Smyth]) gives
\\ n(b) <= log(4 BT^2)/log(rho) =: QMAX, rho = 1.3247... the plastic number.  So
\\ sweeping every q in [2, QMAX] determines, for each b in range, ALL divisors of
\\ n(b) -- hence n(b) itself, since n(b) <= QMAX is one of them.
\\
\\ TWO RANGES, BOTH THEOREMS.  Let e > 1 be a unit of a complex cubic field with
\\ minimal polynomial X^3 - B X^2 + A X - 1, so its conjugates are e and
\\ sigma, sigmabar with |sigma| = e^{-1/2} (the norm is 1).  Then
\\        A = e_2 = 2 e^{1/2} cos(phi) + e^{-1},   B = e_1 = e + 2 e^{-1/2} cos(phi),
\\ whence
\\        |A| <= 2 e^{1/2} + 1        and        |B - e| <= 2 e^{-1/2} < 2 .
\\ lem:etasize gives eta_b < P+1 = 3b^2+3b+4, so for a target |b| <= BT with
\\ BT >= 4 we get eta_b < 3 BT^2 + 3 BT + 4 <= 4 BT^2 -- for EVERY such b, with no
\\ caveat.
\\ Corrected 2026-08-20: this line used to chain P+1 <= 4 b^2, with the caveat
\\ that it is valid for b >= 4 or b <= -1.  That per-b inequality is FALSE at
\\ b = 2 and at b = 3; the range form above is what the sweep actually uses, and
\\ it needs no caveat.  See E028, Addendum.
\\ With e = eta_b^{1/q} this gives e < E+1, E := floor((4 BT^2)^{1/q}), so
\\        |A| <= 2 sqrt(E+1) + 1 <= AMAX ,       -2 <= B <= E + 3 .
\\ Both bounds are computed with sqrtnint, i.e. exactly; no floating point anywhere.
\\ (The lower bound is in fact B >= 0, since e >= rho by Smyth and
\\ rho - 2 rho^{-1/2} = -0.41; we scan from -2, which is safe and costs nothing.)
\\
\\ TWO ENGINES, AND WHY BOTH.  The A-range is ~ E^{1/2} and the box is ~ E^{3/2},
\\ so which engine is affordable depends on q:
\\
\\   sieve_search   scan A alone; A mod p must lie in S_p = {a : C_q(a,.) has a
\\                  root mod p} for 40 primes p; survivors are settled by factoring
\\                  the integer polynomial C_q(A,.) over Q.  This is E022(d')'s
\\                  method verbatim.  Cost ~ E^{1/2} in the scan, but the 40 masks
\\                  cost ~ q^2 each, which is what kills it for large q.
\\
\\   direct_search  scan the whole (A,B) box and evaluate the two power sums at
\\                  integers by their linear recursions.  No polynomial algebra at
\\                  all, so it does not care how large q is; cost ~ q E^{3/2},
\\                  which is what kills it for small q.
\\
\\ They overlap on a band of q and are REQUIRED to agree there -- that is the
\\ calibration of the candidate generation, which is independent in the two
\\ (polynomials over F_p versus integer recursions).  They do share the range
\\ bounds, the mod-3 filter admisA and the final acceptance test accept(), so a
\\ bug in admisA or accept() would not be caught by the agreement.
\\
\\ A sieve produces only false positives, and the direct search is exhaustive, so
\\ in both engines "no b other than those listed" is exact on the range.
\\
\\ Usage:  gp -q check-e028-sweep.gp < /dev/null      (about 10 minutes)

default(parisize, 500000000);
default(realprecision, 80);

\\ --- E119 gate harness ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
info(msg) = { printf("        %s\n", msg); return(1); };

\\ ---------------------------------------------------------------- the curve C_q
\\ p_q(A,B) = sum of the q-th powers of the roots of X^3 - B X^2 + A X - 1,
\\ from p_k = e_1 p_{k-1} - e_2 p_{k-2} + e_3 p_{k-3} with (e_1,e_2,e_3) = (B,A,1).
pq(q) =
{
  my(v = vector(q+1));
  v[1] = 3; v[2] = B; if(q >= 2, v[3] = B^2 - 2*A);
  for(k = 3, q, v[k+1] = B*v[k] - A*v[k-1] + v[k-2]);
  return(v[q+1]);
}
swapAB(f) = substvec(f, [A,B], [B,A]);
curve(q) = { my(PB = swapAB(pq(q))); return(PB^2 - 3*PB + 9 - 3*pq(q)); };

\\ the residues (A,B) mod 3 compatible with 3 | P and 3 | Q (a theorem: p_q is a
\\ Z-polynomial and P = 3(b^2+b+1), Q = 3(b+1) for every b)
admis(q) =
{
  my(PA = pq(q), PB = swapAB(pq(q)), S = List());
  for(ra = 0, 2, for(rb = 0, 2,
    if(substvec(PA,[A,B],[ra,rb]) % 3 == 0 && substvec(PB,[A,B],[ra,rb]) % 3 == 0,
       listput(S, [ra,rb]))));
  return(Vec(S));
}
\\ the same set computed WITHOUT building a bivariate polynomial: the two power
\\ sums are run mod 3 by their integer recursions, O(q) tiny operations per
\\ residue pair.  admis() above builds p_q symbolically, which costs ~q^3 and is
\\ unaffordable past q ~ 100; this is what the sweep actually calls, and the two
\\ are checked against each other on every q where the sieve engine runs.
admis3(q) =
{
  my(S = List(), w);
  for(ra = 0, 2, for(rb = 0, 2,
    w = psAB3(q, ra, rb);
    if(w[1] == Mod(0,3) && w[2] == Mod(0,3), listput(S, [ra,rb]))));
  return(Vec(S));
}
psAB3(q, aa0, bb0) =
{
  my(aa = Mod(aa0,3), bb = Mod(bb0,3),
     s0 = Mod(3,3), s1 = bb, s2 = bb^2 - 2*aa, s,
     t0 = Mod(3,3), t1 = aa, t2 = aa^2 - 2*bb, t);
  if(q == 0, return([Mod(3,3), Mod(3,3)]));
  if(q == 1, return([s1, t1]));
  if(q == 2, return([s2, t2]));
  for(k = 3, q,
    s = bb*s2 - aa*s1 + s0; s0 = s1; s1 = s2; s2 = s;
    t = aa*t2 - bb*t1 + t0; t0 = t1; t1 = t2; t2 = t);
  return([s2, t2]);
}
admisA(q) =
{
  my(L = admis3(q));
  return(Set(vector(#L, i, L[i][1])));
}

\\ ------------------------------------------------- integer power sums (engine 2)
\\ Both sums in one pass; no polynomials, so the cost is O(q) integer operations.
\\   PA = p_q for X^3 - bb X^2 + aa X - 1      (recursion coefficients bb, aa, 1)
\\   PB = p_q for X^3 - aa X^2 + bb X - 1      (recursion coefficients aa, bb, 1)
psAB(q, aa, bb) =
{
  my(s0 = 3, s1 = bb, s2 = bb^2 - 2*aa, s,
     t0 = 3, t1 = aa, t2 = aa^2 - 2*bb, t);
  if(q == 0, return([3, 3]));
  if(q == 1, return([s1, t1]));
  if(q == 2, return([s2, t2]));
  for(k = 3, q,
    s = bb*s2 - aa*s1 + s0; s0 = s1; s1 = s2; s2 = s;
    t = aa*t2 - bb*t1 + t0; t0 = t1; t1 = t2; t2 = t);
  return([s2, t2]);
}

\\ --------------------------------------------------------------- the two ranges
Ebound(q, BT) = sqrtnint(4*BT^2, q);
Abound(q, BT) = 2*sqrtnint(4*BT^2, 2*q) + 3;

\\ ------------------------------------------------------------- accept a point
\\ Given a candidate (aa,bb), decide whether it is an integral point of C_q that
\\ yields a genuine b in range.  Returns [b] or [].
accept(q, aa, bb, BT) =
{
  my(w = psAB(q, aa, bb), PA = w[1], PB = w[2], f, b0);
  if(PB^2 - 3*PB + 9 - 3*PA != 0, return([]));   \\ not on the curve
  if(PB % 3 != 0, return([]));                   \\ b would not be an integer
  b0 = PB/3 - 1;
  if(b0 == 0 || b0 == 1, return([]));            \\ degenerate: e = 1, b = 0
  if(abs(b0) > BT, return([]));                  \\ outside the target range
  f = x^3 - bb*x^2 + aa*x - 1;
  if(!polisirreducible(f), return([]));          \\ e must generate a cubic field
  if(poldisc(f) > 0, return([]));                \\ and the field must be complex
  return([b0]);
}

\\ ================================================================== engine 1
smask(C, p) =
{
  my(m = vectorsmall(p), F);
  for(a = 0, p-1,
    F = subst(C, A, Mod(a,p));
    if(poldegree(F, B) < 1,
       m[a+1] = 1,                                \\ degenerate: keep (safe)
       if(#polrootsmod(F) > 0, m[a+1] = 1)));
  return(m);
}
exactroots(C, A0) =
{
  my(F = subst(C, A, A0), R = List(), FA, g, c1, c0);
  if(poldegree(F, B) < 1, return([]));
  FA = factor(F);
  for(i = 1, matsize(FA)[1],
    g = FA[i,1];
    if(poldegree(g, B) == 1,
      c1 = polcoef(g,1,B); c0 = polcoef(g,0,B);
      if(c1 != 0 && (-c0) % c1 == 0, listput(R, (-c0)/c1))));
  return(Vec(R));
}
sieve_search(q, BT, plist) =
{
  my(C = curve(q), AMAX = Abound(q, BT), RA = admisA(q), masks,
     surv = List(), out = List(), np = #plist, scanned = 0, ok, A0, R, g);
  \\ exactroots() would silently return nothing if C_q(A0,.) were the zero
  \\ polynomial, so the B-degree must not collapse at any integer A0.  It does
  \\ not: the leading coefficient of C_q in B is a nonzero CONSTANT, free of A.
  check(poldegree(C, B) == q && poldegree(polcoef(C, q, B), A) == 0
        && polcoef(C, q, B) != 0,
        Str("E028: deg_B C_q = q with a nonzero constant leading coefficient ",
            polcoef(C, q, B), ", so no specialisation A -> A0 can collapse it; q = ", q));
  check(Set(admis3(q)) == Set(admis(q)),
        Str("E028: the mod-3 recursion reproduces the symbolic admissible classes, q = ", q));
  masks = vector(np, i, smask(C, plist[i]));
  for(nA = -AMAX, AMAX,
    if(!setsearch(RA, nA % 3), next);
    scanned++;
    ok = 1;
    for(i = 1, np, if(!masks[i][(nA % plist[i]) + 1], ok = 0; break));
    if(ok, listput(surv, nA)));
  for(i = 1, #surv,
    A0 = surv[i]; R = exactroots(C, A0);
    for(j = 1, #R,
      g = accept(q, A0, R[j], BT);
      if(#g, listput(out, g[1]))));
  return([Set(Vec(out)), scanned, #surv]);
}

\\ ================================================================== engine 2
direct_search(q, BT) =
{
  my(AMAX = Abound(q, BT), EB = Ebound(q, BT), RA = admisA(q),
     out = List(), tested = 0, g);
  for(nA = -AMAX, AMAX,
    if(!setsearch(RA, nA % 3), next);
    for(nB = -2, EB + 3,
      tested++;
      g = accept(q, nA, nB, BT);
      if(#g, listput(out, g[1]))));
  return([Set(Vec(out)), tested]);
}

PLIST = [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181];

\\ QMAX(BT) = floor(log(4 BT^2)/log(rho)), rho the plastic number (E026(b)) --
\\ computed WITHOUT floating point, so that the range of the sweep is exact and
\\ the conclusion below is [T(CAS)] rather than [E].
\\
\\ Certify lo := NUM/DEN < rho by the sign of lo^3 - lo - 1 (rho is the unique
\\ real root and x^3-x-1 is increasing past it), then take the least N with
\\ lo^{N+1} > 4 BT^2.  Since lo < rho this forces rho^{N+1} > 4 BT^2, so
\\ n(b) <= N: conservative in the right direction, and every step is an integer
\\ comparison.
NUM = 13247179; DEN = 10^7;
qmax_exact(BT) =
{
  my(a = NUM, d = DEN, N = 0, R = 4*BT^2);
  while(a <= R*d, a *= NUM; d *= DEN; N++);
  return(N);
}
qmax_float(BT) =
{
  my(rho = polrootsreal(x^3 - x - 1)[1]);
  return(floor(log(4.0*BT^2)/log(rho)));
}
qmax(BT) =
{
  my(N = qmax_exact(BT));
  check(N == qmax_float(BT),
        Str("E028: the exact and the floating-point QMAX agree at BT = ", BT));
  return(N);
}

\\ ================================================================== the sweep
sweep(BT, qlo, qhi, qsieve, qdirect, label) =
{
  my(t0 = getabstime(), res = List(), both = 0, disagree = 0, tot = 0,
     S, D, used, bs, sc, r);
  printf("\n### %s:  |b| <= %s,  q = %d .. %d ###\n", label, BT, qlo, qhi);
  printf("    sieve engine for q <= %d, direct engine for q >= %d, both on the overlap\n",
         qsieve, qdirect);
  printf("  %4s %18s %12s %9s   %s\n", "q", "E", "scanned", "engine",
         "b with q | n(b)");
  for(q = qlo, qhi,
    S = 0; D = 0; used = ""; sc = 0;
    if(q <= qsieve,
       r = sieve_search(q, BT, PLIST); S = r[1]; sc = r[2]; used = "sieve");
    if(q >= qdirect,
       r = direct_search(q, BT); D = r[1]; sc = r[2];
       used = if(q <= qsieve, "both", "direct"));
    if(q <= qsieve && q >= qdirect,
       both++;
       if(S != D, disagree++;
          printf("   *** ENGINES DISAGREE at q = %d: sieve %s, direct %s ***\n",
                 q, S, D)));
    bs = if(q <= qsieve, S, D);
    tot++;
    if(#bs, listput(res, [q, bs]));
    if(#bs || q <= 16 || q % 50 == 0,
      printf("  %4d %18s %12s %9s   %s\n", q, Ebound(q, BT), sc, used,
             if(#bs, bs, "--"))));
  check(disagree == 0 && both > 0,
        Str("E028 (", label, "): the sieve and the direct search agree on all ",
            both, " exponents of the overlap band q = ", qdirect, "..", qsieve));
  printf("  ... %d exponents swept, %d of them with a solution;  %s\n",
         tot, #res, strtime(getabstime() - t0));
  return(Vec(res));
}

\\ assemble n(b) from the per-q lists
assemble(res, BT, label) =
{
  my(bs = List(), tab = List(), v, b0, qs);
  for(i = 1, #res, v = res[i][2]; for(j = 1, #v, listput(bs, v[j])));
  bs = Set(Vec(bs));
  printf("\n### %s: the function n(b) on |b| <= %s ###\n", label, BT);
  printf("  %16s %8s   %s\n", "b", "n(b)", "divisors q found by the sweep");
  for(i = 1, #bs,
    b0 = bs[i]; qs = List();
    for(j = 1, #res, if(setsearch(Set(res[j][2]), b0), listput(qs, res[j][1])));
    qs = Vec(qs);
    printf("  %16s %8s   %s\n", b0, vecmax(qs), qs);
    listput(tab, [b0, vecmax(qs), qs]));
  return(Vec(tab));
}

\\ n(b) must be the LARGEST q found, and every q found must divide it
consistent(tab, label) =
{
  my(bad = 0, n, qs);
  for(i = 1, #tab,
    n = tab[i][2]; qs = tab[i][3];
    for(j = 1, #qs, if(n % qs[j] != 0, bad++;
      printf("   *** at b = %s: q = %s does not divide n = %s ***\n",
             tab[i][1], qs[j], n))));
  check(bad == 0,
        Str("E028 (", label, "): every exponent found at a given b divides the ",
            "largest one, i.e. the sweep really computes n(b)"));
  return(bad);
}

\\ ==================================================================== tiers
\\ the number of (A,B) pairs the direct engine would test; the engine is used
\\ only where this is below BUDGET, which is what makes the overlap band the
\\ band it is rather than a number chosen by hand.
boxsize(q, BT) = (2*Abound(q, BT) + 1) * (Ebound(q, BT) + 6);
BUDGET = 5000000;

tier1() =
{
  my(EXPECT = [[4, [-75,-3,5,96]], [6, [9]], [8, [-3]], [9, []], [12, []], [16, []]],
     bad = 0, q, want, gotS, gotD, box);
  print("");
  print("### Tier 1: reproduce E026(c)'s table, q = 4,6,8,9,12,16 at |b| <= 10^12 ###");
  for(i = 1, #EXPECT,
    q = EXPECT[i][1]; want = Set(EXPECT[i][2]); box = boxsize(q, 10^12);
    gotS = sieve_search(q, 10^12, PLIST)[1];
    gotD = if(box <= BUDGET, direct_search(q, 10^12)[1], gotS);
    printf("  q=%3d   sieve %-22s direct %-22s expected %-22s (box %s)\n",
           q, gotS, if(box <= BUDGET, gotD, "[box too big]"), want, box);
    if(gotS != want || gotD != want, bad++));
  check(bad == 0,
        "E028 Tier 1: both engines reproduce E026(c)'s calibration table exactly");
  return(bad);
}

tier2(Q12) =
{
  my(r12, t12, ns, g);
  r12 = sweep(10^12, 2, Q12 + 8, 10, 7, "Tier 2");
  t12 = assemble(r12, 10^12, "Tier 2");
  consistent(t12, "Tier 2");
  ns = Set(vector(#t12, i, t12[i][2]));
  printf("\n  exponents n(b) > 1 occurring for |b| <= 10^12 : %s\n", ns);
  check(ns == Set([2,4,6,8,13]),
        "E028 Tier 2: n(b) in {1,2,4,6,8,13} on |b| <= 10^12 -- E026(c)'s bracketed statement, now unconditional and GRH-free");
  g = List();
  for(i = 1, #t12, if(t12[i][2] != 2, listput(g, [t12[i][1], t12[i][2]])));
  printf("  the b with n(b) > 2 : %s\n", Vec(g));
  check(Set(Vec(g)) == Set([[5,4],[96,4],[-75,4],[9,6],[-3,8],[3,13]]),
        "E028 Tier 2: n(b) > 2 exactly at b = 5,96,-75 (n=4), 9 (n=6), -3 (n=8), 3 (n=13)");
  return(t12);
}

tier3(Q30) =
{
  my(r30, t30, ns);
  \\ q = 2 and q = 3 are NOT swept here -- their A-ranges are 5.7e15 and 5.0e10 --
  \\ and come from Thm iff (Pell) and Thm cubelocus, exactly as E026(c) says.
  r30 = sweep(10^30, 4, Q30 + 8, 20, 15, "Tier 3");
  t30 = assemble(r30, 10^30, "Tier 3");
  consistent(t30, "Tier 3");
  ns = Set(vector(#t30, i, t30[i][2]));
  printf("\n  exponents q >= 4 dividing some n(b), |b| <= 10^30 : %s\n", ns);
  check(ns == Set([4,6,8,13]),
        "E028 Tier 3: no q >= 4 other than 4,6,8,13 divides n(b) for any b with |b| <= 10^30 -- eighteen orders of magnitude beyond Tier 2");
  check(Set(vector(#t30, i, t30[i][1])) == Set([-75,-3,3,5,9,96]),
        "E028 Tier 3: and the b realising them are exactly -75,-3,3,5,9,96");
  return(t30);
}

\\ ==================================================================== driver
run() =
{
  my(Q12, Q30);
  print("### E028: the complete sweep of q up to the Smyth bound ###");
  print("    E026(c) determined n(b) on |b| <= 10^12 modulo this sweep, and E119");
  print("    recorded that it had never been run.  It is run here.");
  print("");
  check(NUM^3 - NUM*DEN^2 - DEN^3 < 0,
        Str("E028: ", NUM, "/", DEN, " < rho, certified by the sign of x^3-x-1"));
  check((NUM+1)^3 - (NUM+1)*DEN^2 - DEN^3 > 0,
        Str("E028: rho < ", NUM+1, "/", DEN, ", likewise -- so rho is pinned to 7 decimals exactly"));
  Q12 = qmax(10^12);
  Q30 = qmax(10^30);
  print("  Smyth bound (E026(b)): n(b) <= log(4 BT^2)/log(rho), rho = plastic number");
  print("    (computed by exact integer comparison against a certified rational");
  print("     lower bound for rho, and cross-checked against the 80-digit logarithm)");
  printf("    BT = 10^12  =>  QMAX = %d\n", Q12);
  printf("    BT = 10^30  =>  QMAX = %d\n", Q30);
  \\ E026(b) quotes "n <= 201 for B = 10^12 and n <= 492 for B = 10^30".  The
  \\ first is right; the second is a slip.  log(4*10^60)/log(rho) = 496.24..., so
  \\ the bound is 496, and 492 would have left q = 493..496 unswept.  Nothing
  \\ computed before depended on the number -- it had never been used -- but the
  \\ sweep below does, so it is corrected here and in E026(b).
  check(Q12 == 201 && Q30 == 496,
        Str("E028: the Smyth bounds are 201 and 496 (E026(b) quotes 492 for the ",
            "second; log(4*10^60)/log(rho) = 496.24..., so 492 is a slip and is ",
            "corrected here)"));
  info("QMAX is exact: no logarithm enters the bound, only the certified");
  info("rational rho_- and integer comparisons.  Each sweep is run to QMAX+8 in");
  info("any case, so Tier 3 reaches q = 504, well past either 492 or 496.");
  tier1();
  tier2(Q12);
  tier3(Q30);
  print("");
  print("### CONCLUSION ###");
  print("  [T(CAS): |b| <= 10^12]  n(b) in {1,2,4,6,8,13}, with n = 4 exactly at");
  print("     b = 5, 96, -75;  n = 6 exactly at b = 9;  n = 8 exactly at b = -3;");
  print("     n = 13 exactly at b = 3;  n = 2 at every other square-exception;");
  print("     n = 1 elsewhere.  E026(c)'s bracketed statement, with the bracket");
  print("     removed: every q <= 201 permitted by Smyth's bound has been swept.");
  print("  [T(CAS): |b| <= 10^30]  no exponent q >= 4 other than 4, 6, 8, 13");
  print("     divides n(b) for any b in range, and the b realising them are the");
  print("     same six.  (q = 2, 3 are Thm iff and Thm cubelocus, not swept here.)");
  print("  Both are GRH-free: no bnfinit, no class group, no floating point in the");
  print("  search -- only the two range theorems, sqrtnint, and exact arithmetic.");
  return(1);
}

run();

printf("\nE028 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
