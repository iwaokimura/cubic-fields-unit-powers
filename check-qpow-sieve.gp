\\ check-qpow-sieve.gp --- E022 verification: the |b| <= 10^30 search WITHOUT any
\\ floating-point arithmetic.
\\
\\ check-qpow.gp searched C_q for integral points by locating the real roots of
\\ C_q(A,.) numerically (polrootsreal) and testing the nearest integers exactly.
\\ The reduction "|b| <= BT  =>  |A| <= AMAX" is a theorem, but the root location is
\\ floating point, so a mislocated root could in principle hide a solution.  This
\\ script re-proves the same conclusion by a completely different and EXACT route.
\\
\\ THE IDEA.  If (A,B) in Z^2 lies on C_q, then for every prime p the residue
\\ a = A mod p lies in
\\        S_p := { a in F_p : C_q(a, .) has a root in F_p } .
\\ Each S_p is computed exactly with polrootsmod.  Since |S_p|/p is about
\\ 1-(1-1/p)^... ~ 0.63 for a random polynomial of degree q, intersecting a couple of
\\ dozen such conditions cuts the candidate set for A by a factor ~10^-6, so almost
\\ no A survives -- and a surviving A is then settled exactly by factoring the
\\ univariate integer polynomial C_q(A,.) over Q (no floating point anywhere).
\\
\\ A sieve can only produce FALSE POSITIVES: an integral point always survives every
\\ S_p.  So the conclusion "no integral points other than those listed" is exact.
\\ p = 3 is excluded from the sieve primes: the leading coefficient of C_q in B is
\\ -3, so the B-degree collapses mod 3.  The mod-3 condition on A is imposed
\\ separately, exactly as in check-qpow.gp, and is a theorem there.

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

\\ bitmap of S_p: mask[a+1] = 1 iff C_q(a,.) has a root mod p
smask(C, p) =
{
  my(m = vectorsmall(p));
  for(a = 0, p-1,
    my(F = subst(C, A, Mod(a,p)));
    if(poldegree(F, B) < 1,
       m[a+1] = 1,                                   \\ degenerate: keep (safe)
       if(#polrootsmod(F) > 0, m[a+1] = 1)));
  m;
}

\\ exact resolution of one surviving A: does C_q(A0,.) have an integer root?
exactroots(C, A0) =
{
  my(F = subst(C, A, A0), R = List(), FA);
  FA = factor(F);
  for(i = 1, matsize(FA)[1],
    my(g = FA[i,1]);
    if(poldegree(g, B) == 1,
      my(c1 = polcoef(g,1,B), c0 = polcoef(g,0,B));
      if(c1 != 0 && (-c0) % c1 == 0, listput(R, (-c0)/c1))));
  Vec(R);
}

verify(q, BT, plist) =
{
  my(C = curve(q), PB = swapAB(pq(q)), AMAX, RA, masks, surv = List(), dens = 1.0,
     scanned = 0, t0 = getabstime(), np = #plist);
  \\ EXACT bound, no floating point: sqrtnint(x,n) = floor(x^{1/n}) exactly, so
  \\ (4BT^2)^{1/(2q)} < R+1 and the true bound 2(4BT^2)^{1/(2q)}+1 is < 2R+3.
  AMAX = 2*sqrtnint(4*BT^2, 2*q) + 3;
  RA = Set(vector(#admis(q), i, admis(q)[i][1]));
  masks = vector(np, i, smask(C, plist[i]));
  for(i = 1, np, dens *= vecsum(Vec(masks[i])) / (1.0*plist[i]));
  for(nA = -AMAX, AMAX,
    if(!setsearch(RA, nA % 3), next);
    scanned++;
    my(ok = 1);
    for(i = 1, np,
      if(!masks[i][(nA % plist[i]) + 1], ok = 0; break));
    if(ok, listput(surv, nA)));
  print("  q=",q,"   AMAX=",AMAX,"   A scanned: ",scanned,
        "   sieve primes: ",np,"   density ",dens,
        "   expected survivors ~ ",round(scanned*dens*1000)/1000.);
  print("        A surviving the exact sieve: ",Vec(surv));
  check(Set(Vec(surv)) == if(q == 13, Set([-1, 3]), Set([3])), Str("E022(d): the exact sieve leaves A = 3 only (and A = -1 for q=13), q=", q));
  for(i = 1, #surv,
    my(A0 = surv[i], R = exactroots(C, A0));
    print("         A=",A0,"   exact integer roots B of C_q(A,.) over Z: ",R);
    for(j = 1, #R,
      my(nB = R[j], uu = substvec(PB,[A,B],[A0,nB]));
      print("           (A,B)=(",A0,",",nB,")   3 | p_q(B,A) ? ",uu % 3 == 0,
            "   b = ",if(uu % 3 == 0, uu/3 - 1, "n/a"),
            "   X^3-BX^2+AX-1 = ",x^3 - nB*x^2 + A0*x - 1)));
  print("        time ",strtime(getabstime()-t0));
  Vec(surv);
}

PLIST = [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181];

print("### exact (floating-point-free) verification of the |b| <= 10^30 search ###");
print("    method: A mod p must lie in S_p = {a : C_q(a,.) has a root mod p}, for");
print("    each of the ",#PLIST," primes ",PLIST[1]," ... ",PLIST[#PLIST],".  Survivors are then settled by");
print("    factoring C_q(A,.) over Q.  A sieve cannot lose a solution, so this is exact.");
print();
print("### Tier 2: |b| <= 10^12, to be compared with check-q5.gp and check-qpow.gp ###");
verify(5, 10^12, PLIST);
verify(13, 10^12, PLIST);
print();
print("### Tier 3: |b| <= 10^30, all four exponents ###");
foreach([5,7,11,13], q, verify(q, 10^30, PLIST));

print();
print("### CONCLUSION ###");
print("  The only integral points of C_q with |A| <= AMAX(10^30) are the degenerate");
print("  (A,B)=(3,3) -- where X^3-3X^2+3X-1=(X-1)^3, e=1, b=0 -- for q=5,7,11, and in");
print("  addition (A,B)=(-1,0), i.e. b=3, for q=13.  This agrees with the numerical");
print("  search of check-qpow.gp section (4) and uses no floating-point arithmetic.");

printf("\nE022 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
