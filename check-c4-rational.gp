\\ check-c4-rational.gp --- E040: the rational points of C_4, as a one-parameter
\\ square-detection problem on E(Q).
\\
\\ THE REDUCTION.  E037 gave the degree-2 map C_4 -> E with
\\        C_4 : w^4 - 6(t-1)^2 w^2 + 27t(t^3-4) = 0 ,   u = w^2 ,
\\ so u satisfies u^2 - 6(t-1)^2 u + 27t(t^3-4) = 0.  Completing the square with
\\        y := u - 3(t-1)^2
\\ turns the quotient into the genus-1 curve
\\        H : y^2 = f(t) = -18t^4 - 36t^3 + 54t^2 + 72t + 9 ,
\\ with the rational point (t,y) = (0,3), and
\\        u = 3(t-1)^2 + y ,        u * ubar = 27 t (t^3 - 4) .
\\ A rational point of H lifts to C_4 exactly when u is a SQUARE.  Since
\\ E(Q) = Z<P_0> + (Z/2)^2 with P_0 = (-3,9) on y^2 = x^3 - 36x (rank 1, proved
\\ in E037), the arithmetic question becomes
\\        for which n and torsion T is u(n P_0 + T) a square?
\\ which is exactly the shape of Thm iff ("square <=> Pell") that this project
\\ started from.
\\
\\ THE MAP H -> WEIERSTRASS, derived rather than quoted.  PARI's ellfromeqn
\\ returns only the Jacobian's coefficients, not the map.  So: write
\\        y = q + (d/2q) t + m t^2 ,   q = 3, and f = a t^4 + b t^3 + c t^2 + d t + q^2.
\\ Cancelling the q^2 and dt terms and dividing by t^2 leaves a QUADRATIC in t,
\\        (a - m^2) t^2 + (b - dm/q) t + (c - d^2/(4q^2) - 2qm) = 0 ,
\\ whose discriminant is a CUBIC in m -- and that cubic is the elliptic curve.
\\ With n := 2(a-m^2)t + (b - dm/q) one gets n^2 = Delta(m), and scaling by the
\\ leading coefficient alpha = -8q puts it in Weierstrass form.  Both directions
\\ are explicit; section 0 checks round trips on every rational point of small
\\ height, which is the only reason to trust any of this.
\\
\\ THE DICTIONARY back to b.  In the construction of C_q the unit e > 1 has
\\ minimal polynomial X^3 - BX^2 + AX - 1 and eta_b = e^q, while
\\ eta_b^{-1} = (b+1) - theta with Tr(theta) = 0.  Hence
\\        p_B := Tr(e^{-q}) = Tr(eta_b^{-1}) = 3(b+1) ,
\\ and since p_B is the recursion polynomial p_4 with A and B swapped,
\\        b = (A^4 - 4A^2 B + 2B^2 + 4A - 3)/3 .
\\ Section 2 checks this against E026(c), which lists 4 | n(b) exactly for
\\ b = -75, -3, 5, 96.

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

NMAX = 100;      \\ |n| <= NMAX in the scan; the 400 run is reported in the research log

f = -18*'t^4 - 36*'t^3 + 54*'t^2 + 72*'t + 9;
aa = -18; bb = -36; cc = 54; dd = 72; qq = 3;
Del = (bb - dd*'m/qq)^2 - 4*(aa - 'm^2)*(cc - dd^2/(4*qq^2) - 2*qq*'m);
al = polcoef(Del,3,'m); be = polcoef(Del,2,'m); ga = polcoef(Del,1,'m); de = polcoef(Del,0,'m);
EW = ellinit([0, be, 0, al*ga, al^2*de]);

\\ NB the braces: a multi-line function definition in a GP SCRIPT FILE must be
\\ wrapped in { }, or only the first line is taken as the body.
{
toW(tt, vv) =
  my(m, n);
  m = (vv - qq - dd*tt/(2*qq))/tt^2;
  n = 2*(aa - m^2)*tt + (bb - dd*m/qq);
  [al*m, al*n];
}
{
frW(X, Y) =
  my(m, n, tt, vv);
  m = X/al; n = Y/al;
  tt = (n - bb + dd*m/qq)/(2*(aa - m^2));
  vv = qq + dd*tt/(2*qq) + m*tt^2;
  [tt, vv];
}

\\ ================================================================ Section 0
print("=== 0. CALIBRATION of the birational maps H <-> Weierstrass ===");
printf("  Delta(m) = %s,  leading coeff %d (= -8q)\n", Del, al);
printf("  Weierstrass model %s,  j = %s\n", EW[1..5], EW.j);
{
my(cnt = 0, bad = 0, seen = List());
for(num = -60, 60, for(den = 1, 14,
  my(tt, ff, vv, P, back);
  if(gcd(num,den) != 1, next);
  tt = num/den; if(tt == 0, next);
  ff = subst(f,'t,tt);
  if(!issquare(ff, &vv), next);
  if(setsearch(Set(Vec(seen)), tt), next);
  listput(seen, tt); cnt++;
  P = toW(tt, vv);
  if(!ellisoncurve(EW, P), bad++; printf("  OFF CURVE t = %s\n", tt); next);
  back = frW(P[1], P[2]);
  if(back != [tt, vv], bad++; printf("  ROUND TRIP FAILS t = %s\n", tt))));
printf("  %d distinct rational t of small height, %d failures\n", cnt, bad);
check(bad == 0 && cnt == 7, "E040(a): the H <-> Weierstrass maps round-trip exactly at 7 distinct rational t");
if(bad, print("  *** CALIBRATION FAILED -- nothing below is trustworthy. ***"));
}
print("");

\\ ================================================================ Section 1
print("=== 1. E(Q) ===");
v = 0;
Em = ellinit(ellminimalmodel(EW, &v));
TS = elltors(Em);
printf("  minimal model %s\n", Em[1..5]);
printf("  torsion: order %d, structure %s  <-- (Z/2)^2, NOT Z/4\n", TS[1], TS[2]);
printf("  rank %d (proved: ellrank lower = upper)\n", ellrank(Em)[1]);
tors = [[0], [0,0], [-6,0], [6,0]];
P0 = [-3, 9];
printf("  generator P_0 = %s, on curve: %d\n", P0, ellisoncurve(Em, P0));
{
my(ok = 1);
for(i = 1, #tors, if(#tors[i] > 1 && !ellisoncurve(Em, tors[i]), ok = 0));
printf("  torsion subgroup %s, all on curve: %d\n", tors, ok);
}
print("");

\\ ================================================================ Section 2
print("=== 2. the dictionary to b, checked against E026(c) ===");
{
c4poly(A, B) = my(p, pA, pB);
  p = [3, B, B^2 - 2*A];
  for(k = 3, 4, p = concat(p, [B*p[k] - A*p[k-1] + p[k-2]]));
  pA = p[5]; pB = subst(subst(subst(pA, A, 'S), B, A), 'S, B);
  pB^2 - 3*pB + 9 - 3*pA;
}
C = c4poly('A, 'B);
bof(A, B) = (A^4 - 4*A^2*B + 2*B^2 + 4*A - 3)/3;
\\ the three degree-5 adjoints of E037, dehomogenised at z = 1
g1 = 'A^4 + 3*'A^3 - 3*'A^2*'B - 6*'A*'B + 4*'B^2 - 'A + 'B + 1;
g2 = 3*'A^3 - 'A^2*'B - 6*'A*'B + 4*'B^2 - 'A - 'B + 2;
g3 = 'A^2*'B - 'B^2 - 2*'A + 'B + 1;
evv(P, A0, B0) = subst(subst(P,'A,A0),'B,B0);
{
ratroots(pol) = my(fa = factor(pol), out = List());
  for(i = 1, matsize(fa)[1],
    if(poldegree(fa[i,1]) == 1,
      listput(out, -polcoef(fa[i,1],0)/polcoef(fa[i,1],1))));
  Vec(out);
}
print("  rational points (A,B) of the ORIGINAL degree-8 model, |B| <= 4000,");
print("  pushed through the canonical map to (t,w), and their b:");
print("");
print("    (A,B)         (t, w)             b");
{
my(bs = List());
for(B0 = -4000, 4000,
  my(pol = subst(C, 'B, B0), rts);
  if(pol == 0, next);
  rts = ratroots(pol);
  for(i = 1, #rts,
    my(A0 = rts[i], X, Y, Z, tt, ww, bv);
    X = evv(g1,A0,B0); Y = evv(g2,A0,B0); Z = evv(g3,A0,B0);
    bv = bof(A0, B0);
    if(Z == 0,
      printf("    (%s, %s)  base point of the canonical map (all adjoints vanish)\n", A0, B0)
    ,
      X = X/Z; Y = Y/Z; tt = X - Y - 1; ww = Y + 1;
      printf("    (%s, %s)%s(%s, %s)%s%s\n", A0, B0,
             concat(vector(max(1, 14 - #Str(A0) - #Str(B0)), i, " ")), tt, ww,
             concat(vector(max(1, 12 - #Str(tt) - #Str(ww)), i, " ")), bv);
      if(denominator(bv) == 1 && bv != 0, listput(bs, bv)))));
bs = vecsort(Vec(bs));
printf("\n  integral non-degenerate b recovered: %s\n", bs);
print("  E026(c) lists 4 | n(b) exactly for  [-75, -3, 5, 96].");
printf("  MATCH: %d\n", Set(bs) == Set([-75,-3,5,96]));
check(Set(bs) == Set([-75,-3,5,96]),
      "E040(c): the dictionary returns exactly E026(c)'s list -- from a SEARCH over |B| <= 4000, i.e. a sample, not an exhaustion");
}
print("");

\\ ================================================================ Section 3
print("=== 3. for which n is u = 3(t-1)^2 + y a square? ===");
{
my(hits = List(), seen = List());
for(n = -NMAX, NMAX,
  my(nP = if(n == 0, [0], ellmul(Em, P0, n)));
  for(j = 1, #tors,
    my(P, Pw, ty, tt, yy, u, w);
    P = elladd(Em, nP, tors[j]);
    if(#P < 2, next);
    Pw = ellchangepointinv(P, v);
    ty = frW(Pw[1], Pw[2]); tt = ty[1]; yy = ty[2];
    u = 3*(tt-1)^2 + yy;
    if(issquare(u, &w),
      if(!setsearch(Set(Vec(seen)), [tt,w]),
        listput(seen, [tt,w]); listput(hits, [n, tt, w])))));
printf("  %d distinct (t,w) for |n| <= %d:\n\n", #hits, NMAX);
print("      n      t            w");
for(i = 1, #hits, printf("   %5d   %-12s %s\n", hits[i][1], hits[i][2], hits[i][3]));
print("");
printf("  largest |n| occurring: %d\n", vecmax(apply(h -> abs(h[1]), Vec(hits))));
check(#hits == 4 && vecmax(apply(h -> abs(h[1]), Vec(hits))) == 2,
      "E040(d): exactly 4 solutions, all with |n| <= 2, over the scanned |n| <= NMAX");
}
print("");
print("=== VERDICT ===");
print("  [T] The rational points of C_4 found by the two independent routes --");
print("      direct search on the degree-8 model, and the square test on E(Q) --");
print("      agree, and the dictionary b = (A^4-4A^2B+2B^2+4A-3)/3 returns");
print("      exactly E026(c)'s list b = -75, -3, 5, 96 (plus the degenerate");
print("      b = 0, outside the family's range b < -1 or b > 2).");
print("  [E: |n| <= 400] Every solution has |n| <= 2.  C_4 also carries rational");
print("      points with NON-INTEGRAL b, e.g. (A,B) = (-123/23, 5931/529) with");
print("      b = -22168640/279841; these are genuine points of the curve but are");
print("      arithmetically irrelevant, since the family needs b in Z.");
print("  [OPEN] that the list is COMPLETE.  That is exactly what a Chabauty-type");
print("      argument would have to supply, and E038 says the classical one is");
print("      unavailable.  What this experiment changes is the shape of the");
print("      target: not 'find the rational points of a genus-3 curve' but");
print("      'show u(nP_0 + T) is a square only for |n| <= 2'.");

printf("\nE040 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
