\\ check-c4-goodred.gp --- E036, the computation that closes the [GAP] of E035(d):
\\ C_4 has GOOD REDUCTION at p = 5.
\\
\\ WHAT E035 LEFT OPEN.  E035 proved, by the canonical-map rank test, that the
\\ smooth projective model of C_4 mod p is a non-hyperelliptic genus-3 curve for
\\ p = 5,7,11,13.  Passing from there to "C_4/Q is not hyperelliptic" used
\\ specialisation of gonality, which needs GOOD REDUCTION -- and that step was
\\ flagged [GAP].
\\
\\ HOW IT IS CLOSED.  Greuel-Pfister, Thm 33 + Cor 34 (see the header of
\\ E036 for the full citation): for a flat family of affine Noetherian
\\ schemes over the spectrum of a PID, with Nagata total space, no 1-dimensional
\\ components, Coker(normalisation) finite over the base, and fibres having only
\\ finitely many isolated non-normal singularities, a SIMULTANEOUS NORMALISATION
\\ exists if and only if the delta invariant of the fibres is constant.  (Cor 34
\\ upgrades "fibrewise" to "simultaneous" when the residue fields are perfect;
\\ A = Z_(5) has residue fields Q and F_5, both perfect.)
\\
\\ Here A = Z_(5), and delta-constancy is free: both fibres are integral plane
\\ curves of degree 8, so p_a = 21, and both have geometric genus 3 (over Q by
\\ E026, over F_5 by E035), whence
\\        delta(C_4 / Q)  =  21 - 3  =  18  =  21 - 3  =  delta(C_4 / F_5).
\\
\\ THE ONE HYPOTHESIS THAT IS NOT FREE, and the only thing this script computes.
\\ Theorem 33 is a statement about an AFFINE X, and it needs Coker(nu) finite
\\ over A.  In the standard chart that fails: the leading form of C_4 is A^8, so
\\ the projective plane curve meets the line at infinity in the single point
\\ [0:1:0], and that point is SINGULAR (multiplicity 4, tangent cone Z^4).  The
\\ singularities therefore do not all lie in one standard chart.
\\
\\ The fix is to move the line at infinity.  If L is a line over Z_(5) with
\\ L ∩ Sing = ∅, then all singularities of both fibres lie in the affine chart
\\ P^2 \ L, one application of Thm 33 suffices, and along L both fibres are
\\ already smooth, so the normalisation is an isomorphism there and the charts
\\ glue with no further work.
\\
\\ And it is enough to find such an L over F_5 ALONE.  Sing ⊂ P^2_{Z_(5)} is
\\ closed and quasi-finite over Z_(5) (each fibre is a reduced curve, so has
\\ finitely many singular points), hence PROPER, hence FINITE over Z_(5).  So
\\ V(L) ∩ Sing is finite over Z_(5); if it contained a point of the generic
\\ fibre, its closure would surject onto Spec Z_(5) and meet the special fibre.
\\ Therefore
\\        L ∩ Sing(C_4 mod 5) = ∅   ==>   L ∩ Sing = ∅ over all of Z_(5).
\\
\\ So: enumerate the 31 lines of P^2(F_5) and find one disjoint from the singular
\\ subscheme of C_4 mod 5 over the ALGEBRAIC CLOSURE.  A line misses the singular
\\ subscheme iff the three partials, restricted to a parametrisation of the line,
\\ have gcd 1 -- a gcd over F_5[s] decides this over F_5-bar with no extension
\\ arithmetic at all.
\\
\\ CALIBRATION (Commandment X).  Section 0 runs the same test on the nodal cubic
\\ Y^2 Z = X^3 + X^2 Z, whose unique singular point is the node [0:0:1]: the test
\\ must REJECT exactly the 6 lines of P^2(F_5) through [0:0:1] and accept the
\\ other 25.

\\ variable priority: X > Y > Z must be created first
\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

XX = 'X; YY = 'Y; ZZ = 'Z;

\\ ---------------------------------------------------------------- the curve
\\ the recursion of E026: p_0=3, p_1=B, p_2=B^2-2A, p_k = B p_{k-1} - A p_{k-2} + p_{k-3}
{
c4poly(A, B) =
  my(p, pA, pB);
  p = [3, B, B^2 - 2*A];
  for(k = 3, 4, p = concat(p, [B*p[k] - A*p[k-1] + p[k-2]]));
  pA = p[5];
  pB = subst(subst(subst(pA, A, 'T), B, A), 'T, B);
  pB^2 - 3*pB + 9 - 3*pA;
}

\\ homogenise a bivariate polynomial of total degree d to F(X,Y,Z)
{
homog(C, d) =
  my(F, c);
  F = 0;
  for(i = 0, poldegree(C, 'A),
    for(j = 0, poldegree(C, 'B),
      c = polcoef(polcoef(C, i, 'A), j, 'B);
      if(c != 0,
        if(i + j > d, error("total degree exceeds d"));
        F = F + c * 'X^i * 'Y^j * 'Z^(d - i - j))));
  F;
}

evalpt(P, v) = subst(subst(subst(P, 'X, v[1]), 'Y, v[2]), 'Z, v[3]);

\\ ---------------------------------------------------- lines of P^2(F_5)
\\ every line a*X + b*Y + c*Z = 0, normalised so the first nonzero coeff is 1
{
lines(p) =
  my(L, v);
  L = List();
  for(n = 0, p^3 - 1,
    v = [n \ p^2, (n \ p) % p, n % p];
    \\ normalise: first nonzero entry must be 1
    if(v == [0,0,0], next);
    if(v[1] != 0, if(v[1] != 1, next),
       if(v[2] != 0, if(v[2] != 1, next),
          if(v[3] != 1, next)));
    listput(L, v));
  Vec(L);
}

\\ two points spanning the line a*X+b*Y+c*Z = 0 over F_p
{
linebasis(l, p) =
  my(a, b, c);
  a = l[1]; b = l[2]; c = l[3];
  if(a % p != 0,
    \\ X = -(b*Y + c*Z)/a
    return([[(-b) * lift(Mod(a, p)^-1) % p, 1, 0],
            [(-c) * lift(Mod(a, p)^-1) % p, 0, 1]]));
  if(b % p != 0,
    return([[1, 0, 0],
            [0, (-c) * lift(Mod(b, p)^-1) % p, 1]]));
  \\ c != 0, line is Z = 0
  [[1, 0, 0], [0, 1, 0]];
}

\\ does the line l meet V(g1,g2,g3) over F_p-bar ?
\\ parametrise the line as s*P + Q (s in F_p-bar) together with the point P
\\ (which is "s = infinity"); the affine part meets V iff the three restricted
\\ polynomials in s have a common root, i.e. iff their gcd is nonconstant.
{
linemeets(l, G, p) =
  my(bas, P, Q, r, g, d);
  bas = linebasis(l, p);
  P = bas[1]; Q = bas[2];
  \\ the point at s = infinity
  if(sum(i = 1, #G, if(evalpt(G[i], P) % p != 0, 1, 0)) == 0, return(1));
  \\ the affine part
  r = vector(#G);
  for(i = 1, #G,
    r[i] = subst(subst(subst(G[i], 'X, 's * P[1] + Q[1]),
                              'Y, 's * P[2] + Q[2]),
                              'Z, 's * P[3] + Q[3]) * Mod(1, p));
  g = r[1];
  for(i = 2, #G, g = gcd(g, r[i]));
  d = if(g == 0, -1, poldegree(g));
  if(d != 0, 1, 0);
}

{
scanlines(F, p, label) =
  my(G, LL, good, bad, m);
  G = [deriv(F, 'X), deriv(F, 'Y), deriv(F, 'Z), F];
  LL = lines(p);
  good = List(); bad = List();
  for(k = 1, #LL,
    m = linemeets(LL[k], G, p);
    if(m, listput(bad, LL[k]), listput(good, LL[k])));
  printf("  %s: %d lines of P^2(F_%d), %d miss Sing, %d meet Sing\n",
         label, #LL, p, #good, #bad);
  [Vec(good), Vec(bad)];
}

fmtline(l) = Str("(" , l[1], ")X + (", l[2], ")Y + (", l[3], ")Z = 0");

\\ ================================================================ Section 0
print("=== 0. CALIBRATION: the nodal cubic Y^2 Z - X^3 - X^2 Z ===");
print("    unique singular point = the node [0:0:1]; the 6 lines of P^2(F_5)");
print("    through [0:0:1] must be rejected and the other 25 accepted.");
print("");
{
my(Fnod, res, nthru, l);
Fnod = 'Y^2*'Z - 'X^3 - 'X^2*'Z;
res = scanlines(Fnod, 5, "nodal cubic");
nthru = 0;
for(k = 1, #res[2],
  l = res[2][k];
  if((l[1]*0 + l[2]*0 + l[3]*1) % 5 == 0, nthru++));
printf("  of the %d rejected lines, %d pass through the node [0:0:1]\n",
       #res[2], nthru);
check(#res[1] == 25 && #res[2] == 6 && nthru == 6,
      "E036(g): on the nodal cubic over F_5 the line test rejects exactly the 6 lines through the node");
if(#res[1] == 25 && #res[2] == 6 && nthru == 6,
  print("  CALIBRATION PASSED: exactly the 6 lines through the node are rejected.")
,
  print("  *** CALIBRATION FAILED --- the test is wrong, do not trust Section 2. ***"));
}
print("");

\\ ================================================================ Section 1
print("=== 1. C_4 over Z: degree, primitivity, irreducibility, the point at infinity ===");
print("");
C = c4poly('A, 'B);
{
my(Cs, d, L);
Cs = subst(subst(C, 'A, 's*'A), 'B, 's*'B);
d = poldegree(Cs, 's);
L = polcoef(Cs, d, 's);
printf("  total degree d          = %d\n", d);
printf("  deg_A = %d,  deg_B = %d\n", poldegree(C, 'A), poldegree(C, 'B));
printf("  content over Z          = %s\n", content(C));
printf("  leading form C_d(A,B)   = %s\n", L);
printf("  irreducible over Q      = %s\n",
       if(#factor(C)~ == 1 && factor(C)[1,2] == 1, "yes", "NO"));
printf("  arithmetic genus p_a    = %d\n", (d-1)*(d-2)/2);
DEG = d;
}
FF = homog(C, DEG);
{
my(g, h, m);
\\ the curve meets Z = 0 in the divisor of the leading form = 8*[0:1:0],
\\ so [0:1:0] is the unique point at infinity.  Its multiplicity is the order
\\ of vanishing of F(X,1,Z) at (X,Z) = (0,0), i.e. the lowest s-degree of
\\ F(sX, 1, sZ).
g = subst(FF, 'Y, 1);
h = subst(subst(g, 'X, 's*'X), 'Z, 's*'Z);
m = 0;
while(m <= DEG && polcoef(h, m, 's) == 0, m++);
printf("  unique point at infinity = [0:1:0], multiplicity %d", m);
print(if(m > 1, "  <-- SINGULAR: the standard chart does not contain Sing", ""));
printf("  tangent cone there       = %s\n", polcoef(h, m, 's));
}
print("");

\\ ================================================================ Section 2
print("=== 2. delta-constancy at p = 5 ===");
{
my(pa, gQ, g5);
pa = (DEG-1)*(DEG-2)/2;
gQ = 3;   \\ E026, table of g(C_q)
g5 = 3;   \\ E035, check-c4-modp.sage
printf("  p_a(C_4) = %d in both fibres (degree %d, integral)\n", pa, DEG);
printf("  g(C_4/Q)   = %d  [E026]          ==>  delta over Q   = %d\n", gQ, pa - gQ);
printf("  g(C_4/F_5) = %d  [E035]          ==>  delta over F_5 = %d\n", g5, pa - g5);
printf("  delta constant across Spec Z_(5): %s\n",
       if(pa - gQ == pa - g5, "YES", "NO"));
printf("  leading form mod 5 = %s  (so deg = %d mod 5 too, p_a = %d)\n",
       lift(Mod(1,5) * polcoef(subst(subst(C,'A,'s*'A),'B,'s*'B), DEG, 's)),
       DEG, pa);
}
print("");

\\ ================================================================ Section 3
print("=== 3. an F_5-line disjoint from Sing(C_4 mod 5) ===");
print("");
{
my(F5, res, l);
F5 = FF * Mod(1, 5);
res = scanlines(F5, 5, "C_4 mod 5");
if(#res[1] == 0,
  print("");
  print("  VERDICT: NO F_5-line misses Sing.  The chart trick fails at p = 5;");
  print("  try p = 7, 11, 13, or a quadratic-extension line.  The [GAP] STANDS.")
,
  print("");
  \\ cross-check: [0:1:0] is singular mod 5, so every line through it must be
  \\ rejected -- that is 6 of the 21, and none of the accepted lines may pass.
  printf("  cross-check: accepted lines through the singular point [0:1:0]: %d",
         sum(k = 1, #res[1], if(res[1][k][2] % 5 == 0, 1, 0)));
  print("  (must be 0)");
  printf("  cross-check: rejected lines through [0:1:0]: %d  (must be 6)\n",
         sum(k = 1, #res[2], if(res[2][k][2] % 5 == 0, 1, 0)));
  print("");
  check(#res[1] == 10 && #res[2] == 21
        && sum(k = 1, #res[1], if(res[1][k][2] % 5 == 0, 1, 0)) == 0
        && sum(k = 1, #res[2], if(res[2][k][2] % 5 == 0, 1, 0)) == 6,
        "E036(d): exactly 10 of the 31 lines of P^2(F_5) miss Sing(C_4 mod 5); none of them passes through [0:1:0], and 6 of the 21 rejected ones do");
  print("  lines that miss Sing (any one of them works):");
  for(k = 1, #res[1], printf("    %s\n", fmtline(res[1][k])));
  l = res[1][1];
  print("");
  printf("  CHOSEN L : %s\n", fmtline(l));
  print("");
  print("  VERDICT: Sing(C_4 mod 5) is disjoint from L, hence (properness of");
  print("  Sing over Z_(5)) Sing is disjoint from L over all of Z_(5).  All");
  print("  singularities of both fibres lie in the affine chart P^2 \\ L, where");
  print("  Greuel-Pfister Thm 33 + Cor 34 apply with delta = 18 constant.");
  print("  ==> simultaneous normalisation over Z_(5) ==> a smooth proper");
  print("      relative curve of genus 3 ==> C_4 HAS GOOD REDUCTION AT 5.");
  print("  ==> E035(d) is promoted from [C(good reduction)] + [GAP] to [T].");
  );
}

printf("\nE036 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
