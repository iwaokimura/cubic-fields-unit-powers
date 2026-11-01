\\ check-c4-prym.gp --- E038: how big is the Prym?  I.e. is classical Chabauty
\\ available at q = 4?
\\
\\ THE QUESTION.  E037 showed Aut(C_4) = Z/2 with quotient the rank-1 elliptic
\\ curve E: y^2 = x^3 - 36x, so
\\        Jac(C_4) ~ E x P ,   dim P = 2 ,
\\        rank Jac(C_4)(Q) = 1 + rank P(Q) .
\\ Classical Chabauty needs rank Jac < g = 3, i.e. needs rank P(Q) <= 1.  This
\\ script estimates rank P.
\\
\\ WHAT CAN AND CANNOT BE PROVED HERE (Commandment VIII, before implementing).
\\ Computing rank P(Q) is a descent on an abelian surface, and neither PARI/GP
\\ nor Sage implements that.  So an unconditional [T] is NOT available and is not
\\ attempted.  What IS cheap and exact is the trace of Frobenius:
\\        a_p(X) = p + 1 - #X(F_p),      a_p(P) = a_p(X) - a_p(E) ,
\\ the second identity being exact because Jac(X) ~ E x P.  From those a
\\ Mestre-Nagao sum estimates the rank.  The result is therefore [P], and the
\\ script's job is to make that [P] as sharp and as honestly calibrated as it can
\\ be -- which is why sections 0 and 2 are longer than section 1.
\\
\\ THE POINT COUNT IS O(p), NOT O(p^2).  In the coordinates of E037,
\\        X : w^4 + b(t) w^2 + a(t) = 0 ,   a = 27t^4 - 108t ,  b = -6(t-1)^2 ,
\\ so for each t one solves a QUADRATIC in u = w^2 and counts square roots:
\\ #{w} = sum over roots u of (1 + legendre(u,p)).  The line at infinity meets X
\\ where 27T^4 - 6T^2W^2 + W^4 = 0, i.e. at [1:s:0] with s^4 - 6s^2 + 27 = 0.
\\ Section 0 checks this against TWO independent brute forces.

default(parisize, 900000000);

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

B      = 20000;    \\ prime bound for the sums
BRUTE  = 60;       \\ calibrate the fast count against brute force below this

QUARTIC = 27*'X^4 - 108*'X^3*'Y + 156*'X^2*'Y^2 - 96*'X*'Y^3 + 22*'Y^4 \
        - 108*'X^3*'Z + 312*'X^2*'Y*'Z - 276*'X*'Y^2*'Z + 76*'Y^3*'Z \
        + 156*'X^2*'Z^2 - 264*'X*'Y*'Z^2 + 90*'Y^2*'Z^2 \
        - 192*'X*'Z^3 + 148*'Y*'Z^3 + 112*'Z^4;

\\ ---------------------------------------------------------------- the counts
{
countfast(p) =
  my(u, tot, a, b, DD, r, i2, k);
  tot = 0; i2 = (p+1)/2;
  for(tt = 0, p-1,
    a = (27*tt^4 - 108*tt) % p;
    b = (-6*(tt-1)^2) % p;
    DD = (b*b - 4*a) % p;
    k = kronecker(DD, p);
    if(k == 0,
      u = (-b * i2) % p; tot += 1 + kronecker(u, p)
    , k == 1,
      r = lift(sqrt(Mod(DD, p)));
      u = ((-b + r) * i2) % p; tot += 1 + kronecker(u, p);
      u = ((-b - r) * i2) % p; tot += 1 + kronecker(u, p)));
  tot + #polrootsmod('s^4 - 6*'s^2 + 27, p);
}

\\ brute force in the (t,w) chart -- same coordinates, different algorithm
{
countbrute1(p) =
  my(tot = 0);
  for(tt = 0, p-1, for(ww = 0, p-1,
    if(Mod(27*tt^4 - 108*tt + ww^4 - 6*(tt-1)^2*ww^2, p) == 0, tot++)));
  for(ss = 0, p-1, if(Mod(27 - 6*ss^2 + ss^4, p) == 0, tot++));
  tot;
}

\\ brute force on the ORIGINAL quartic in P^2(F_p) -- different coordinates AND
\\ different algorithm, so this is a genuinely independent check
\\ NB: define the evaluator at top level.  Writing "ev(x,y,z) = ..." for a name
\\ declared in my() does not make a local function in GP; it leaves a t_CLOSURE
\\ where a number is expected.
evq(aa, bb, cc) = substvec(QUARTIC, ['X, 'Y, 'Z], [aa, bb, cc]);
{
countbrute2(p) =
  my(tot = 0);
  for(yy = 0, p-1, for(zz = 0, p-1, if(Mod(evq(1, yy, zz), p) == 0, tot++)));
  for(zz = 0, p-1, if(Mod(evq(0, 1, zz), p) == 0, tot++));
  if(Mod(evq(0, 0, 1), p) == 0, tot++);
  tot;
}

\\ ================================================================ Section 0
print("=== 0. CALIBRATION of the O(p) point count ===");
print("    fast vs brute force in the (t,w) chart, and vs brute force on the");
print("    original quartic in P^2 -- three routes, two of them independent.");
print("");
{
my(bad = 0, f, b1, b2);
forprime(p = 5, BRUTE,
  f = countfast(p); b1 = countbrute1(p); b2 = countbrute2(p);
  if(f != b1 || f != b2, bad++);
  printf("  p = %3d : fast %4d   chart %4d   P^2 %4d   %s\n", p, f, b1, b2,
         if(f == b1 && f == b2, "ok", "*** MISMATCH ***")));
printf("\n  mismatches: %d\n", bad);
check(bad == 0, "E038(a): the O(p) point count agrees with two independent brute forces for every p < 60");
if(bad, print("  *** CALIBRATION FAILED -- everything below is worthless. ***"));
}
print("");

\\ ================================================================ Section 1
print("=== 1. a_p(X), a_p(E), a_p(P) ===");
E = ellinit([0,0,0,-36,0]);
gettime();
plist = List(); apX = List(); apP = List();
{
forprime(p = 5, B,
  my(ax = p + 1 - countfast(p));
  listput(plist, p); listput(apX, ax); listput(apP, ax - ellap(E, p)));
}
{
my(bad = 0, badX = 0);
for(i = 1, #plist,
  \\ squared, so the Weil test is exact integer arithmetic: a float sqrt here
  \\ would put a floating-point step inside a [T(CAS)] claim (E119).
  if(apP[i]^2 > 16*plist[i], bad++);
  if(apX[i]^2 > 36*plist[i], badX++));
printf("  %d good primes p <= %d, in %.1f s\n", #plist, B, gettime()/1000.);
printf("  Weil |a_p(P)| <= 4 sqrt p (dim 2) : %d violations\n", bad);
printf("  Weil |a_p(X)| <= 6 sqrt p (dim 3) : %d violations\n", badX);
check(bad == 0 && badX == 0, "E038(b): every computed a_p(P), a_p(X) satisfies its Weil bound");
print("");
print("  p     a_p(X)  a_p(E)  a_p(P)");
for(i = 1, 8,
  printf("  %4d  %6d  %6d  %6d\n", plist[i], apX[i], ellap(E, plist[i]), apP[i]));
}
print("");

\\ ================================================================ Section 2
print("=== 2. Mestre-Nagao, calibrated at BOTH dimensions ===");
print("    S(B) = sum_{p<=B} a_p log(p) / p ;  heuristically S/log B ~ d/2 - r,");
print("    so the rank estimate is r_est = d/2 - S/log B.  The calibration");
print("    tables below measure how far that is actually to be trusted.");
print("");
{
mnE(c, B) = my(Ej = ellinit(c), s = 0);
  forprime(p = 5, B, if(Ej.disc % p != 0, s += ellap(Ej,p)*log(p)/p)); s;
}
{
mnV(v, pl) = my(s = 0); for(i = 1, #pl, s += v[i]*log(pl[i])/pl[i]); s;
}
L = log(B);
c32 = [0,0,0,-1,0];  c11 = [0,-1,1,0,0];  c37 = [0,0,1,-1,0];
c576 = [0,0,0,-36,0]; c389 = [0,1,1,-2,0]; c5077 = [0,0,1,-7,6];
s32 = mnE(c32,B); s11 = mnE(c11,B); s37 = mnE(c37,B);
s576 = mnE(c576,B); s389 = mnE(c389,B); s5077 = mnE(c5077,B);
print("  DIMENSION 1 (elliptic curves of known rank):");
{
my(d = [[s32,0,"N=32"],[s11,0,"N=11"],[s37,1,"N=37"],[s576,1,"N=576 (our E)"],
        [s389,2,"N=389"],[s5077,3,"N=5077"]]);
for(i = 1, #d,
  printf("    true rank %d  %-14s : r_est = %5.2f   (error %+5.2f)\n",
         d[i][2], d[i][3], 0.5 - d[i][1]/L, 0.5 - d[i][1]/L - d[i][2]));
}
print("");
print("  DIMENSION 2 (products of the above -- traces add, so ranks add):");
{
my(d = [[s32+s11, 0, "N32 x N11"], [s32+s37, 1, "N32 x N37"],
        [s576+s37, 2, "N576 x N37"], [s37+s389, 3, "N37 x N389"],
        [s389+s5077, 5, "N389 x N5077"]]);
for(i = 1, #d,
  printf("    true rank %d  %-14s : r_est = %5.2f   (error %+5.2f)\n",
         d[i][2], d[i][3], 1.0 - d[i][1]/L, 1.0 - d[i][1]/L - d[i][2]));
}
print("");

\\ ================================================================ Section 3
print("=== 3. the objects of interest ===");
{
my(sP = mnV(apP, plist), sX = mnV(apX, plist));
printf("    dim 1  E  (rank 1, PROVED in E037) : r_est = %5.2f   <- the control\n",
       0.5 - s576/L);
printf("    dim 2  Prym P                      : r_est = %5.2f\n", 1.0 - sP/L);
printf("    dim 3  Jac(C_4)                    : r_est = %5.2f\n", 1.5 - sX/L);
print("");
printf("    internal consistency S(X)-S(E)-S(P) = %.10f  (exactly 0 by a_p(X)=a_p(E)+a_p(P))\n",
       sX - s576 - sP);
  check(abs(sX - s576 - sP) < 10^(-9), "E038(d): S(X) = S(E) + S(P) identically");
  check(abs(0.5 - s576/L - 1.0) < 0.15, "E038(c): the control curve E, of PROVED rank 1, estimates to 1.0 +- 0.15 -- FLOATING POINT, heuristic");
  check(1.0 - sP/L > 2.0, "E038(d),(e): the Mestre-Nagao estimate for rank P is above 2, so classical Chabauty is unavailable -- [P], NOT a proof");
print("");
print("=== VERDICT ===");
printf("    [P] rank P(Q) is about %.1f, so rank Jac(C_4)(Q) is about %.1f.\n",
       1.0 - sP/L, 1.5 - sX/L);
print("    Classical Chabauty needs rank Jac < g = 3, i.e. rank P <= 1.");
print("    The estimate is well above that, and the control (E, true rank 1)");
print("    comes out right, so:");
print("");
print("    [P] CLASSICAL CHABAUTY IS NOT AVAILABLE AT q = 4.");
print("    The effective method has to be quadratic Chabauty for plane quartics,");
print("    on the canonical model of E037.  This is EVIDENCE, NOT PROOF: a");
print("    Mestre-Nagao sum is a heuristic, the calibration errors above are of");
print("    size ~0.4, and no descent has been carried out.");
}

printf("\nE038 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
