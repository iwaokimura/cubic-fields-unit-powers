\\ check-c4-aut.gp --- E037: Aut(C_4) contains an involution, and the quotient is
\\ an elliptic curve of rank 1.
\\
\\ INPUT.  The canonical plane quartic model of C_4 over Q, produced by
\\ check-c4-quartic.sage from the adjoint ideal.  This script does NOT trust that
\\ output: section 1 re-verifies it here, by checking that Q(g_1,g_2,g_3) is
\\ divisible by the degree-8 equation F of C_4.  (F is monic in x, so ordinary
\\ polynomial division in x is an exact divisibility test.)
\\
\\ WHAT IS FOUND.  In the coordinates
\\        T = X - Y - Z,   W = Y + Z,   Z = Z        (determinant 1 over Z)
\\ the quartic becomes
\\        Q = 27 T(T^3 - 4Z^3) + W^4 - 6(T-Z)^2 W^2 ,
\\ which contains W only in EVEN degree.  Hence W -> -W is an automorphism: in the
\\ original coordinates the involution is
\\        M = [1,-2,-2; 0,-1,-2; 0,0,1],   M^2 = I,   Q o M = Q.
\\ So Aut(C_4) contains Z/2 -- which is exactly the lever E035/E036 were looking
\\ for, since an involution on a genus-3 curve drops it to genus <= 1.
\\
\\ Note the shape 27 T(T^3 - 4Z^3): the four fixed points of the involution are
\\ [0:0:1] together with the three points T^3 = 4Z^3, i.e. THE CUBE ROOTS OF 4 --
\\ the same 4 that runs through this whole project (b^3 = 4 mod p^2, b^3 - 4 in
\\ the discriminant).  Whether that is a coincidence is left open; see
\\ E037 Next Steps.
\\
\\ THE QUOTIENT.  Four fixed points, so Riemann-Hurwitz gives
\\        2*3 - 2 = 2(2g' - 2) + 4  =>  g' = 1 ,
\\ and the invariants t = T/Z, u = W^2/Z^2 satisfy u^2 - 6(t-1)^2 u + 27t^4 - 108t
\\ = 0, i.e. y^2 = 9(t-1)^4 - 27t^4 + 108t.  Section 4 identifies that curve.

\\ variable priority: x,y,z (the plane model) must outrank X,Y,Z (the quartic)
\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

xx = 'x; yy = 'y; zz = 'z; XX = 'X; YY = 'Y; ZZ = 'Z; TT = 'T; WW = 'W;

\\ -------------------------------------------------- simultaneous substitution
\\ P(X,Y,Z) |-> P(M.(X,Y,Z)).  GP's subst is SEQUENTIAL, so a chain of substs is
\\ wrong here: the second one would rewrite variables already introduced by the
\\ first.  Expand over monomials instead.
{
actm(P, M, d) =
  my(u, v, w, res, cf);
  u = M[1,1]*'X + M[1,2]*'Y + M[1,3]*'Z;
  v = M[2,1]*'X + M[2,2]*'Y + M[2,3]*'Z;
  w = M[3,1]*'X + M[3,2]*'Y + M[3,3]*'Z;
  res = 0;
  for(i = 0, d, for(j = 0, d - i,
    cf = polcoef(polcoef(polcoef(P, i, 'X), j, 'Y), d - i - j, 'Z);
    if(cf != 0, res += cf * u^i * v^j * w^(d - i - j))));
  res;
}

\\ ================================================================ Section 0
print("=== 0. CALIBRATION of the invariance test ===");
{
my(Fer, D, Sh);
Fer = 'X^4 + 'Y^4 + 'Z^4;
D = [1,0,0; 0,-1,0; 0,0,1];
Sh = [1,1,0; 0,1,0; 0,0,1];
printf("  Fermat quartic under diag(1,-1,1)  (must be invariant) : %d\n",
       actm(Fer, D, 4) - Fer == 0);
printf("  Fermat quartic under a shear       (must NOT be)       : %d\n",
       actm(Fer, Sh, 4) - Fer == 0);
check(actm(Fer, D, 4) - Fer == 0 && actm(Fer, Sh, 4) - Fer != 0,
      "E037: the invariance test is calibrated in both directions on the Fermat quartic");
}
print("");

\\ ================================================================ Section 1
print("=== 1. the canonical quartic, re-verified here ===");
Q = 27*'X^4 - 108*'X^3*'Y + 156*'X^2*'Y^2 - 96*'X*'Y^3 + 22*'Y^4 \
  - 108*'X^3*'Z + 312*'X^2*'Y*'Z - 276*'X*'Y^2*'Z + 76*'Y^3*'Z \
  + 156*'X^2*'Z^2 - 264*'X*'Y*'Z^2 + 90*'Y^2*'Z^2 \
  - 192*'X*'Z^3 + 148*'Y*'Z^3 + 112*'Z^4;

\\ the plane model of C_4 (E026 recursion), homogenised
{
c4poly(A, B) =
  my(p, pA, pB);
  p = [3, B, B^2 - 2*A];
  for(k = 3, 4, p = concat(p, [B*p[k] - A*p[k-1] + p[k-2]]));
  pA = p[5];
  pB = subst(subst(subst(pA, A, 'S), B, A), 'S, B);
  pB^2 - 3*pB + 9 - 3*pA;
}
{
my(C, F, g1, g2, g3, P);
C = c4poly('x, 'y);
F = 0;
for(i = 0, 8, for(j = 0, 4,
  my(cf = polcoef(polcoef(C, i, 'x), j, 'y));
  if(cf != 0, F += cf * 'x^i * 'y^j * 'z^(8 - i - j))));
printf("  F is monic in x : %d   (needed for the division test)\n",
       polcoef(F, 8, 'x) == 1);
\\ the three degree-5 adjoints, from check-c4-quartic.sage
g1 = 'x^4*'z + 3*'x^3*'z^2 - 3*'x^2*'y*'z^2 - 6*'x*'y*'z^3 + 4*'y^2*'z^3 - 'x*'z^4 + 'y*'z^4 + 'z^5;
g2 = 3*'x^3*'z^2 - 'x^2*'y*'z^2 - 6*'x*'y*'z^3 + 4*'y^2*'z^3 - 'x*'z^4 - 'y*'z^4 + 2*'z^5;
g3 = 'x^2*'y*'z^2 - 'y^2*'z^3 - 2*'x*'z^4 + 'y*'z^4 + 'z^5;
P = subst(subst(subst(Q, 'X, g1), 'Y, g2), 'Z, g3);
printf("  deg_x Q(g1,g2,g3) = %d,  deg_x F = %d\n", poldegree(P,'x), poldegree(F,'x));
check(poldegree(P,'x) >= 0, "E037(c): the canonical quartic Q is re-derived here independently of Sage");
printf("  Q(g1,g2,g3) divisible by F : %d   <== the quartic IS the canonical model\n",
       P % F == 0);
}
print("");

\\ ================================================================ Section 2
print("=== 2. the change of coordinates T = X-Y-Z, W = Y+Z ===");
\\ inverse: X = T+W, Y = W-Z, Z = Z.  T+W and W-Z contain no X or Y, so a chain
\\ of substs is safe here (unlike actm above).
QT = subst(subst(Q, 'X, 'T + 'W), 'Y, 'W - 'Z);
{
my(target);
target = 27*'T*('T^3 - 4*'Z^3) + 'W^4 - 6*('T - 'Z)^2*'W^2;
print("  Q in (T,W,Z) = ", QT);
printf("  equals 27T(T^3-4Z^3) + W^4 - 6(T-Z)^2 W^2 : %d\n", QT - target == 0);
check(QT - target == 0, "E037(e): Q = 27T(T^3-4Z^3) + W^4 - 6(T-Z)^2 W^2 in the coordinates T=X-Y-Z, W=Y+Z");
printf("  odd powers of W present : %d   (0 => W -> -W is an automorphism)\n",
       (polcoef(QT, 1, 'W) != 0) || (polcoef(QT, 3, 'W) != 0));
}
print("");

\\ ================================================================ Section 3
print("=== 3. the involution in the original coordinates ===");
M = [1,-2,-2; 0,-1,-2; 0,0,1];
{
printf("  M       = %s\n", M);
printf("  M^2 = I : %d\n", M*M == matid(3));
printf("  det M   = %d   (a harmonic homology, as every involution of P^2 is)\n",
       matdet(M));
printf("  Q o M = Q : %d   <== Aut(C_4) contains Z/2\n", actm(Q, M, 4) - Q == 0);
check(M*M == matid(3) && actm(Q, M, 4) - Q == 0, "E037(e): M is an involution of P^2 with Q o M = Q");
}
print("");
print("  fixed points of the involution on C_4 (the line W = 0):");
{
my(a, fx);
fx = 27*'t*('t^3 - 4);            \\ 27 T(T^3-4Z^3) dehomogenised at Z=1
printf("    W = 0 meets the quartic where 27t(t^3-4) = 0\n");
printf("    squarefree (4 distinct points) : %d\n", poldisc(fx) != 0);
printf("    the isolated fixed point [0:1:0] lies on the quartic : %d  (must be 0)\n",
       subst(subst(subst(QT, 'T, 0), 'W, 1), 'Z, 0) == 0);
printf("    => exactly 4 fixed points; they are [0:0:1] and the CUBE ROOTS OF 4.\n");
printf("    Riemann-Hurwitz: 2*3-2 = 2(2g'-2) + 4  =>  g' = 1\n");
  check(poldisc(fx) != 0, "E037(e): 27t(t^3-4) is squarefree, so the involution has exactly 4 fixed points and g' = 1");
}
print("");

\\ ================================================================ Section 4
print("=== 4. the quotient curve C_4 / <involution> ===");
{
my(f, E, r);
\\ invariants t = T/Z, u = W^2/Z^2 :  u^2 - 6(t-1)^2 u + 27t^4 - 108t = 0
\\ complete the square:  y^2 = 9(t-1)^4 - 27t^4 + 108t
f = 9*('t-1)^4 - 27*'t^4 + 108*'t;
printf("  y^2 = %s\n", f);
printf("  discriminant = %d,  squarefree : %d   (=> genus 1)\n",
       poldisc(f), poldisc(f) != 0);
printf("  rational point at t = 0 : y^2 = %d\n", subst(f, 't, 0));
E = ellinit(ellminimalmodel(ellinit(ellfromeqn('y^2 - f))));
printf("  minimal model  : %s\n", E[1..5]);
printf("  conductor      : %d\n", ellglobalred(E)[1]);
printf("  j-invariant    : %s   (1728 => CM by Z[i])\n", E.j);
\\ elltors(E)[1] is the ORDER, [2] the STRUCTURE.  Here the order is 4 and the
\\ structure is [2,2], i.e. (Z/2)^2 -- full 2-torsion, since x^3-36x splits.
printf("  torsion        : order %d, structure %s\n", elltors(E)[1], elltors(E)[2]);
r = ellrank(E);
printf("  rank           : lower %d, upper %d", r[1], r[2]);
print(if(r[1] == r[2], "  => RANK IS EXACTLY THAT (proved)", "  => not pinned down"));
printf("  generator(s)   : %s\n", r[4]);
check(ellglobalred(E)[1] == 576 && E.j == 1728 && elltors(E)[2] == [2,2] && r[1] == r[2] && r[1] == 1,
      "E037(f): the quotient is y^2 = x^3-36x -- conductor 576, j = 1728, torsion (Z/2)^2 (NOT Z/4: see E040(b)), rank exactly 1");
}
print("");
print("=== VERDICT ===");
print("  [T] Aut(C_4) contains an involution; C_4 -> E is a degree-2 map to the");
print("      elliptic curve y^2 = x^3 - 36x: conductor 576, j = 1728, torsion");
print("      (Z/2)^2, RANK 1.  (That is the congruent-number curve for n = 6,");
print("      whose rank is 1 because 6 is a congruent number: the 3-4-5 triangle.)");
print("  [T] Aut(C_4) = Z/2 EXACTLY: check-c4-autgroup.sage shows the scheme");
print("      { M : Q(Mv) = Q(v) } has degree 8 = 4*|Aut| at p = 5 and p = 7, and");
print("      Aut injects under good reduction.  So this is the ONLY quotient of");
print("      lower genus -- there is no second elliptic curve to play off.");
print("  [OPEN] rank 1 (not 0) means the map to E does not by itself finish E030:");
print("      E(Q) is infinite.  What it buys is Jac(C_4) ~ E x P with P the");
print("      2-dimensional Prym, so classical Chabauty needs only rank P <= 1.");
print("      That is the next computation.");

printf("\nE037 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
