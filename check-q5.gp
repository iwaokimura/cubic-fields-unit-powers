\\ check-q5.gp --- E021: is eta_b ever a FIFTH power of a unit?
\\
\\ Setup (exactly as for q=3 in lem:towernocube).  If eta_b = u^5 with u>1 a unit,
\\ then N(u)=1 and u has minimal polynomial X^3-B X^2+A X-1 with A,B in Z.  The
\\ minimal polynomial of eta_b is X^3-P X^2+Q X-1 with P=3(b^2+b+1), Q=3(b+1).
\\ Newton's identities give, with p5(A,B) = B^5-5AB^3+5A^2B+5B^2-5A:
\\      (I)   p5(A,B) = P = 3(b^2+b+1)          [ = e_1(u^5) ]
\\      (II)  p5(B,A) = Q = 3(b+1)              [ = e_2(u^5) ]
\\ (e_2(u^5) is e_1 of the fifth powers of the inverse roots, whose minimal
\\ polynomial is X^3-A X^2+B X-1, i.e. p5 with A and B interchanged.)

default(realprecision, 40);

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

p5(A, B) = B^5 - 5*A*B^3 + 5*A^2*B + 5*B^2 - 5*A;

print("### (0) sanity: p5 really is e_1(u^5), and its swap is e_2(u^5) ###");
{
my(bad = 0, cnt = 0);
for(A = -6, 6, for(B = -6, 6,
  my(f = x^3 - B*x^2 + A*x - 1, g);
  if(polisirreducible(f) && poldisc(f) < 0,
    cnt++;
    g = minpoly(Mod(x,f)^5);
    if(polcoef(g,2) != -p5(A,B) || polcoef(g,1) != p5(B,A) || polcoef(g,0) != -1,
       bad++; print("  FAIL A=",A," B=",B,"  minpoly(u^5)=",g)))));
print("  complex cubic (A,B) with |A|,|B|<=6 tested: ", cnt, "   failures: ", bad);
check(bad == 0, "E021: p_5 = e_1(u^5) and its swap = e_2(u^5), 84 complex cubic (A,B), |A|,|B|<=6");
}

print();
print("### (1) modulo 3 the system forces A = B = 0 mod 3 ###");
{
my(sol = []);
for(A = 0, 2, for(B = 0, 2,
  my(ok = 0);
  for(b = 0, 2, if((p5(A,B) - 3*(b^2+b+1)) % 3 == 0 && (p5(B,A) - 3*(b+1)) % 3 == 0, ok = 1));
  if(ok, sol = concat(sol, [[A,B]]))));
print("  (A,B) mod 3 admitting some b mod 3: ", sol);
check(sol == [[0,0]], "E021(a): (0,0) is the only admissible class mod 3");
}

print();
print("### (2) congruence obstruction search over prime powers m ###");
print("    (by CRT it suffices to test prime powers; 'sol' = solvable mod m)");
solvable(m, restrict3) =
{
  my(hit = vectorsmall(m*m), X, Y, ok = 0);
  for(A = 0, m-1, for(B = 0, m-1,
    X = p5(A,B) % m; Y = p5(B,A) % m;
    hit[X*m + Y + 1] = 1));
  for(b = 0, m-1,
    if(!(restrict3 && b % 3 == 0),
      X = (3*(b^2+b+1)) % m; Y = (3*(b+1)) % m;
      if(hit[X*m + Y + 1], ok = 1; break)));
  ok;
}
{
my(L = [2,4,8,16,32,64,128, 3,9,27,81,243, 5,25,125, 7,49,343, 11,121, 13,169,
        17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,
        109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]);
for(i = 1, #L, my(m = L[i], s = solvable(m, 0));
  if(!s, print("  *** OBSTRUCTION at m = ", m, " ***")));
print("  prime powers with NO solution (unrestricted b): none unless printed above");
for(i = 1, #L, my(m = L[i]);
  if(m % 3 == 0, my(s = solvable(m, 1));
    print("  m = ", m, "  solvable with 3 nmid b ? ", s)));
}

print();
print("### (3) elimination: the plane curve C ###");
print("    A=3al, B=3be forces (Newton):  b+1 = u(al,be),  b^2+b+1 = v(al,be),");
print("    u = 81al^5-135al^3be+45al*be^2+15al^2-5be,");
print("    v = 81be^5-135al*be^3+45al^2be+15be^2-5al,");
print("    so C: u^2-u+1-v = 0, equivalently (2u-1)^2 = 4v-3.");
u5 = 81*al^5 - 135*al^3*be + 45*al*be^2 + 15*al^2 - 5*be;
v5 = 81*be^5 - 135*al*be^3 + 45*al^2*be + 15*be^2 - 5*al;
{
my(C = u5^2 - u5 + 1 - v5, F);
print("  deg_al C = ", poldegree(C, al), "   deg_be C = ", poldegree(C, be),
      "   total degree 10");
F = factor(C);
print("  number of irreducible factors over Q: ", matsize(F)[1]);
check(polcoef(polcoef(C, 10, al), 0, be) == 6561, "E021(c): the top-degree form of C is 6561*al^10");
check(poldegree(C, al) == 10 && poldegree(C, be) == 5, "E021(c): deg_al C = 10, deg_be C = 5");
check(matsize(F)[1] == 1 && F[1,2] == 1, "E021(c): C is irreducible over Q");
for(i = 1, matsize(F)[1],
  print("   factor ", i, " (multiplicity ", F[i,2], "):  deg_al = ",
        poldegree(F[i,1], al), ", deg_be = ", poldegree(F[i,1], be)));
print("  the top-degree form of C (deg(al)=deg(be)=1) is 6561*al^10: one single");
print("  point at infinity, [0:1:0].  A Thue equation F(x,y)=m needs a squarefree");
print("  leading form with at least 3 distinct roots, so C is NOT of Thue type.");
print("  in the RELEVANT asymptotic region be ~ al^2 the balance is governed by");
print("   (81*al^5-135al^3be+45al be^2)  ==  9*al*(9al^4-15al^2be+5be^2) ? ",
      81*al^5-135*al^3*be+45*al*be^2 == 9*al*(9*al^4-15*al^2*be+5*be^2));
print("   9al^4-15al^2be+5be^2 irreducible over Q ? ",
      polisirreducible(subst(9*al^4-15*al^2*be+5*be^2, be, y)),
      "   disc_be = 45al^4, so it splits over Q(sqrt5)");
}

print();
print("### (4) the size window: |A| <= 2 sqrt(B) + ... and the angle condition ###");
print("    u=eta_0>1, |sigma|=u^{-1/2}: B = u+2u^{-1/2}cos(phi), A = 2u^{1/2}cos(phi)+u^{-1},");
print("    so |B-u| <= 2u^{-1/2} and |A| <= 2 u^{1/2}+u^{-1}.");
print("    With c = al/sqrt(be): the leading balance forces 9c^5-15c^3+5c = +-1,");
print("    i.e. (with c = (2/sqrt3) sin(theta)) sin(5theta) = +- sqrt3/2:");
{
print("   real roots of 9c^5-15c^3+5c-1: ", polrootsreal(9*c^5-15*c^3+5*c-1));
print("   real roots of 9c^5-15c^3+5c+1: ", polrootsreal(9*c^5-15*c^3+5*c+1));
print("   all lie in [-2/sqrt3, 2/sqrt3] = [", -2/sqrt(3), ", ", 2/sqrt(3), "]");
}

print();
print("### (5) COMPLETE search for integral points on C, and the range it covers ###");
print("    If eta_b = u^5 then |B-u| <= 2u^{-1/2} < 2, so 3be = B < u+2 = eta_b^{1/5}+2.");
print("    For |b| >= 4 one has eta_b < P+1 = 3b^2+3b+4 <= 4b^2, so |b| <= 10^12 forces");
print("    u < (4*10^24)^{1/5} = 83255.4 and hence be <= 27752 < BEMAX.  For each be we");
print("    solve the degree-10 polynomial C(.,be) with polrootsreal (which finds ALL real");
print("    roots) and test each rounded root exactly over Z, so the search is complete.");
BEMAX = 30000;
{
default(realprecision, 200);
my(hits = 0, tested = 0, F, R, a0, uu, vv, sols = Set([]));
for(n = -20, BEMAX,
  F = subst(u5^2 - u5 + 1 - v5, be, n);
  if(poldegree(F, al) < 1, next);
  R = polrootsreal(F);
  tested++;
  for(j = 1, #R,
    a0 = round(R[j]);
    uu = subst(subst(u5, al, a0), be, n);
    vv = subst(subst(v5, al, a0), be, n);
    if(uu^2 - uu + 1 == vv, hits++; sols = setunion(sols, Set([[a0, n]]));
      print("   SOLUTION  al=", a0, "  be=", n, "  b=", uu-1,
            "   (A,B)=(", 3*a0, ",", 3*n, ")   X^3-BX^2+AX-1 = ",
            factor(x^3 - 3*n*x^2 + 3*a0*x - 1)))));
print("  be from -20 to ", BEMAX, ": ", tested, " values solved;  integral points: ", hits);
check(sols == Set([[1, 1]]), "E021(f): the degenerate (al,be)=(1,1) is the ONLY integral point of C for be in [-20,BEMAX] (hits counts real roots, and be=1 gives a multiple one)");
print("  the only one is the degenerate (al,be)=(1,1): X^3-3X^2+3X-1=(X-1)^3, u=1, b=0.");
print("  CONCLUSION [E]: eta_b is not a fifth power for any b with |b| <= 10^12.");
}
{
print("  the remaining |b| <= 3 directly (exponent n with eta_b = eta_0^n):");
for(i = 1, 5,
  my(b = [-3,-2,-1,2,3][i], f = x^3-3*b*x-b^3, K = bnfinit(f,1), n);
  n = abs(lift(bnfisunit(K, 1/((b+1)-Mod(x,f)))[1]));
  print("    b=", b, "  n=", n, "   5 | n ? ", n % 5 == 0));
}

print();
print("### (6) the cover C -> A^1_al has degree 5; its branch locus ###");
{
my(D = poldisc(u5^2 - u5 + 1 - v5, be), F);
print("  deg_al disc_be(C) = ", poldegree(D, al));
F = factor(D);
print("  irreducible factors over Q (deg, multiplicity):");
for(i = 1, matsize(F)[1],
  print("    deg ", poldegree(F[i,1], al), "   mult ", F[i,2]));
print("  => 2+4+20 = 26 distinct roots.  A Riemann-Hurwitz guess based on treating");
print("  each of these as a simple tame branch point would give g >= 9; that guess is");
print("  WRONG.  The genus of C, computed with Sage 10.7 (see check-q5-genus.sage,");
print("  three independent computations), is exactly 6.  Since 6 >= 2, Faltings'");
print("  theorem gives finitely many rational, hence finitely many integral, points on");
print("  C: only FINITELY MANY b have eta_b a fifth power (non-effectively).");
print("  The affine singular locus is finite and non-rational: the al-coordinates are");
print("  the roots of (9al^2-3al-1)(81al^4+81al^3+81al^2+21al+11), and 9al^2-3al-1 has");
print("  roots (1+-sqrt5)/6.  Sum of the delta invariants = 36-6 = 30.");
}

printf("\nE021 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
