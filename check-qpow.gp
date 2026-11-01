\\ check-qpow.gp --- E022: is eta_b ever a q-th power of a unit, for q = 7, 11, 13?
\\
\\ E021 settled q=5 by eliminating b from Newton's identities and searching the
\\ resulting plane curve completely for |b| <= 10^12.  This script does three things.
\\
\\  (A) It makes the whole construction UNIFORM in q, in the raw coordinates (A,B)
\\      instead of (al,be) = (A/3,B/3), so that the same code runs for every prime q.
\\      If eta_b = e^q with e>1 a unit then N(e)=1 and e has minimal polynomial
\\      X^3-BX^2+AX-1 with A,B in Z; the minimal polynomial of eta_b is
\\      X^3-PX^2+QX-1 with P=3(b^2+b+1), Q=3(b+1).  Newton's identities give
\\           p_q(A,B) = P,      p_q(B,A) = Q,
\\      where p_q(A,B) is the sum of the q-th powers of the roots of X^3-BX^2+AX-1
\\      (so p_q(B,A) is the same for the inverse roots, whose minimal polynomial is
\\      X^3-AX^2+BX-1).  Eliminating b through Q^2-3Q+9 = 3P leaves the plane curve
\\           C_q :  p_q(B,A)^2 - 3 p_q(B,A) + 9 - 3 p_q(A,B) = 0,     b = p_q(B,A)/3 - 1.
\\      For q=5 one has C_5(3al,3be) = 9 * (the curve of check-q5.gp), verified in (2).
\\
\\  (B) It shows that the mod-3 step of E021 -- "the system forces A = B = 0 mod 3" --
\\      is NOT uniform in q.  Since p_q is a Z-polynomial, only (A,B) mod 3 matters,
\\      so the 9 residue classes can be checked exhaustively.  The step holds for every
\\      prime 5 <= q <= 200 EXCEPT q = 13, where 5 of the 9 classes survive.  The
\\      reason is structural: the roots lie in F_27 when 3 is inert, |F_27^*| = 26 =
\\      2*13, and for q = 13 every root satisfies e^13 = +-1.  And q = 13 is exactly
\\      the exponent realised by the sporadic b = 3, where eta_3 = rho^13 with rho the
\\      plastic number: (A,B) = (-1,0) there, which is (2,0) mod 3.
\\
\\  (C) It searches C_q completely along the A-axis rather than the B-axis.  Since
\\      A = 2e^{1/2}cos(phi) + e^{-1} one has |A| <= 2e^{1/2}+1, whereas B is of the
\\      size of e itself; and deg_B C_q = q while deg_A C_q = 2q.  Iterating over A is
\\      therefore both shorter and of lower degree: for q=5 and |b| <= 10^12 it needs
\\      387 values of A and quintics, against 30020 values of be and degree-10
\\      polynomials in E021.  This reaches |b| <= 10^30 for every q in {5,7,11,13}.
\\      The q=5 run reproduces E021 along a different axis, and the q=13 run finds
\\      b=3 -- the two calibrations of the code.
\\
\\ The one numerical step here is polrootsreal in (4).  check-qpow-sieve.gp re-proves
\\ the same conclusion with NO floating-point arithmetic, by an exact modular sieve on
\\ A followed by exact factorisation of the survivors; the two searches agree.

default(realprecision, 200);

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

\\ ---------------------------------------------------------------- (0) machinery

\\ p_q(A,B) in the formal variables A,B: power sum of the roots of X^3-BX^2+AX-1,
\\ i.e. e1=B, e2=A, e3=1 and p_k = e1 p_{k-1} - e2 p_{k-2} + e3 p_{k-3}.
pq(q) =
{
  my(v = vector(q+1));
  v[1] = 3; v[2] = B; if(q >= 2, v[3] = B^2 - 2*A);
  for(k = 3, q, v[k+1] = B*v[k] - A*v[k-1] + v[k-2]);
  v[q+1];
}
swapAB(f) = substvec(f, [A,B], [B,A]);
curve(q) = my(PB = swapAB(pq(q))); PB^2 - 3*PB + 9 - 3*pq(q);

print("### (0) sanity: p_q(A,B) = e_1(e^q) and p_q(B,A) = e_2(e^q) ###");
{
foreach([2,3,5,7,11,13], q,
  my(PA = pq(q), PB = swapAB(pq(q)), bad = 0, cnt = 0);
  for(nA = -6, 6, for(nB = -6, 6,
    my(f = x^3 - nB*x^2 + nA*x - 1, g);
    if(polisirreducible(f),
      cnt++;
      g = minpoly(Mod(x,f)^q);
      if(polcoef(g,2) != -substvec(PA,[A,B],[nA,nB]) ||
         polcoef(g,1) !=  substvec(PB,[A,B],[nA,nB]) ||
         polcoef(g,0) != -1, bad++; print("   FAIL q=",q," A=",nA," B=",nB)))));
  print("  q=",q,"   irreducible (A,B) with |A|,|B|<=6 tested: ",cnt,"   failures: ",bad);
  check(bad == 0, Str("E022: p_q against minpoly, |A|,|B|<=6, q=", q)));
}

\\ ------------------------------------------------- (1) the mod-3 step is not uniform

\\ Both P and Q are divisible by 3 for every b, so a residue class (A,B) mod 3 is
\\ admissible exactly when 3 | p_q(A,B) and 3 | p_q(B,A).  This is a complete test.
admis(q) =
{
  my(PA = pq(q), PB = swapAB(pq(q)), S = List());
  for(ra = 0, 2, for(rb = 0, 2,
    if(substvec(PA,[A,B],[ra,rb]) % 3 == 0 && substvec(PB,[A,B],[ra,rb]) % 3 == 0,
       listput(S, [ra,rb]))));
  Vec(S);
}

badq(qmax) = my(L = List()); forprime(q = 5, qmax, if(#admis(q) > 1, listput(L, q))); Vec(L);

print();
print("### (1) mod 3: for which q does the system force (A,B) = (0,0) mod 3 ? ###");
print("    p_q is a Z-polynomial, so only (A,B) mod 3 matters: 9 classes, exhaustive.");
foreach([5,7,11,13,17,19,23], q, print("  q=",q,"   admissible (A,B) mod 3: ",admis(q)));
print("  primes 5 <= q <= 200 where (0,0) is NOT forced: ", badq(200), "   [T: exhaustive]");
check(badq(200) == [13], "E022(a): q=13 is the ONLY prime 5<=q<=200 for which mod 3 does not force (A,B)=(0,0)");
print("  reason: if 3 is inert the roots lie in F_27^* of order 26 = 2*13, so for");
print("  q = 13 every root satisfies e^13 = +-1 and p_13 degenerates.  13 is the only");
print("  odd prime dividing 26, and q=3 is excluded separately (lem:towernocube).");
print("  the sporadic b=3 realises exactly q=13:  eta_3 = rho^13, rho the plastic");
print("  number, min poly X^3-X-1, so (A,B) = (-1,0) = (2,0) mod 3.");
print("   check: p_13(A,B) at (-1,0) = ",substvec(pq(13),[A,B],[-1,0])," = P = 3(9+3+1) = ",3*13);
print("          p_13(B,A) at (-1,0) = ",substvec(swapAB(pq(13)),[A,B],[-1,0])," = Q = 3(3+1) = ",12);
print("          C_13(-1,0) = ",substvec(curve(13),[A,B],[-1,0]),"  (expect 0)");
check(substvec(curve(13),[A,B],[-1,0]) == 0 && substvec(pq(13),[A,B],[-1,0]) == 39 && substvec(swapAB(pq(13)),[A,B],[-1,0]) == 12, "E022(a): (A,B)=(-1,0) lies on C_13 with P=39, Q=12, i.e. b=3");

\\ ------------------------------------------------------------- (2) the curves C_q

print();
print("### (2) the curve C_q: degrees, irreducibility, and the Thue test ###");
{
foreach([3,5,7,11,13], q,
  my(C = curve(q), F = factor(C));
  print("  q=",q,"   total degree ",poldegree(C,A),"   deg_A = ",poldegree(C,A),
        "   deg_B = ",poldegree(C,B),"   irreducible factors over Q: ",matsize(F)[1]);
  for(i = 1, matsize(F)[1],
    print("        factor ",i," (mult ",F[i,2],"): deg_A = ",poldegree(F[i,1],A),
  check(matsize(F)[1] == 1 && F[1,2] == 1 && poldegree(C,A) == 2*q && poldegree(C,B) == q, Str("E022(b): C_q irreducible over Q with deg_A = 2q, deg_B = q, q=", q));
          ", deg_B = ",poldegree(F[i,1],B))));
print("  p_q(B,A) is weighted-homogeneous of weight q in (e1,e2,e3)=(A,B,1), so its");
print("  monomials A^i B^j have i+2j <= q and its top TOTAL-degree part is A^q alone.");
print("  Hence the top-degree form of C_q is A^{2q} for EVERY q: a single point at");
print("  infinity [0:1:0] of multiplicity 2q.  A Thue equation F(x,y)=m needs a");
print("  squarefree leading form with >= 3 distinct roots, so:");
print("  [T] THE THUE ROUTE IS CLOSED FOR EVERY PRIME q >= 5, not only for q = 5.");
foreach([3,5,7,11,13], q,
  my(C = curve(q), d = poldegree(C,A), top = 0);
  \\ extract the total-degree-d part
  for(i = 0, d, for(j = 0, poldegree(C,B),
    if(i+j == d, top += polcoef(polcoef(C,j,B),i,A) * A^i * B^j)));
  print("   q=",q,"   top-degree form = ",top);
  \\ this check used to sit OUTSIDE the foreach (the loop closed on the line
  \\ above), where q reverts to a symbol: A^(2*q) then throws "irrational
  \\ exponent", the statement aborted, and the gate never counted it.  Found
  \\ in the 2026-08-22 full verification run (E124); the printed forms had
  \\ been correct all along, but unasserted.
  check(top == A^(2*q), Str("E022(b): the top-degree form of C_q is A^{2q}, q=", q)));
print("  NOTE the q=3 entry: C_3 is an irreducible degree-6 curve whose top form is");
print("  also A^6, so the Thue equation of lem:towernocube does NOT come from the");
print("  elimination itself.  It comes from the EXTRA gcd step available at q=3");
print("  (al = a_1 d, ga = g d, then a_1^2 | g^3 forces a_1 = +-1 and only then is the");
print("  equation homogeneous).  That step has no analogue for q >= 5.");
}

print();
print("### (2b) cross-check against E021: C_5(3al,3be) = 9 * (curve of check-q5.gp) ###");
{
my(u5, v5);
u5 = 81*al^5 - 135*al^3*be + 45*al*be^2 + 15*al^2 - 5*be;
v5 = 81*be^5 - 135*al*be^3 + 45*al^2*be + 15*be^2 - 5*al;
print("  identity holds ? ", substvec(curve(5),[A,B],[3*al,3*be]) == 9*(u5^2 - u5 + 1 - v5));
check(substvec(curve(5),[A,B],[3*al,3*be]) == 9*(u5^2 - u5 + 1 - v5), "E022(2b): C_5(3al,3be) = 9 * (the curve of check-q5.gp)");
}

\\ ----------------------------------------------- (3) no congruence obstruction, q=7,11

print();
print("### (3) congruence obstructions for q = 7, 11, 13 (as in E021 for q=5) ###");
print("    by CRT it suffices to test prime powers; 'sol' = the system is solvable mod m");
solvable(q, m, restrict3) =
{
  my(PA = pq(q), PB = swapAB(pq(q)), hit = vectorsmall(m*m), X, Y, ok = 0);
  for(nA = 0, m-1, for(nB = 0, m-1,
    X = substvec(PA,[A,B],[nA,nB]) % m; Y = substvec(PB,[A,B],[nA,nB]) % m;
    hit[X*m + Y + 1] = 1));
  for(b = 0, m-1,
    if(!(restrict3 && b % 3 == 0),
      X = (3*(b^2+b+1)) % m; Y = (3*(b+1)) % m;
      if(hit[X*m + Y + 1], ok = 1; break)));
  ok;
}
{
my(L = [2,4,8,16,32,64, 3,9,27,81, 5,25,125, 7,49, 11,121, 13,169,
        17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]);
foreach([7,11,13], q,
  my(obst = List(), o3 = List());
  for(i = 1, #L, my(m = L[i]);
    if(!solvable(q, m, 0), listput(obst, m));
    if(m % 3 == 0 && !solvable(q, m, 1), listput(o3, m)));
  print("  q=",q,"   prime powers <= 97 with NO solution: ",Vec(obst),
        "   ... and none with 3 nmid b imposed: ",Vec(o3));
  check(#obst == 0 && #o3 == 0,
        Str("E022(c): the system is solvable modulo every prime power <= 97 tested, q=", q)));
print("  => NO local obstruction for q = 7, 11, 13 either: no congruence proof exists.");
}

\\ --------------------------------------------------------- (4) the complete A-search

\\ If eta_b = e^q with e>1 a unit, the conjugates of e are e and sigma,sigmabar with
\\ |sigma|^2 = 1/e, so A = e_2(e) = 2 e^{1/2} cos(phi) + e^{-1} and |A| <= 2e^{1/2}+1.
\\ Also e = eta_b^{1/q} and eta_b < P+1 = 3b^2+3b+4 <= 4b^2 for b >= 4 or b <= -1
\\ (lem:etasize), so |b| <= BT forces |A| <= 2(4 BT^2)^{1/(2q)} + 1 =: AMAX.
\\ For each admissible A in [-AMAX,AMAX] we solve C_q(A,.) -- degree exactly q in B,
\\ leading coefficient -3 -- with polrootsreal, which returns ALL real roots, and test
\\ the nearest three integers exactly over Z.  The search is therefore complete.
search(q, BT) =
{
  my(PB = swapAB(pq(q)), C = curve(q), AMAX, RA, hits = List(), cnt = 0,
     t0 = getabstime());
  \\ EXACT bound, no floating point: sqrtnint(x,n) = floor(x^{1/n}) exactly, so
  \\ (4BT^2)^{1/(2q)} < R+1 and the true bound 2(4BT^2)^{1/(2q)}+1 is < 2R+3.
  AMAX = 2*sqrtnint(4*BT^2, 2*q) + 3;
  RA = Set(vector(#admis(q), i, admis(q)[i][1]));
  for(nA = -AMAX, AMAX,
    if(!setsearch(RA, nA % 3), next);
    cnt++;
    my(F = subst(C, A, nA), R = polrootsreal(F));
    for(j = 1, #R,
      my(r = round(R[j]));
      for(d = -1, 1,
        my(nB = r + d, uu);
        if(substvec(C,[A,B],[nA,nB]) == 0,
           uu = substvec(PB,[A,B],[nA,nB]);
           if(uu % 3 == 0,
              hits = Set(concat(Vec(hits), [[nA, nB, uu/3 - 1]])))))));
  [Vec(hits), AMAX, cnt, strtime(getabstime()-t0)];
}

print();
print("### (4) COMPLETE search on C_q for |b| <= 10^30, q = 5, 7, 11, 13 ###");
BTARGET = 10^30;
{
foreach([5,7,11,13], q,
  my(S = search(q, BTARGET), H = S[1]);
  print("  q=",q,"   AMAX=",S[2],"   A-values scanned: ",S[3],
        "   deg_B C_q = ",q,"   time ",S[4]);
  print("        integral points on C_q with |A| <= AMAX: ",#H);
  check(Set(vector(#H, i, [H[i][1], H[i][2]])) == if(q == 13, Set([[3,3],[-1,0]]), Set([[3,3]])), Str("E022(d): the only integral points of C_q with |A| <= AMAX(10^30) are (3,3), and (-1,0) for q=13; q=", q));
  for(i = 1, #H,
    my(nA = H[i][1], nB = H[i][2], b = H[i][3], f = x^3 - nB*x^2 + nA*x - 1, irr);
    irr = polisirreducible(f);
    print("         (A,B)=(",nA,",",nB,")   b = ",b,"   X^3-BX^2+AX-1 = ",f,
          "   irreducible: ",irr);
    if(irr && b != 0 && b != 1,
      my(g = x^3-3*b*x-b^3, K, n, e);
      e = polrootsreal(f)[1];
      K = bnfinit(g,1);
      n = abs(lift(bnfisunit(K, 1/((b+1)-Mod(x,g)))[1]));
      print("           e = ",e,"   eta_b = eta_0^n with n = ",n,
            "   q | n ? ",n % q == 0,"   bnfcertify = ",bnfcertify(K));
      check(n % q == 0 && bnfcertify(K) == 1,
            Str("E022(d): the nondegenerate point of C_q gives q | n, certified without GRH, q=", q)))));
}

print();
print("### (5) the values |b| <= 3, where eta_b < 4b^2 is not available ###");
{
foreach([-3,-2,-1,2,3], b,
  my(f = x^3-3*b*x-b^3, K = bnfinit(f,1), n);
  n = abs(lift(bnfisunit(K, 1/((b+1)-Mod(x,f)))[1]));
  print("  b=",b,"   eta_b = eta_0^n, n = ",n,
        "   divisible by 5,7,11,13 ? ",[n%5==0, n%7==0, n%11==0, n%13==0]));
}

print();
print("### CONCLUSION ###");
print("  [T]  the Thue route is closed for every prime q >= 5 (top form A^{2q}).");
print("  [T]  mod 3 forces (A,B)=(0,0) for every prime 5<=q<=200 except q=13;");
print("       q=13 is the exponent of the sporadic b=3, and 13 | |F_27^*| = 26.");
print("  [T]  no congruence obstruction exists for q = 7, 11, 13.");
print("  [E: |b| <= 10^30]  for q = 5, 7, 11 the only integral point of C_q in range is");
print("       the degenerate (A,B)=(3,3), where X^3-3X^2+3X-1=(X-1)^3, e=1 and b=0;");
print("       for q = 13 the only further point is (A,B)=(-1,0), i.e. b=3.");
print("       Together with |b| <= 3 in (5): eta_b is a q-th power for no b with");
print("       4 <= |b| <= 10^30 and q in {5,7,11,13}, and among |b| <= 3 only for");
print("       b = 3 with q = 13.");

printf("\nE022 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
