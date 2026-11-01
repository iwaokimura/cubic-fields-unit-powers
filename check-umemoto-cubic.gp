\\ check-umemoto-cubic.gp --- E026 (e): Umemoto's observation of 2026-08-12.
\\
\\ NOTATION POLICY (author's decision, 2026-08-12).  The sequel keeps the notation
\\ of paper 1 -- (A,B) as in its Theorem 5.1, the branch formulas (5.1), the sequences
\\ l_k, f_k with l_k + f_k*sqrt(3) = (2+sqrt(3))^k, and eta_b, eta_0 as in the Setup
\\ -- and does not adopt the notation of the source of an observation.  Everything
\\ below is therefore stated in paper 1's symbols.
\\
\\ THE OBSERVATION (as communicated by the author, in our notation).  For a b at
\\ which eta_b is NOT the fundamental unit, the fundamental unit of K_b is a root of
\\ a cubic equation whose coefficients are given by Fibonacci-Lucas type sequences
\\ built from the solutions of the Pell equation D^2 - 3E^2 = 1.
\\
\\ WHAT IT IS.  This is the unit v of thm:iff.  That theorem says eta_b is a square
\\ in O_K^* iff (I) B^2-2A = 3(b^2+b+1), (II) A^2-2B = 3(b+1) is solvable, and its
\\ proof produces v with eta_b = v^2 and minimal polynomial X^3-BX^2+AX-1, the pairs
\\ (A,B) being parametrised by the Pell equation.  With (D,E) = (l_k,f_k), where
\\ l_k + f_k*sqrt(3) = (2+sqrt(3))^k, and signs s, sg = +-1 (eq:branch):
\\
\\      A = 1 + s*l_k ,
\\      B = 2A^2 - 3 - 3*sg*f_k*(A+1)  =  (A^2 - 3b - 3)/2 ,
\\      b = 1 - A^2 + 2*sg*f_k*(A+1) .
\\
\\ Purely in the sequences (using l_k^2 = 3f_k^2+1, 6f_k^2 = l_{2k}-1, 2f_k l_k = f_{2k}):
\\
\\      B = l_{2k} + 4 s l_k - 6 sg f_k - 3 s sg f_k l_k ,
\\      b = -(l_{2k}-1)/2 - 1 - 2 s l_k + 4 sg f_k + s sg f_{2k} .
\\
\\ So the observation is the assertion that v IS the fundamental unit, i.e. that
\\ n(b) = 2, i.e. that 4 | n(b) and 6 | n(b) both fail.  By check-composite-q.gp
\\ that happens exactly for b = -3, 5, 9, 96, -75 in the range searched, and by
\\ check-composite-genus.sage (g(C_4) = 3, g(C_6) = 10, Faltings) for at most
\\ finitely many b in total.
\\
\\ WHAT IS CHECKED HERE, for k <= KMAX and all four sign branches:
\\   (1) the two closed forms above, and B = (A^2-3b-3)/2, hold over Z;
\\   (2) X^3-BX^2+AX-1 is irreducible with a unique real root v, and v^2 = eta_b;
\\   (3) the b produced are exactly the b_pm(k) = (f_{2k-1}-1)/2 +- 2 f_{k-1} of
\\       thm:closed (as sets, both signs of b);
\\   (4) v = eta_0^m with m from bnfisunit:  m = 1 confirms the observation.
\\ NB k = 0 is included: (D,E) = (1,0) gives b = -3, the E = 0 degenerate branch.
\\
\\ CAUTION.  Step (4) uses bnfinit, hence GRH for the class group.  The
\\ GRH-free route to the same conclusion is check-composite-q.gp, whose sieve is a
\\ finite exact computation; this script is the direct confirmation.
\\ Note also that working with X^3-BX^2+AX-1 (coefficients of size |b|) instead of
\\ f_b = x^3-3bx-b^3 (coefficients of size |b|^3) makes bnfinit dramatically
\\ cheaper: k <= 8, i.e. |b| up to 7.6*10^8, runs in well under a second.
\\
\\ Usage:  gp -q check-umemoto-cubic.gp        (about a second)

default(realprecision, 60);
\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

KMAX = 8;

\\ (l_k, f_k) with l_k + f_k*sqrt3 = (2+sqrt3)^k
lf(k) = my(L=1, F=0); for(i=1,k, my(L2 = 2*L+3*F, F2 = L+2*F); L=L2; F=F2); [L,F];
\\ f_n:  f_0=0, f_1=1, f_{n+1} = 4 f_n - f_{n-1}
fs(n) = my(a=0,b=1); if(n==0, return(0)); if(n<0, return(-fs(-n))); for(i=2,n, my(c=4*b-a); a=b; b=c); b;

print("### Umemoto's cubic X^3-BX^2+AX-1: is its real root the fundamental unit? ###");
print("   k   s  sg |  b              A         B        | v^2=eta_b | closed | m (v=eta_0^m)");
{
my(nfail = 0, nexc = 0, ntest = 0, exc = List());
for(k = 0, KMAX,
  my(w = lf(k), L = w[1], F = w[2], w2 = lf(2*k), L2 = w2[1], F2 = w2[2]);
  for(si = 1, 2, for(sgi = 1, 2,
    my(s = if(si==1,1,-1), sg = if(sgi==1,1,-1));
    my(A = 1 + s*L);
    my(B = 2*A^2 - 3 - 3*sg*F*(A+1));
    my(b = 1 - A^2 + 2*sg*F*(A+1));
    if(b == 0 || b == 1, next);
    ntest++;
    \\ (1) the closed forms
    my(Bcl = L2 + 4*s*L - 6*sg*F - 3*s*sg*F*L);
    my(bcl = -(L2-1)/2 - 1 - 2*s*L + 4*sg*F + s*sg*F2);
    my(clos = (B == Bcl) && (b == bcl) && (2*B == A^2 - 3*b - 3));
    \\ (2) the cubic and its real root
    my(g = x^3 - B*x^2 + A*x - 1);
    my(irr = polisirreducible(g), rr = polrootsreal(g));
    my(v = if(#rr == 1, rr[1], 0));
    my(f = x^3 - 3*b*x - b^3);
    my(et = 1/((b+1) - polrootsreal(f)[1]));
    my(sq = (#rr == 1) && (v > 1) && abs(v^2 - et) < 10^(-20)*abs(et));
    \\ (4) is v the fundamental unit?
    my(K = bnfinit(g, 1));
    my(m = abs(centerlift(bnfisunit(K, Mod(x, g))[1])));
    if(!clos || !irr || !sq, nfail++);
    if(m != 1, nexc++; listput(exc, [b, m]));
    print("   ", k, "   ", s, "  ", sg, " | ", b, "\t", A, "\t", B, "\t| ",
          if(sq, "ok", "FAIL"), "\t| ", if(clos && irr, "ok", "FAIL"), "\t| ", m,
          if(m == 1, "   <-- fundamental",
             concat("   <-- EXCEPTION: eta_b = eta_0^", 2*m)));
  ));
);
print("");
print("  branches tested (k <= ", KMAX, "): ", ntest, ";  failures of (1),(2): ", nfail);
check(nfail == 0, "E026(e): over the 31 non-degenerate branches k<=8 the closed forms hold, X^3-BX^2+AX-1 is irreducible and v^2 = eta_b");
print("  branches with m > 1 (Umemoto's observation fails): ", nexc, "  [b, m] = ", Vec(exc));
check(Set(Vec(exc)) == Set([[-3,4],[5,2],[9,3],[-75,2],[96,2]]), "E026(e): Umemoto observation fails exactly at b = -3,5,9,-75,96 -- ASSUMES GRH (bnfinit, no bnfcertify)");
print("  i.e. eta_b = eta_0^{2m} there.  All have |b| <= 96; every branch with");
print("  k >= 4 gives m = 1.");
}

print("");
print("### cross-check with thm:closed:  b_pm(k) = (f_{2k-1}-1)/2 +- 2 f_{k-1} ###");
{
my(bad = 0);
for(k = 1, KMAX,
  my(bp = (fs(2*k-1)-1)/2 + 2*fs(k-1), bm = (fs(2*k-1)-1)/2 - 2*fs(k-1));
  my(w = lf(k), L = w[1], F = w[2], S = List());
  for(si = 1, 2, for(sgi = 1, 2,
    my(s = if(si==1,1,-1), sg = if(sgi==1,1,-1));
    listput(S, 1 - (1+s*L)^2 + 2*sg*F*(2+s*L));
  ));
  my(SS = Set(Vec(S)), ok = setsearch(SS, bp) && setsearch(SS, bm));
  if(!ok, bad++);
  print("  k = ", k, "   thm:closed: {", bm, ", ", bp, "}   branches: ", Vec(SS),
        "   ", if(ok, "ok", "MISMATCH"));
);
print("  mismatches: ", bad);
check(bad == 0, "E026(e): the branch values agree with thm:closed b_pm(k) for k<=KMAX");
}
printf("\nE026 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);

quit
