\\ check-lucas-powers.gp --- E052: can the Bugeaud-Mignotte-Siksek machinery be
\\ pointed at OUR sequences, and would it close E033/E034?
\\
\\ THE QUESTION.  E032(a) established that the standard references on powers in
\\ Lucas sequences do not cover ours: f_n = U_n(4,1), l_n = V_n(4,1)/2, with
\\ l^2 - 3 f^2 = 1 and l_n + f_n sqrt3 = (2+sqrt3)^n.  BMS I (Annals 2006) is
\\ (P,Q) = (1,-1); Ribenboim-McDaniel needs P,Q odd; Kagawa-Terai needs 4|P,
\\ Q=-1.  The new reference is BMS II (Compositio 142 (2006) 31-62),
\\ the Lebesgue-Nagell equation x^2 + D = y^n.  Does the METHOD generalise to
\\ our sequence, and would that help?
\\
\\ WHAT THE LITERATURE ACTUALLY OFFERS (all verified, see E052):
\\   * BMS II is a different equation (x^2 + D = y^n), not our shape.  Its value
\\     here is as a template: classical (linear forms in three logarithms) +
\\     modular (Bennett-Skinner recipe for A x^n + B y^n = C z^2, level lowering)
\\     + Thue equations for small p, and the trick of using the modular side to
\\     force the variables LARGE so the log-forms bound becomes usable.
\\   * The generalisation the question asks for is published: Silliman-Vogt,
\\     "Powers in Lucas sequences via Galois representations" (arXiv:1307.5078)
\\     -- "a systematic approach towards the problem of determining all perfect
\\     powers in any particular Lucas sequence".  In their notation
\\     u_{n+2} = b u_{n+1} + c u_n, OUR sequence is (b,c) = (4,-1).
\\
\\ WHAT THIS SCRIPT CHECKS.
\\   1. the sequences and the conic (calibration against E009/E032);
\\   2. the perfect powers actually present, out to n = NMAX;
\\   3. Silliman-Vogt Theorem 2 evaluated for (b,c) = (4,-1): their general
\\      bound on the exponent p is explicit, and for us it is astronomical --
\\      which is why their Section 5 sieve, not Theorem 2, is the usable route;
\\   4. the descent our sequence gives, verified rather than asserted;
\\   5. THE POINT: the quantity E033/E034 need is NOT a perfect power.  It is
\\      kappa, the square part of an explicit cofactor, required to be below the
\\      FOURTH ROOT of that cofactor.  Section 5 measures kappa^4/W along the
\\      four families of E032(1) and shows how far the two species are apart.
\\
\\ Failure counts are printed explicitly; the run ends with a VERDICT block.

NMAX = 300;          \\ how far to walk the sequences
KMAX = 40;           \\ how far to measure kappa in section 5

\\ ------------------------------------------------------------------ the data
{
lucas(nmax) =
  my(L, F, l, f, nl, nf);
  L = vector(nmax + 1); F = vector(nmax + 1);
  l = 1; f = 0;
  for(n = 0, nmax,
    L[n + 1] = l; F[n + 1] = f;
    nl = 2*l + 3*f; nf = l + 2*f; l = nl; f = nf);
  return([L, F]);
};

\\ product of the odd primes dividing m (Silliman-Vogt's rad')
{
radodd(m) =
  my(r);
  r = 1;
  if(m == 0, return(0));
  foreach(factor(abs(m))[, 1], q, if(q != 2, r *= q));
  return(r);
};

\\ ------------------------------------------------------------- 1. calibration
{
section1(L, F) =
  my(bad);
  print("=== 1. the sequences and the conic (calibration) ===");
  print("");
  printf("  f_n = U_n(4,1) : %s ...\n", vector(9, i, F[i]));
  printf("  l_n = V_n(4,1)/2: %s ...\n", vector(9, i, L[i]));
  bad = 0;
  for(n = 0, NMAX,
    if(L[n + 1]^2 - 3*F[n + 1]^2 != 1, bad++));
  for(n = 2, NMAX,
    if(F[n + 1] != 4*F[n] - F[n - 1], bad++);
    if(L[n + 1] != 4*L[n] - L[n - 1], bad++));
  printf("  l^2 - 3 f^2 = 1 and the recurrence u_{n+1} = 4 u_n - u_{n-1}:\n");
  printf("    %d failures over n <= %d\n", bad, NMAX);
  print("  (E009's definition; E032 calls these f_n, l_n)");
  print("");
  return(bad);
};

\\ --------------------------------------------------------- 2. perfect powers
{
section2(L, F) =
  my(hits, e);
  print("=== 2. the perfect powers that are actually there ===");
  print("");
  hits = 0;
  for(n = 1, NMAX,
    e = ispower(F[n + 1]);
    if(e, printf("  f_%d = %d is a perfect %d-th power\n", n, F[n + 1], e); hits++);
    e = if(L[n + 1] > 1, ispower(L[n + 1]), 0);
    if(e, printf("  l_%d = %d is a perfect %d-th power\n", n, L[n + 1], e); hits++));
  printf("\n  %d nontrivial perfect powers with 1 <= n <= %d\n", hits, NMAX);
  print("  (f_0 = 0 and l_0 = 1 are the trivial ones Silliman-Vogt exclude)");
  print("  For the exponent 2 this is a theorem, not a search: E032(b) cites");
  print("  Ljunggren for x^2 - 3y^4 = 1, whose only solutions are (2,1),(7,2).");
  print("");
  return(hits);
};

\\ ------------------------------- 3. Silliman-Vogt Theorem 2 for (b,c)=(4,-1)
{
section3() =
  my(b, c, disc, N, psi, alpha, t1, t2log, t3);
  print("=== 3. Silliman-Vogt Theorem 2 evaluated for our sequence ===");
  print("");
  b = 4; c = -1;
  disc = b^2 + 4*c;
  alpha = (b + sqrt(disc))/2;
  print("  their normalisation u_{n+2} = b u_{n+1} + c u_n, so (b,c) = (4,-1)");
  printf("  nondegenerate, b^2+4c = %d > 0  =>  Theorem 2 applies\n", disc);
  N = 2^8 * radodd(c) * radodd(disc);
  psi = N;
  foreach(factor(N)[, 1], q, psi = psi * (1 + 1/q));
  printf("  N    = 2^8 * rad'(c) * rad'(b^2+4c) = 2^8 * %d * %d = %d\n",
         radodd(c), radodd(disc), N);
  printf("  psi(N) = %d\n", psi);
  printf("  alpha  = (b + sqrt(b^2+4c))/2 = %.6f  (= 2 + sqrt 3)\n", alpha);
  t1 = 17;
  t2log = (psi/12 + 1) * log(psi)/log(10);
  t3 = 4*log(alpha)*max(30, N + 1);
  printf("  the three terms of the bound p <= max{...}:\n");
  printf("    17\n");
  printf("    psi(N)^(psi(N)/12+1) = %d^%d  ~  10^%.0f\n", psi, psi/12 + 1, t2log);
  printf("    4 log|alpha| * max{30, N+1} = %.0f\n", t3);
  print("");
  print("  So the general theorem is explicit but not usable as it stands: the");
  print("  middle term dominates by ~400 orders of magnitude.  Their Section 5");
  print("  (an elementary sieve fed by Thue bounds) is the practical route, and");
  print("  it is what their Theorem 3 demonstrates -- on (b,c) = (3,1),(5,1),");
  print("  (7,1), none of which is ours.");
  print("");
  return(0);
};

\\ ------------------------------------------------------ 4. the descent shapes
{
section4(L, F) =
  my(bad, l, f, u, v);
  print("=== 4. the descent our sequence gives, verified ===");
  print("");
  print("  f_n = y^p  <=>  l_n^2 - 3 y^{2p} = 1, i.e. (l-1)(l+1) = 3 f^2.");
  print("  l_n is odd for n even and even for n odd, so there are two cases:");
  print("    n odd  (l even): gcd(l-1,l+1) = 1, so {l-1,l+1} = {3a^2, b^2}");
  print("                     with b^2 - 3a^2 = +-2;");
  print("    n even (l odd) : gcd(l-1,l+1) = 2, l-1 = 2u, l+1 = 2v, uv = 3g^2,");
  print("                     v = u+1, giving b^2 - 3a^2 = +-1 (Pell again).");
  print("");
  bad = 0;
  print("   n   l_n mod 2   gcd(l-1,l+1)   core(l-1)   core(l+1)");
  for(n = 1, 12,
    l = L[n + 1]; f = F[n + 1];
    if((l - 1)*(l + 1) != 3*f^2, bad++);
    u = gcd(l - 1, l + 1);
    if(n % 2 == 1 && u != 1, bad++);
    if(n % 2 == 0 && u != 2, bad++);
    printf("  %2d      %d           %d          %-10d %-10d\n",
           n, l % 2, u, core(l - 1), core(l + 1)));
  printf("\n  %d failures\n", bad);
  print("  The n odd case is the one with a genuinely new equation; the n even");
  print("  case falls back on the Pell equation and gives nothing new.");
  print("");
  return(bad);
};

\\ ---------------------------------------------- 5. what E033/E034 actually need
{
section5(L, F) =
  my(W, kap, worst, m, lm, fm);
  print("=== 5. the quantity E033/E034 need is NOT a perfect power ===");
  print("");
  print("  E032(1) writes b = R k^2 with an explicit square factor, and");
  print("  k = (that factor) * kappa where kappa^2 is the square part of an");
  print("  explicit COFACTOR W.  E032(c) reads the Artin condition as");
  print("  kappa^4 < c^2 W/(eps s)^2, i.e. kappa << W^{1/4}.  The column below is");
  print("  the CONSTANT-FREE PROXY kappa^4/W, not the condition itself: it shows");
  print("  the shape of the demand, not whether it holds.  The four families:");
  print("    n = 2m+1, b_- :  W = 3 f_{m+1} l_m");
  print("    n = 2m+1, b_+ :  W =   f_m     l_{m+1}");
  print("    n = 2m  , b_- :  W = (3f_m + l_m)(l_m - f_m)");
  print("    n = 2m  , b_+ :  W = 3 (l_m + f_m)(3 f_m - l_m)");
  print("");
  print("   m   family        kappa    kappa^4 / W      (needs < 1)");
  worst = 0;
  for(m = 1, KMAX,
    lm = L[m + 1]; fm = F[m + 1];
    foreach([[3*F[m + 2]*lm, "2m+1, b-"],
             [fm*L[m + 2], "2m+1, b+"],
             [(3*fm + lm)*(lm - fm), "2m  , b-"],
             [3*(lm + fm)*(3*fm - lm), "2m  , b+"]], it,
      W = it[1];
      if(W <= 0, next);
      kap = core(W, 1)[2];
      if(m <= 8 || kap > 12,
        printf("  %2d   %s   %-6d   %.3e\n", m, it[2], kap, 1.0*kap^4/W));
      worst = max(worst, 1.0*kap^4/W)));
  printf("\n  worst kappa^4/W over m <= %d : %.3e\n", KMAX, worst);
  print("");
  print("  This is an INEQUALITY about the square part, with the square-free");
  print("  complement free to be anything.  Perfect-power machinery -- BMS,");
  print("  Silliman-Vogt, Bennett-Skinner -- answers 'W = y^p' with the exponent");
  print("  as the unknown.  Here the unknown is a DIVISOR d = kappa^2 ranging up");
  print("  to W^{1/2}, and each d is a different Thue equation, so the family is");
  print("  infinite.  That is E032(c)'s point, and reading BMS II confirms it:");
  print("  nothing in that toolbox bounds a square part.");
  print("");
  return(0);
};

\\ ------------------- 6. (E053) is our cofactor of the shape BLMS 2007 covers?
\\ Their Theorem 1 needs  prod_{i=1}^m U_{n_i} = mu y^p  with mu in T-bar (an
\\ S-unit for a FIXED finite prime set T), p prime, and m < p.  Section 6 checks
\\ the identities that decide whether our W is even of the shape "product of
\\ U-terms", independently of the hypotheses on mu and p.
{
section6(L, F) =
  my(bad, lm, fm, A, B, sq, v, worst);
  print("=== 6. (E053) the shape of our cofactors against BLMS 2007 ===");
  print("");
  print("  (i) l_m is not a U-term but a ratio of two:  l_m = U_{2m}/(2 U_m)");
  bad = 0;
  for(m = 1, 60,
    if(F[2*m + 1] != 2*F[m + 1]*L[m + 1], bad++));
  printf("      U_{2m} = 2 U_m l_m for 1 <= m <= 60 : %d failures\n", bad);
  print("  (ii) the even-index families use two FURTHER sequences, l_m - f_m and");
  print("       3 f_m - l_m, which satisfy the same recurrence but are neither");
  print("       U nor V; only their product is a term:");
  for(m = 1, 60,
    lm = L[m + 1]; fm = F[m + 1];
    if((lm - fm)*(3*fm - lm) != F[2*m], bad++);
    if((3*fm + lm)*(3*fm - lm) != L[2*m + 1] - 2, bad++));
  printf("      (l_m-f_m)(3f_m-l_m) = f_{2m-1} and (3f_m+l_m)(3f_m-l_m)\n");
  printf("      = l_{2m}-2 for 1 <= m <= 60 : %d failures in total\n", bad);
  print("");
  print("  (iii) the hypothesis that actually fails.  Writing W = kappa^2 * v");
  print("        with v squarefree puts our question in the form W = v * y^2,");
  print("        i.e. mu = v and p = 2.  BLMS need mu in T-bar for a FIXED");
  print("        finite T, and m < p.  Here v is the squarefree complement:");
  print("");
  print("     m   W = 3 f_{m+1} l_m       squarefree part v      omega(v)");
  worst = 0;
  for(m = 1, 12,
    lm = L[m + 1];
    A = 3*F[m + 2]*lm;
    v = core(A);
    sq = core(A, 1)[2];
    worst = max(worst, omega(v));
    printf("    %2d   %-22s %-22s %d\n", m, A, v, omega(v)));
  printf("\n      largest number of distinct primes in v over m <= 12 : %d\n", worst);
  print("      v grows and its prime support is unbounded, so no fixed finite T");
  print("      contains all the mu's.  That is hypothesis (1) of their Theorem 1,");
  print("      and it is the one our question violates -- before even reaching");
  print("      m < p, which fails too since p = 2 and m = 2.");
  print("");
  print("  (iv) BLMS say so themselves (their Section 2): the equation");
  print("       U_n U_m = y^2 'is not covered by our Theorems 1, 2, which however");
  print("       do cover the equation U_n U_m = y^p for a prime p >= 3'.");
  print("");
  print("  (v) what their Reduction Theorem DOES give us.  It reduces a product");
  print("      to a single term, U_q = +- A^{(q-1)/2} z^p, and A = 1 when r, s");
  print("      are coprime.  Our (r,s) = (4,-1) is coprime, so for our sequence");
  print("      the product problem reduces to U_q = z^p -- which is exactly the");
  print("      sub-project E052(c) identified.  The dependency is one-way.");
  print("");
  return(bad);
};

{
run() =
  my(LF, L, F, nfail);
  LF = lucas(NMAX + 2);
  L = LF[1]; F = LF[2];
  nfail = 0;
  nfail += section1(L, F);
  section2(L, F);
  section3();
  nfail += section4(L, F);
  section5(L, F);
  nfail += section6(L, F);
  print("=== VERDICT ===");
  printf("  failures: %d\n", nfail);
  print("  [T(CAS)] the only perfect power among f_n, l_n for 1 <= n <= 300 is");
  print("  f_2 = 4; for the exponent 2 this is a theorem (E032(b), Ljunggren).");
  print("  [T] The generalisation asked about EXISTS (Silliman-Vogt), our");
  print("  sequence is inside its framework as (b,c) = (4,-1), and no published");
  print("  worked example covers it.  Their general bound for us is ~10^400, so");
  print("  a determination would mean running their Section 5 sieve: real work,");
  print("  not a citation.");
  print("  [T] But it would answer a question this project does not have.  The");
  print("  kappa/s gaps of E033/E034 are square-part inequalities, a species no");
  print("  perfect-power method addresses.  E032(c) said so; BMS II read in the");
  print("  original does not change it.");
  return(nfail);
};

run();
