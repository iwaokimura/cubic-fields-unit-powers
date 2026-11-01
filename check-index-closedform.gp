\\ check-index-closedform.gp --- E031: a closed form for the index along the
\\ exceptional family, and what it leaves to prove for the open problem.
\\
\\ SETTING (E027 notation, = ours).  For n >= 2, sign sg = +-1, with
\\ (2+sqrt3)^n = l_n + f_n sqrt3, l = l_n, f = f_n, l_{n-1} = 2l-3f, f_{n-1} = 2f-l:
\\      b   = (l + 2 sg) f_{n-1},   A = 1 + sg*l,   B = (l + 2 sg) l_{n-1} - 1,
\\      G   = X^3 - B X^2 + A X - 1,   theta = v = the real root,   eta_b = v^2,
\\      I   = [O_K : Z[v]],   a = [O_K : Z[theta_b]],   m = |AB-1| (lem:mAB).
\\ Open problem: is v the fundamental unit for all but finitely many n?
\\ Route: Artin, i.e. |D_K| > 4 B^{3/2} + 24, which needs I bounded ABOVE.
\\
\\ WHAT THIS SCRIPT ESTABLISHES:
\\ (1) [T] disc(f_b) = (AB-1)^2 disc(G), as an identity in Z[l,f]/(l^2-3f^2-1).
\\     (So the two orders' discriminants differ by the explicit square m^2.)
\\ (2) [T] b^3 - 4 = Y^2 Z, an IDENTITY, with Y and Z explicit Pell expressions:
\\       n odd,  sg=-1:   Y = f_{(3n-1)/2} + l_{(n-1)/2}
\\       n odd,  sg=+1:   Y = l_{(3n-1)/2} - 3 f_{(n-1)/2}
\\       n even, sg=-1:  2Y = 3f_{3n/2} - l_{3n/2} + 3f_{n/2-1} + 3l_{n/2-1}
\\       n even, sg=+1:  2Y = -f_{3n/2} + l_{3n/2} - 3f_{n/2-1} - l_{n/2-1}
\\     This is thm:exc (exceptional => b^3-4 non-squarefree) made EXPLICIT and
\\     constructive for this family: the square divisor is written down.
\\ (3) [E: n <= 24] Y is the WHOLE square part of b^3-4, i.e. Z is squarefree away
\\     from b.  This is the one remaining gap, and it is a (star)-type statement --
\\     but now about an explicit sequence Z(n), not about a general integer.
\\ (4) [T, given (3)] a = a_b * Y * (2,3-corrections) with a_b = prod p^{[3 v_p(b)/2]},
\\     so |D_K| = 27 |b|^3 Z / a_b^2 : the Y^2 CANCELS.  The Artin condition becomes
\\     an explicit inequality between Pell expressions.
\\ (5) [E: n <= 44] I = f_{n-1} * E_n with E_n tiny ({2,3,5}-smooth except at
\\     n = 27, 29, 39, where the forward-locus primes 7, 7, 29 appear; max 348).
\\     The Artin condition only needs E_n << (2+sqrt3)^{n/2}: an EXPONENTIAL margin.
\\     So the Artin condition needs far less than a bound on E_n by a constant.
\\
\\ Usage:  gp -q check-index-closedform.gp        (about 8 seconds)

default(realprecision, 40);

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

lf(n) = my(L=1,F=0); for(i=1,n, my(L2=2*L+3*F, F2=L+2*F); L=L2; F=F2); [L,F];
fs(k) = if(k < 0, -lf(-k)[2], lf(k)[2]);
ls(k) = lf(abs(k))[1];

\\ the closed form Y(n, sg) of (2) above
Yform(n, sg) =
{
  my(j = (3*n)\2, k = n\2);
  if(n % 2 == 1,
     if(sg < 0, fs(j) + ls(k), ls(j) - 3*fs(k)),
     if(sg < 0, (3*fs(j) - ls(j) + 3*fs(k-1) + 3*ls(k-1))/2,
                (-fs(j) + ls(j) - 3*fs(k-1) - ls(k-1))/2));
}
\\ the actual square part of b^3-4, by factorisation
ysq(n, sg) =
{
  my(w = lf(n), l = w[1], f = w[2], b = (l+2*sg)*(2*f-l));
  my(fa = factor(abs(b^3-4)), y = 1);
  for(i = 1, matsize(fa)[1], y *= fa[i,1]^(fa[i,2]\2));
  y;
}
dat(n, sg) =    \\ [b, A, B, G]
{
  my(w = lf(n), l = w[1], f = w[2], lm = 2*l-3*f, fm = 2*f-l);
  my(A = 1+sg*l, B = (l+2*sg)*lm-1, b = (l+2*sg)*fm);
  [b, A, B, x^3 - B*x^2 + A*x - 1];
}

\\ ---------------------------------------------------------------- (1)
print("### (1) [T] the identity  disc(f_b) = (AB-1)^2 disc(G) ###");
{
my(red(P) = lift(Mod(P, l^2-3*f^2-1)), ok = 1);
foreach([-1,1], sg,
  my(lm = 2*l-3*f, fm = 2*f-l, A = 1+sg*l, B = (l+2*sg)*lm-1, bb = (l+2*sg)*fm);
  my(D1 = -27*bb^3*(bb^3-4));
  my(D2 = (A*B-1)^2*(A^2*B^2-4*A^3-4*B^3+18*A*B-27));
  my(r = (red(D1-D2) == 0));
  ok = ok && r;
  print("    sign ", if(sg<0,"-","+"), " : identity holds in Z[l,f]/(l^2-3f^2-1) : ", r));
check(ok, "E031(1): disc(f_b) = (AB-1)^2 disc(G) in Z[l,f]/(l^2-3f^2-1), both signs");
print("    => [O_K:Z[theta_b]] = |AB-1| * [O_K:Z[v]], i.e. a = m*I (lem:mAB).");
}

\\ ---------------------------------------------------------------- (2),(3)
print("");
print("### (2) [T] b^3-4 = Y^2 Z identically, and (3) [E] Y is the whole square part ###");
{
my(rd(P) = lift(Mod(P, L^2-3*F^2-1)), cj(P) = subst(P, L, -L));
my(divq(D, N) =                       \\ N/D in the ring, or 0
  my(Db = rd(cj(D)), T = rd(N*Db), NN = rd(D*Db), t1, t0);
  t1 = polcoef(T,1,L); t0 = polcoef(T,0,L);
  if(t1 % NN == 0 && t0 % NN == 0, rd((t1/NN)*L + t0/NN), 0));
my(l3 = L^3+9*L*F^2, f3 = 3*L^2*F+3*F^3);
my(l31 = 2*l3+3*f3, f31 = l3+2*f3, lm1 = 2*L-3*F, fm1 = 2*F-L);
my(cases = [
  ["n odd,  sign -", 2*L^2+6*F^2+6*L*F, L^2+3*F^2+4*L*F, -1, f31 + L],
  ["n odd,  sign +", 2*L^2+6*F^2+6*L*F, L^2+3*F^2+4*L*F,  1, l31 - 3*F],
  ["n even, sign -", L^2+3*F^2, 2*L*F, -1, (3*f3-l3+3*fm1+3*lm1)/2],
  ["n even, sign +", L^2+3*F^2, 2*L*F,  1, (-f3+l3-3*fm1-lm1)/2]]);
for(i = 1, #cases,
  my(c = cases[i], b = rd((c[2]+2*c[4])*(2*c[3]-c[2])));
  my(Q = divq(rd(c[5]^2), rd(b^3-4)));
  print("    ", c[1], " :  Y^2 | b^3-4 : ", Q != 0);
  check(Q != 0, Str("E031(2): Y^2 | b^3-4 is a polynomial identity, case ", c[1]));
  if(Q != 0, print("        Z = (b^3-4)/Y^2 = ", Q)));
}
print("");
print("    numerical check that Y is the FULL square part (delta = 1):");
{
my(bad = 0, tested = 0);
for(n = 2, 24,
  foreach([-1,1], sg,
    tested++;
    if(Yform(n,sg) != ysq(n,sg), bad++;
       print("      delta > 1 at n = ", n, " sign ", sg,
             " : y = ", ysq(n,sg), " vs Y = ", Yform(n,sg)))));
print("    n <= 24, both signs: ", tested, " cases, deviations: ", bad,
      "   [E: Z is squarefree away from b on this range]");
check(bad == 0 && tested == 46, "E031(3): Y is the whole square part of b^3-4, 46 cases, n<=24");
}

\\ ---------------------------------------------------------------- (4)
print("");
print("### (4) the index in closed form:  a = a_b * Y * eps,  eps a {2,3}-unit ###");
print("    Then |D_K| = 27|b|^3 |b^3-4| / a^2 = 27 |b|^3 Z / (a_b eps)^2: the Y^2");
print("    CANCELS, and the Artin condition becomes explicit in the Pell data.");
print("    (a_b = prod_{p | b} p^{[3 v_p(b)/2]}; eps collects the 2,3-adic");
print("    corrections of thm:idx23, which the p >= 5 formula does not see.)");
print("  n s |  eps = a/(a_b Y)   {2,3}-unit?   |D_K| = 27|b|^3 Z/(a_b eps)^2 ?");
{
my(bad = 0, seen = List());
for(n = 2, 14,
  foreach([-1,1], sg,
    my(D = dat(n,sg), b = D[1], DK = nfdisc(D[4]));
    my(a = sqrtint(abs(poldisc(x^3-3*b*x-b^3)/DK)));
    my(fb = factor(abs(b)), ab = 1);
    for(i = 1, matsize(fb)[1], ab *= fb[i,1]^((3*fb[i,2])\2));
    my(Y = Yform(n,sg), Z = abs(b^3-4)/Y^2, eps = a/(ab*Y));
    my(r = eps); foreach([2,3], p,
      while(numerator(r) % p == 0, r = r/p);
      while(denominator(r) % p == 0, r = r*p));
    my(ok = (r == 1) && (27*abs(b)^3*Z/(ab*eps)^2 == abs(DK)));
    if(!ok, bad++);
    listput(seen, eps);
    if(n <= 8 || !ok,
      print("  ", n, " ", if(sg<0,"-","+"), " |  eps = ", eps, "\t",
            if(r == 1, "yes", "NO  <<<"), "\t", if(ok, "yes", "NO  <<<")))));
print("  failures over n <= 14, both signs: ", bad);
check(bad == 0, "E031(4): a = a_b*Y*eps with eps a {2,3}-unit, and |D_K| = 27|b|^3 Z/(a_b eps)^2, n<=14");
print("  values of eps taken: ", vecsort(Vec(seen), , 8),
      "   [E: bounded, and a {2,3}-unit, on this range]");
}

\\ ---------------------------------------------------------------- (5)
print("");
print("### (5) what the Artin condition actually needs ###");
print("    Artin:  |D_K| > 4 B^{3/2} + 24, i.e.  I^2 < |disc(G)| / (4 B^{3/2}+24).");
print("  n s |  I           f_{n-1}      E = I/f_{n-1}  |  bound I < K_n      Artin ratio");
{
my(worst = 10^9);
for(n = 2, 30,
  my(w = lf(n), fm = 2*w[2]-w[1]);
  foreach([-1,1], sg,
    my(D = dat(n,sg), B = D[3], G = D[4]);
    my(DK = nfdisc(G), I = sqrtint(poldisc(G)/nfdisc(G)));
    my(K = sqrt(abs(poldisc(G))/(4*abs(B)^(3/2)+24)));
    my(r = abs(DK)/(4*abs(B)^(3/2)+24));
    if(n >= 5 && r < worst, worst = r);
    if(n <= 8 || n >= 27,
      print("  ", n, " ", if(sg<0,"-","+"), " | ", I, "\t", fm, "\t", I/fm,
            "\t| ", strprintf("%.4e", K), "\t", strprintf("%.4e", r)))));
print("  minimum Artin ratio over n >= 5 (both signs): ", strprintf("%.4f", worst));
check(worst >= 3.87, "E031(5): the Artin ratio is >= 3.87 for 5 <= n <= 30 -- MEASURED over that range only, and floating-point");
print("  => the condition holds for 5 <= n <= 30 (the computed range; the extension");
print("     to every n >= 5 is [E], not [T] -- see E119); it fails only");
print("     at n = 2 (both),");
print("     n = 3 (sign -) and n = 4 (sign -), and of those only n=2,3(-) are");
print("     genuine failures of fundamentality (E027(3)).");
print("  => since I = f_{n-1} E_n and K_n / f_{n-1} grows like (2+sqrt3)^{n/2},");
print("     ALL that is needed is  E_n << (2+sqrt3)^{n/2}  -- an exponential margin");
print("     against the observed E_n <= 348 for n <= 44.");
}
printf("\nE031 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);

quit
