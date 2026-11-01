\\ check-bsquare.gp --- E032: the square part of b along the exceptional family is
\\ an IDENTITY too, and what is then left of the Artin route.
\\
\\ CONTEXT.  E031 wrote a = a_b * Y * eps * s with a_b = prod_{p|b} p^{[3 v_p(b)/2]},
\\ Y^2 || b^3-4 (an identity), eps a {2,3}-unit, s^2 || Z = (b^3-4)/Y^2, and
\\        |D_K| = 27 |b|^3 Z / (a_b eps s)^2 .
\\ If b = R k^2 with R squarefree then a_b = |b| k, so the Artin condition
\\ |D_K| > 4 B^{3/2} + 24 reads
\\        (k eps s)^2  <  27 |b| Z / (4 B^{3/2} + 24) .
\\ E031 measured k/sqrt(|b|) ~ w^{-n/2}: the square part of b is far below the
\\ trivial bound, and that is exactly the slack the condition lives on.  Where does
\\ that square part come from?  From identities, as it turns out.
\\
\\ (1) [T] THE FOUR FACTORISATION IDENTITIES.  With l^2-3f^2 = 1 throughout,
\\     n = 2m+1 :  l_n - 2 = 6 f_m f_{m+1},        l_n + 2 = 2 l_m l_{m+1},
\\                 f_{n-1} = f_{2m} = 2 f_m l_m,
\\        so     b_-(n) = 12 f_m^2 f_{m+1} l_m ,   b_+(n) = 4 f_m l_m^2 l_{m+1} ;
\\     n = 2m   :  l_n - 2 = (3f_m - l_m)(3f_m + l_m),   l_n + 2 = 3(l_m-f_m)(l_m+f_m),
\\                 f_{n-1} = f_{2m-1} = (l_m - f_m)(3 f_m - l_m),
\\        so     b_-(n) = (3f_m-l_m)^2 (3f_m+l_m)(l_m-f_m) ,
\\               b_+(n) = 3 (l_m-f_m)^2 (l_m+f_m)(3f_m-l_m) .
\\     Every one of these is elementary from l^2 = 3f^2+1; e.g.
\\     (3f-l)(3f+l) = 9f^2-l^2 = 6f^2-1 = l_{2m}-2.
\\     So b carries an EXPLICIT square factor of size ~ w^{n/2}, w = 2+sqrt3, and
\\     k = (that factor) * kappa, where kappa^2 is the square part of the cofactor.
\\
\\ (2) [T] THE FOUR LIMITS.  27 Z / (4 B^{3/2}+24) tends to a constant depending
\\     only on the class (sign, parity of n): 1.0086, 0.3362, 0.6724, 2.0173.
\\     So the Artin condition is equivalent to
\\        (kappa * eps * s)^2  <  c^2 * tau ,   tau = squarefree part of the cofactor,
\\     with c^2 the constant above -- i.e. to the statement that the explicit
\\     cofactor is NOT close to a perfect square.
\\
\\ WHAT REMAINS -- and what the literature does NOT give.  (An earlier version of
\\ this header said the kappa statement is "of a kind that squares in Lucas
\\ sequences settle effectively".  That was wrong; see E032, Analysis,
\\ and commit 0b24d56.)
\\   Our sequences are f_n = U_n(4,1), l_n = V_n(4,1)/2.  Bugeaud-Mignotte-Siksek
\\   (Ann. of Math. 163 (2006), 969-1018) is about THE Fibonacci and THE Lucas
\\   sequence, (P,Q) = (1,-1): not applicable.  Ribenboim-McDaniel (JNT 58 (1996),
\\   104-123) need P,Q odd; Kagawa-Terai (Manuscripta Math. 96 (1998), 195-202)
\\   need 4|P, Q = -1: neither covers (4,1).
\\   What does apply: l^2-3f^2 = 1 turns f_j = d v^2 into l_j^2 - 3 d^2 v^4 = 1 and
\\   l_j = d v^2 into d^2 v^4 - 3 f_j^2 = 1, quartic Pell equations with at most two
\\   positive solutions FOR EACH FIXED d (Ljunggren, J. LMS 41 (1966), 542-544;
\\   Walsh, Acta Arith. 87 (1998), 179-188; Akhtari, Crelle 630 (2009), 33-57).
\\   In particular x^2-3y^4 = 1 has exactly (y,x) = (1,2),(2,7), so f_j is a square
\\   only for j = 0,1,2 and l_j only for j = 0: the extremal case is excluded.
\\   BUT the Artin condition needs kappa << W^{1/4}, i.e. d up to W^{1/2}, while
\\   those theorems fix d first.  So (a) kappa and (b) s (the square part of Z, the
\\   (star)-type gap of E031(3)) are the SAME species, and both are open.
\\
\\ Usage:  gp -q check-bsquare.gp        (about 2 seconds)

default(realprecision, 50);
\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

lf(n) = my(L=1,F=0); for(i=1,n, my(L2=2*L+3*F, F2=L+2*F); L=L2; F=F2); [L,F];
fs(k) = if(k < 0, -lf(-k)[2], lf(k)[2]);
ls(k) = lf(abs(k))[1];
Yform(n, sg) = my(j = (3*n)\2, k = n\2); if(n % 2 == 1, if(sg < 0, fs(j) + ls(k), ls(j) - 3*fs(k)), if(sg < 0, (3*fs(j) - ls(j) + 3*fs(k-1) + 3*ls(k-1))/2, (-fs(j) + ls(j) - 3*fs(k-1) - ls(k-1))/2));

\\ ---------------------------------------------------------------- (1)
print("### (1) the four factorisation identities for b ###");
{
my(bad = 0, tested = 0);
for(m = 1, 14,
  \\ n = 2m+1
  my(n = 2*m+1, v = lf(n), l = v[1], f = v[2], fm1 = 2*f-l);
  tested += 3;
  if(l - 2 != 6*fs(m)*fs(m+1), bad++; print("  FAIL l-2, m=", m));
  if(l + 2 != 2*ls(m)*ls(m+1), bad++; print("  FAIL l+2, m=", m));
  if(fm1 != 2*fs(m)*ls(m), bad++; print("  FAIL f_{2m}, m=", m));
  tested += 2;
  if((l-2)*fm1 != 12*fs(m)^2*fs(m+1)*ls(m), bad++; print("  FAIL b_-, n=", n));
  if((l+2)*fm1 != 4*fs(m)*ls(m)^2*ls(m+1), bad++; print("  FAIL b_+, n=", n));
  \\ n = 2m
  my(n2 = 2*m, v2 = lf(n2), l2 = v2[1], f2 = v2[2], fm2 = 2*f2-l2);
  my(F = fs(m), L = ls(m));
  tested += 5;
  if(l2 - 2 != (3*F-L)*(3*F+L), bad++; print("  FAIL l_{2m}-2, m=", m));
  if(l2 + 2 != 3*(L-F)*(L+F), bad++; print("  FAIL l_{2m}+2, m=", m));
  if(fm2 != (L-F)*(3*F-L), bad++; print("  FAIL f_{2m-1}, m=", m));
  if((l2-2)*fm2 != (3*F-L)^2*(3*F+L)*(L-F), bad++; print("  FAIL b_-, n=", n2));
  if((l2+2)*fm2 != 3*(L-F)^2*(L+F)*(3*F-L), bad++; print("  FAIL b_+, n=", n2));
);
print("  identities tested: ", tested, ",  failures: ", bad);
check(bad == 0 && tested == 140, "E032(1): the ten factorisation identities for l_n -+ 2, f_{n-1} and b_-+(n), 140 instances, m<=14");
print("  (each follows from l^2 = 3f^2+1 alone: e.g. (3f-l)(3f+l) = 6f^2-1 = l_{2m}-2)");
}

\\ ---------------------------------------------------------------- (2)
print("");
print("### (2) the explicit square factor against the true square part of b ###");
print("  n s |  identity square root   k (true)     kappa = k/identity   k/sqrt|b|");
{
for(n = 3, 18,
  my(v = lf(n), l = v[1], f = v[2], fm = 2*f-l, m = n\2);
  foreach([-1,1], sg,
    my(b = (l+2*sg)*fm);
    my(fb = factor(abs(b)), k = 1);
    for(i = 1, matsize(fb)[1], k *= fb[i,1]^(fb[i,2]\2));
    my(id = if(n % 2 == 1, if(sg<0, fs(m), ls(m)),
                           if(sg<0, abs(3*fs(m)-ls(m)), abs(ls(m)-fs(m)))));
    check(k % id == 0 && k/id <= 12,
          Str("E032(1): the identity square factor divides the true k, with kappa = k/id <= 12, n=", n));
    print("  ", n, " ", if(sg<0,"-","+"), " |  ", id, "\t", k, "\t", k/id, "\t",
          strprintf("%.6f", k/sqrt(abs(b)*1.0)))));
print("  kappa = k/(identity part) is the only non-explicit piece: it is the square");
print("  root of the square part of the explicit cofactor, and stays small (1..12");
print("  over this range).  So the w^{n/2}-sized square part of b is an IDENTITY,");
print("  not an accident; only the bounded kappa is arithmetic.");
}

\\ ---------------------------------------------------------------- (3)
print("");
print("### (3) the four limits of 27 Z / (4 B^{3/2}+24), and the true Artin ratio ###");
print("  n s |  27Z/(4B^1.5+24)     eps*s (from E031)      Artin ratio");
{
for(n = 11, 18,
  my(v = lf(n), l = v[1], f = v[2], lm = 2*l-3*f, fm = 2*f-l);
  foreach([-1,1], sg,
    my(b = (l+2*sg)*fm, A = 1+sg*l, B = (l+2*sg)*lm-1);
    my(G = x^3-B*x^2+A*x-1, DK = nfdisc(G));
    my(a = sqrtint(abs(poldisc(x^3-3*b*x-b^3)/DK)));
    my(fb = factor(abs(b)), ab = 1);
    for(i = 1, matsize(fb)[1], ab *= fb[i,1]^((3*fb[i,2])\2));
    my(Y = Yform(n,sg), Z = abs(b^3-4)/Y^2, thr = 4*abs(B)^(3/2)+24);
    check(abs(27*Z/thr - if(n % 2 == 1, if(sg<0, 1.00865, 0.33622), if(sg<0, 0.67243, 2.01729))) < 0.0001,
          Str("E032(2): 27Z/(4B^{3/2}+24) sits at its limiting constant to 4 decimals -- FLOATING POINT, n=", n));
    print("  ", n, " ", if(sg<0,"-","+"), " |  ", strprintf("%.5f", 27*Z/thr),
          "\t\t", a/(ab*Y), "\t\t", strprintf("%.4e", abs(DK)/thr))));
print("  the limits are   1.00865 (n odd, -),  0.33622 (n odd, +),");
print("                   0.67243 (n even, -), 2.01729 (n even, +).");
print("  => using only the trivial k^2 <= |b| the condition is borderline (and fails");
print("     once eps > 1); the whole margin comes from k being ~ w^{-n/2} sqrt(|b|),");
print("     which (1) explains: the square part of b is an identity, not an accident.");
}
printf("\nE032 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);

quit
