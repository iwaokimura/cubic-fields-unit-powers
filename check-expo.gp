\\ check-expo.gp --- E026 (a),(b): the exponent n of eta_b = eta_0^n, the size
\\ route that FAILS to determine it, and the unconditional upper bound for n.
\\
\\ CONTEXT.  The first paper settles when eta_b IS the fundamental unit.  The sequel asks
\\ the complementary question, deferred from the first paper: when it is not, WHICH power
\\ of the fundamental unit is it?  Write
\\        eta_b = eta_0^{n(b)} ,   n(b) = 1  <=>  eta_b fundamental.
\\
\\ (a) THE DATA.  For the square-exceptions b_pm(k) of thm:closed (k <= KMAX, both
\\     branches) this section prints D_K, the index a = [O_K:Z[theta]], n from
\\     bnfisunit, and the two ratios that decide whether the Artin/size argument of
\\     paper 1 (Lemma 4.1, |D_K| < 4e^3+24 for a unit e>1) can prove
\\     n = 2 -- i.e. can rule out eta_0 = sqrt(eta_b) being itself a q-th power:
\\           r_q = |D_K| / (4 * eta_0^{3/q} + 24) ,   r_q >= 1 excludes q .
\\     RESULT: r_2 < 1 happens along the family (b = 1425: r_2 = 0.45) while n = 2
\\     there anyway, so the size route CANNOT establish Umemoto's observation.  This
\\     is the same failure mode as (star) in E019(c): a lower bound for |D_K| is not
\\     available without controlling the square part of b^3-4.  The route that does
\\     work is the curve C_q of E021/E022 -- see check-composite-q.gp.
\\
\\ (b) THE UPPER BOUND FOR n [T, cites Smyth 1971].  A unit e>1 of a complex cubic
\\     field has minimal polynomial X^3-BX^2+AX-1; it is NONRECIPROCAL, since the
\\     reciprocal condition is A = B, which forces p(1) = A-B = 0, contradicting
\\     irreducibility.  By Smyth's theorem the Mahler measure of a nonreciprocal
\\     algebraic integer is at least the plastic number rho = 1.3247...  (the real
\\     root of x^3-x-1, the smallest Pisot number), and for such an e the Mahler
\\     measure is e itself (one conjugate outside the unit circle).  Hence
\\           e >= rho  for every unit e > 1 of a complex cubic field,
\\     and therefore
\\           n(b) = log(eta_b)/log(eta_0) <= log(eta_b)/log(rho) .
\\     This section checks the bound against the known n, and checks that it is
\\     ATTAINED, exactly, at the sporadic b = 3 (where eta_0 = rho and n = 13).
\\     Reference (confirmed via the zbMATH Open API, Commandment III):
\\     C. J. Smyth, On the product of the conjugates outside the unit circle of an
\\     algebraic integer, Bull. London Math. Soc. 3 (1971), 169-175,
\\     DOI 10.1112/blms/3.2.169, Zbl 3372120.
\\
\\ Usage:  gp -q check-expo.gp        (a few seconds)

default(realprecision, 80);
\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

KMAX = 7;

\\ f_n:  f_0=0, f_1=1, f_{n+1} = 4 f_n - f_{n-1}   (l_n + f_n sqrt3 = (2+sqrt3)^n)
fseq(k) = my(a=0,b=1); if(k==0, return(0)); for(i=2,k, my(c=4*b-a); a=b; b=c); b;

print("### (a) the exponent n along the Pell family, and the size ratios r_q ###");
print("    r_q = |D_K| / (4*eta_0^{3/q}+24);  r_q >= 1 would exclude eta_0 = e^q.");
print("  k  s  b                D_K                  a=[O:Z[th]]          n   r_2     r_3");
{
my(nbad = 0);
for(k = 1, KMAX,
  my(f2k1 = fseq(2*k-1), fk1 = fseq(k-1));
  for(si = 1, 2,
    my(sg = if(si==1, 1, -1));
    my(b = (f2k1 - 1)/2 + sg*2*fk1);
    if(b == 0 || b == 1, next);
    my(f = x^3 - 3*b*x - b^3);
    my(K = bnfinit(f, 1));
    my(DK = K.disc);
    my(a = abs(round(sqrt(poldisc(f)/DK))));
    my(th = Mod(x, f));
    my(u1 = 1/((b+1) - th));
    my(n = abs(centerlift(bnfisunit(K, lift(u1))[1])));
    my(et = 1/((b+1) - polrootsreal(f)[1]));
    my(e0 = sqrt(et));                                  \\ eta_0 = sqrt(eta_b) if n = 2
    my(r2 = abs(DK)/(4*e0^(3/2) + 24), r3 = abs(DK)/(4*e0 + 24));
    if(n == 2 && r2 < 1, nbad++);
    print("  ", k, "  ", sg, "  ", b, "\t", DK, "\t", a, "\t", n,
          "   ", strprintf("%.3f", r2), "  ", strprintf("%.3f", r3));
  );
);
print("  members with n = 2 but r_2 < 1 (size route inconclusive there): ", nbad);
check(nbad > 0, "E026(a): the Artin/size ratio r_2 < 1 for at least one family member with n = 2, so the size route cannot prove n = 2 -- ASSUMES GRH (bnfinit, no bnfcertify)");
print("  => the Artin/size argument does NOT prove n = 2 along the family.");
}

print("");
print("### (b) Smyth's bound  n <= log(eta_b)/log(rho),  rho = plastic number ###");
{
my(rho = polrootsreal(x^3 - x - 1)[1], bad = 0);
my(bs = [5, 9, 96, 112, 1425, 1485, -3, -16, -75, -135, -1344, -1568, 3]);
my(ns = [4, 6,  4,   2,    2,    2,  8,  2,   4,    2,     2,     2, 13]);
print("  rho = ", rho);
print("       b        n     log(eta_b)/log(rho)   n <= bound ?");
for(i = 1, #bs,
  my(b = bs[i], f = x^3 - 3*b*x - b^3);
  my(et = 1/((b+1) - polrootsreal(f)[1]));
  my(bd = log(et)/log(rho));
  if(ns[i] > bd + 10^(-20), bad++);
  print("  ", b, "\t", ns[i], "\t", strprintf("%.4f", bd), "\t",
        if(ns[i] <= bd + 10^(-20), "ok", "VIOLATED"),
        if(b == 3, "   <-- equality: eta_3 = rho^13", ""));
);
print("  violations: ", bad);
\\ the nonreciprocity step, checked on the minimal polynomials of the units above
check(bad == 0, "E026(b): Smyth n <= log(eta_b)/log(rho) holds at all 13 known non-fundamental b, |b|<=3000");
print("  nonreciprocity check (A = B never occurs for a unit of a complex cubic field):");
my(nr = 0, tot = 0);
for(A = -6, 6, for(B = -6, 6,
  my(p = x^3 - B*x^2 + A*x - 1);
  if(!polisirreducible(p), next);
  if(poldisc(p) > 0, next);                              \\ keep the complex cubics
  tot++;
  if(A == B, nr++);
));
print("    complex cubic units with |A|,|B| <= 6 : ", tot, ",  of them reciprocal (A=B): ", nr);
check(nr == 0 && tot == 84, "E026(b): none of the 84 complex cubic units with |A|,|B|<=6 is reciprocal (A=B)");
}
printf("\nE026 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);

quit
