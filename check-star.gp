\\ check-star.gp --- E019/P2,P3: the explicit condition (star) that rules out q>=5
\\
\\ (star)   |D_K| >= 4*(3(b^2+b+1)+1)^(3/5) + 24 .
\\
\\ Reason: if eta_b = u^q with u>1 and q >= 5, then u <= eta_b^(1/5) and
\\ lem:etasize gives eta_b < P+1 = 3(b^2+b+1)+1, while lem:artin gives
\\ |D_K| <= 4u^3+24 <= 4*eta_b^(3/5)+24 < 4*(P+1)^(3/5)+24.  So (star) forbids
\\ q >= 5.  Together with thm:iff (q=2) and lem:cube (q=3, resp. lem:towernocube)
\\ this makes "eta_b not fundamental <=> eta_b is a square" a theorem for every b
\\ satisfying (star).
\\
\\ P3: in the same situation the b-coprime squarefree kernel t of b^3-4 divides
\\ |D_K|, so t < 4(P+1)^(3/5)+24; since v_2(b^3-4) <= 2 and v_3(b^3-4) <= 1
\\ (cubes are 0,1,8 mod 9), b^3-4 = 2^a*3^e*t*y^2 with 2^a*3^e <= 12, so
\\     y^2 >= |b^3-4| / (12*(4*(P+1)^(3/5)+24)),
\\ i.e. b^3-4 must have a square divisor of size >> |b|^(1.8).

default(realprecision, 60);

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

BND(b) = 4*(3*(b^2+b+1)+1)^(3/5) + 24;

print("### (1) (star) over |b| <= 3000, both signs ###");
{
my(bad = [], cnt = 0);
for(b = -3000, 3000, if(b != 0 && b != 1,
  cnt++;
  if(abs(nfdisc(x^3-3*b*x-b^3)) < BND(b), bad = concat(bad, [b]))));
print("  tested ", cnt, " values;  (star) FAILS exactly for b in ", bad);
check(Set(bad) == Set([-75,-3,3,9]), "E020(c): (star) fails exactly at b = -75,-3,3,9 over |b|<=3000");
}

print();
print("### (2) the four exceptions to (star), with the unit exponent n ###");
print("      (eta_b = eta_0^n; n even <=> eta_b is a square)");
{
my(v = [-75, -3, 3, 9]);
for(i = 1, #v,
  my(b = v[i], f = x^3-3*b*x-b^3, K = bnfinit(f, 1), th = Mod(x, f), n);
  n = bnfisunit(K, 1/((b+1)-th));
  print("  b=", b, "  |D_K|=", abs(K.disc), "  bound=", BND(b),
        "  (star)=", abs(K.disc) >= BND(b),
        "  n=", abs(lift(n[1])), "  square=", abs(lift(n[1])) % 2 == 0,
        "  b^3-4=", factor(b^3-4)));
}

print();
print("### (3) the Pell exceptions all satisfy (star) except -75,-3,9 ###");
{
my(v = [5,9,96,112,1425,1485,20160,20384,-3,-16,-75,-135,-1344,-1568,-19855,-20691]);
for(i = 1, #v,
  my(b = v[i], dk = abs(nfdisc(x^3-3*b*x-b^3)));
  print("  b=", b, "  |D_K|=", dk, "  bound=", BND(b), "  (star)=", dk >= BND(b)));
}

print();
print("### (4) b=3 is a genuine counterexample to \"not fundamental => square\" ###");
{
my(b = 3, f = x^3-3*b*x-b^3, K = bnfinit(f, 1), th = Mod(x,f), n);
n = abs(lift(bnfisunit(K, 1/((b+1)-th))[1]));
print("  b=3: |D_K|=", abs(K.disc), "  a=[O_K:Z[theta]]=",
      sqrtint(abs(poldisc(f)) \ abs(K.disc)),
      "  eta_3 = eta_0^", n, "  (odd, so eta_3 is NOT a square)");
print("  b^3-4 = ", b^3-4, " (prime);  fundamental unit eta_0 = ",
      nfbasistoalg(K, K.fu[1]));
}

print();
print("### (5) P3: q>=5 forces a large square divisor of b^3-4 ###");
print("      v_2(b^3-4) <= 2 and v_3(b^3-4) <= 1 (cubes mod 9 are 0,1,8):");
{
my(bad = 0);
for(b = -3000, 3000, if(b != 0 && b != 1,
  if(valuation(b^3-4, 2) > 2 || valuation(b^3-4, 3) > 1, bad++; print("  FAIL b=", b))));
print("      violations over |b|<=3000: ", bad);
check(bad == 0, "E020(b): v_2(b^3-4)<=2 and v_3(b^3-4)<=1 over |b|<=3000");
print("      cubes mod 9: ", Set(vector(27, i, i^3 % 9)));
}
{
print("  for the (star)-failing b, the forced square divisor y^2:");
my(v = [-75, -3, 3, 9]);
for(i = 1, #v,
  my(b = v[i], N = abs(b^3-4), F = factor(N), t = 1, y = 1);
  for(j = 1, matsize(F)[1],
    if(F[j,1] >= 5 && b % F[j,1] != 0 && F[j,2] % 2 == 1, t *= F[j,1]));
  y = sqrtint(N \ (2^valuation(N,2) * 3^valuation(N,3) * t));
  print("    b=", b, "  b^3-4=", factor(b^3-4), "  t=", t, "  y=", y,
        "  lower bound for y^2 = ", floor(N / (12*BND(b))),
        "  y^2=", y^2, "  ok=", y^2 >= N/(12*BND(b))));
}
{
print("  and the b with |b|<=3000 admitting such a square divisor at all:");
my(lst = []);
for(b = -3000, 3000, if(b != 0 && b != 1,
  my(N = abs(b^3-4), y = 1, F = factor(N));
  for(j = 1, matsize(F)[1],
    if(F[j,1] >= 5 && b % F[j,1] != 0, y *= F[j,1]^(F[j,2] \ 2)));
  if(y^2 >= N/(12*BND(b)), lst = concat(lst, [b]))));
print("    ", lst);
}


print();
print("### (6) thm:closed with k in Z: b_pm(k) = (f_{2k-1}-1)/2 +- 2 f_{k-1} ###");
default(realprecision, 200);
pf(n)  = round(real(((2+sqrt(3))^n-(2-sqrt(3))^n)/(2*sqrt(3))));
plD(n) = round(real(((2+sqrt(3))^n+(2-sqrt(3))^n)/2));
{
my(bp, bm, S = [], T = []);
for(k = -8, 8,
  bp = (pf(2*k-1)-1)/2 + 2*pf(k-1);
  bm = (pf(2*k-1)-1)/2 - 2*pf(k-1);
  print("  k=", k, "  b_+=", bp, "  b_-=", bm,
        if(bp == 0 || bp == 1 || bm == 0 || bm == 1, "   <- degenerate", ""));
  if(bp != 0 && bp != 1, S = concat(S, [bp]));
  if(bm != 0 && bm != 1, S = concat(S, [bm])));
for(n = 0, 8, for(i = 1, 4,
  my(sn = [1,1,-1,-1][i], sg = [1,-1,1,-1][i], A, bb);
  A = 1+sn*plD(n); bb = 1-A^2+2*sg*pf(n)*(A+1);
  if(bb != 0 && bb != 1, T = concat(T, [bb]))));
print("  branch values (n<=8) missing from the closed form (|k|<=8): ", setminus(Set(T), Set(S)));
print("  closed-form values missing from the branches:                ", setminus(Set(S), Set(T)));
print("  degenerate values are exactly b_-(0)=1, b_+(1)=b_-(1)=0, b_-(-1)=0.");
}

print();
print("### (7) P4: thm:mainneg extended to b <= -1 (the case b=-1) ###");
default(realprecision, 40);
{
my(b = -1, f = x^3-3*b*x-b^3, K = nfinit(f), th, eta, P);
th = polrootsreal(f)[1]; eta = 1/((b+1)-th); P = 3*(b^2+b+1);
print("  b=-1: f = ", f, "  theta = ", th, "  eta = ", eta, "  P+1 = ", P+1);
print("        1 < eta < P+1 ? ", eta > 1 && eta < P+1);
print("        D_K = ", K.disc, "   a = ", sqrtint(abs(poldisc(f)) \ abs(K.disc)),
      "   |b^3-4| = ", abs(b^3-4), "   27|b^3-4| = ", 27*abs(b^3-4));
print("        Artin bound 4*eta^{3/2}+24 = ", 4*eta^1.5+24, " < |D_K| = ", abs(K.disc),
      " ? ", 4*eta^1.5+24 < abs(K.disc));
print("        lem:size(ii) at c=1:  27(c^3+4) = 135  >  4(3(c^2-c+1)+1)^{3/2}+24 = ",
      4*(3*(1-1+1)+1)^1.5+24);
print("        Q(1) = ", subst(297*c^6+1296*c^5-3024*c^4+8424*c^3-4032*c^2+2304*c+6032, c, 1));
print("        Q(c) identity check: ",
      (27*c^3+84)^2-16*(3*c^2-3*c+4)^3 == 297*c^6+1296*c^5-3024*c^4+8424*c^3-4032*c^2+2304*c+6032);
print("        eta_{-1} is the fundamental unit (bnfisunit exponent = +-1) ? ",
      abs(lift(bnfisunit(bnfinit(f,1), 1/((b+1)-Mod(x,f)))[1])) == 1);
}
print();
print("### (8) sanity: eta_b IS fundamental for all b<=-1, 3 nmid b, b^3-4 squarefree, |b|<=120 ###");
{
my(bad = 0, cnt = 0);
for(b = -120, -1, if(b % 3 != 0 && issquarefree(b^3-4),
  my(f = x^3-3*b*x-b^3, K = bnfinit(f, 1), n);
  cnt++;
  n = abs(lift(bnfisunit(K, 1/((b+1)-Mod(x,f)))[1]));
  if(n != 1, bad++; print("  NOT FUNDAMENTAL b=", b, "  exponent=", n))));
print("  tested ", cnt, " values;  failures: ", bad);
check(bad == 0, "E020: eta_b fundamental for b<=-1, 3 nmid b, b^3-4 squarefree, |b|<=120");
}

print();
print("### (9) the sporadic b=3 in detail (paper 1, Remark 5.6) ###");
default(realprecision, 40);
{
my(b = 3, f = x^3-3*b*x-b^3, K = bnfinit(f,1), th, eta, rho, n);
th = polrootsreal(f)[1]; eta = 1/((b+1)-th); rho = polrootsreal(x^3-x-1)[1];
n = abs(lift(bnfisunit(K, 1/((b+1)-Mod(x,f)))[1]));
print("  f_3 = ", f, "   disc = ", poldisc(f), " = -27^2*23 ? ", poldisc(f) == -27^2*23);
print("  theta = ", th, "   eta_3 = ", eta);
print("  a = ", sqrtint(abs(poldisc(f)) \ abs(K.disc)), " = b^3 ? ",
      sqrtint(abs(poldisc(f)) \ abs(K.disc)) == b^3,
      "   v_3(a) = floor(3(v_3(b)+1)/2) = ", (3*(valuation(b,3)+1))\2);
print("  D_K = ", K.disc, "   h = ", K.no, "   regulator = ", K.reg,
      "   bnfcertify = ", bnfcertify(K), " (so h and R are GRH-free)");
print("  K_3 = Q[x]/(x^3-x-1) ? ", nfisisom(K, x^3-x-1) != 0,
      "   nfdisc(x^3-x-1) = ", nfdisc(x^3-x-1));
print("  plastic number rho = ", rho, "   rho^3-rho-1 = ", rho^3-rho-1);
print("  eta_3 = rho^13 ? ", abs(eta - rho^13) < 10^(-30), "   (bnfisunit exponent n = ", n, ")");
print("  Artin at rho: 4*rho^3+24 = ", 4*rho^3+24, "  vs |D_K| = 23   ratio = ", (4*rho^3+24)/23);
print("  (star) RHS = ", BND(b), "  vs |D_K| = ", abs(K.disc), "   (star) = ", abs(K.disc) >= BND(b));
print("  rem:powerful RHS = |b^3-4|/(12*BND) = ", abs(b^3-4)/(12*BND(b)), " < 1, so no constraint");
}
print("  -23 is the negative field discriminant closest to 0:");
{
my(S = List([]));
for(a2 = -2, 2, for(a1 = -25, 25, for(a0 = -25, 25,
  my(g = x^3+a2*x^2+a1*x+a0, d);
  if(polisirreducible(g), d = nfdisc(g); if(d < 0, listput(S, d))))));
S = Set(Vec(S));
print("    search |a2|<=2, |a1|,|a0|<=25: ", #S, " distinct negative discriminants;");
print("    the five closest to 0: ", vecsort(Vec(S), , 4)[1..5]);
}

print();
print("### (10) 3 nmid b: |D_K| >= 27 * R * t, with equality up to a power of 2 (rem:abc) ###");
print("     R = prod_{p|b, v_p(b) odd} p  (so |b| = R k^2, R squarefree)");
print("     t = squarefree part of |b^3-4|  (never divisible by 2, since 2|b => v_2(b^3-4)=2)");
{
my(bad = 0, cnt = 0, worst = 0, wb = 0, r);
for(b = -3000, 3000, if(b != 0 && b != 1 && b % 3 != 0,
  my(dk = nfdisc(x^3-3*b*x-b^3), F = factor(abs(b)), G = factor(abs(b^3-4)),
     R = 1, Rodd = 1, t = 1, k);
  cnt++;
  for(j = 1, matsize(F)[1], if(F[j,2] % 2 == 1, R *= F[j,1]; if(F[j,1] > 2, Rodd *= F[j,1])));
  for(j = 1, matsize(G)[1], if(G[j,2] % 2 == 1, t *= G[j,1]));
  k = sqrtint(abs(b) \ R);
  if(abs(b) != R*k^2 || !issquarefree(R), bad++; print("  |b| = R k^2 FAIL b=", b));
  if(t % 2 == 0, bad++; print("  2 | t FAIL b=", b));
  if(abs(dk) < 27*R*t, bad++; print("  |D_K| >= 27 R t FAIL b=", b));
  if(abs(dk) != 27 * 2^valuation(dk,2) * Rodd * t,
     bad++; print("  |D_K| = 27*2^{v_2}*R_odd*t FAIL b=", b));
  if(valuation(dk,3) < 3, bad++; print("  27 | D_K FAIL b=", b));
  r = 1.0*R*t/abs(b)^1.2;
  if(cnt == 1 || r < worst, worst = r; wb = b)));
print("  tested ", cnt, " values with 3 nmid b;   failures: ", bad);
check(bad == 0, "E020(b): |D_K| >= 27 R t, with equality up to a power of 2, 3 nmid b, |b|<=3000");
print("  min R*t/|b|^{6/5} = ", worst, " at b = ", wb,
      "     (>= 4*3^{3/5}/27 = ", 4*3^0.6/27, " suffices for (star))");
}
{
print("  by contrast, for 3 | b the factor 3^3 is absent: v_3(D_K) = [v_3(b) even] in {0,1}:");
my(bad = 0);
for(b = -600, 600, if(b != 0 && b != 1 && b % 3 == 0,
  my(dk = nfdisc(x^3-3*b*x-b^3), w = valuation(b,3));
  if(valuation(dk,3) != (1 - w % 2), bad++; print("   FAIL b=", b))));
print("   mismatches over |b|<=600, 3|b: ", bad);
check(bad == 0, "E020(c): v_3(D_K) = [v_3(b) even] in {0,1} for 3|b, |b|<=600");
print("   the four (star)-failures all have 3 | b: ",
      vector(4, i, my(v = [-75,-3,3,9]); [v[i], v[i] % 3 == 0]));
}
{
print("  ABC bookkeeping at the tightest case b=-100 = -(1)*10^2:");
my(b = -100, G = factor(abs(b^3-4)));
print("   |b^3-4| = ", G, "   R = ", 1, "   k = ", 10, "   t = ", 89,
      "   R*t = 89 vs 0.2864*|b|^{6/5} = ", 0.2864*100^1.2);
print("   ABC quality of (4, 10^6, 1000004): ",
      log(1000004.)/log(1.0*2*10*(2*53*89)));
}

printf("\nE020 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
