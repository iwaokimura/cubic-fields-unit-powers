\\ check-two-logs.gp --- E139/E140: eta_c != eta_b^m for all m >= 31 (m <= 30 is E138,
\\ check-field-iso.gp), for every b != 0, 1: E139 does b < -1 or b > 2, E140 (section H)
\\ adds b = 2 and b = -1.  Uses LMN 1995, Theoreme 3 (p. 289).  Paper 2, Section 10.
\\
\\ Every claim below is checked in EXACT integer / rational arithmetic.  Floating
\\ point is used only to PROPOSE a candidate (a root, an angle), which is then
\\ verified exactly (sign changes, interval bounds).  Transcendental quantities
\\ (pi, log, cos) are enclosed by rational intervals from series with explicit
\\ remainders (Machin for pi, atanh series for log, integer-interval Taylor for cos).
\\
\\ Notation: lam = eta_b, T = 3(b^2+b+1), mu, conj(mu) the complex roots of h_b,
\\ |mu|^2 = 1/lam, psi = arg mu in (0, pi), beta = mu/conj(mu), theta' = |arg beta|
\\ in (0, pi), cos theta' = Re beta = lam (T - lam)^2 / 2 - 1.  theta = 3 theta'/pi.
\\
\\ The chain (written out in paper 2, Section 10; research log E139):
\\  (A) eta_b^m of h-type  <=>  1 - 2cos(2m psi) = RHS(Lam, cos m psi),  Lam = lam^m  [identity, checked here].
\\  (B) m >= 31: |RHS| <= 7 Lam^(-1/2), hence dist(2m psi, +-pi/3 + 2piZ) <= 4.3 lam^(-m/2),
\\      hence |j pi - 3m theta'| <= 13 lam^(-m/2) for an odd j with 1 <= j <= 3m.
\\  (C) LMN Th. 3 with alpha = beta or conj(beta), log alpha = i theta', b1 = j, b2 = 3m:
\\      log|Lambda| >= -8.87 a H^2, a <= 10.98 pi + 1.5 l (l = log lam), H <= Hmax(m)
\\      := max(17, 3 log(3m/40 + 3m/68.9) + 12.08).  So a solution needs G(m, l) <= 0 with
\\      G(m, l) = (m/2) l - log 13 - 8.87 (10.98 pi + 1.5 l) Hmax(m)^2.
\\  (D) Region I: G > 0 for all m >= MCAP and l >= log 9.3 (lam_b >= 9.3 for every b in range).
\\  (E) |b| >= 10^4: dist(2 psi, +-pi/3 + 2piZ) = eps_b with eps_b |b| <= 2.13, so a
\\      solution needs m >= kappa |b|, kappa = (pi/3 - 10^-9)/2.13.
\\      Region II: G(m, l) > 0 for all |b| >= B0, m >= kappa |b|, l >= log(3b^2 - 3|b| + 1).
\\  (F) |b| < B0: for 31 <= m <= MCAP,  ||m theta|| > (13/pi) lam^(-15) >= (13/pi) lam^(-m/2),
\\      certified per b by the best-approximation property of the convergents.
\\ Together with E138 (m <= 30): no b, c in range and m >= 2 with eta_c = eta_b^m.
\\  (H) E140 adds b = 2 and b = -1 (section H), so with E138 the statement holds for every
\\      b != 0, 1 except (b, m) = (-1, 4), where eta_{-1}^4 = eta_5.
\\  (I) E152 (H. Umemoto's proposal): the chain (A)-(C) uses only that lam is a unit > 1 of a
\\      cubic field with one real place.  Every such unit has lam >= rho = 1.3247.. (Smyth), so
\\      for m >= 124, lam^m >= rho^124 > 10^15 and (B), (C) hold with l = log lam >= log 1.3247.
\\      Region IV: G(m, l) > 0 for all m >= M0 = 6082138 and l >= log 1.3247.  Hence lam^m of
\\      h-type forces m < M0; with lam = eta_0 and m = n(b): n(b) < 6082138 for every b != 0, 1.
\\      Paper 2, Section 10 (Proposition 10.20 and Corollary 10.21; Theorem B(iv)).

if(default(parisize) < 800000000, default(parisize, 800000000));

FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };

if(type(B0) != "t_INT", B0 = 163000);       \\ region II starts here; (F) covers 2 <= |b| < B0
if(type(MCAP) != "t_INT", MCAP = 630000);
if(type(M1) != "t_INT", M1 = 1310000);      \\ E140: exponent cap for b = -1 (lam = 3.10..)
if(type(BSCAN) != "t_INT", BSCAN = B0);
if(type(M0) != "t_INT", M0 = 6082138);      \\ E152: exponent cap for every unit (region IV)     \\ Tier 1 wrappers may lower this (then the gate is partial)
P = 320; SC = 2^P;

hb(b) = { return(x^3 - 3*(b^2+b+1)*x^2 + 3*(b+1)*x - 1); };
inrange(b) = { return(b < -1 || b > 2); };

\\ ---------- exact enclosures of transcendental constants ----------

\\ arctan(1/n) in [S_{2N-1}, S_{2N}] (alternating series with decreasing terms)
atanbr(n, N) = {
  my(s = 0, lo = 0);
  for(k = 0, 2*N, s += (-1)^k / ((2*k+1) * n^(2*k+1)); if(k == 2*N-1, lo = s));
  return([lo, s]);
};
pibr() = {
  my(A = atanbr(5, 80), B = atanbr(239, 30));
  return([16*A[1] - 4*B[2], 16*A[2] - 4*B[1]]);
};

\\ log y for rational y in [1, 2]: 2 atanh(z), z = (y-1)/(y+1) in [0, 1/3]; positive terms,
\\ tail after N terms <= 2 z^(2N+1) / ((2N+1)(1 - z^2))
logsmall(y, N) = {
  my(z = (y - 1)/(y + 1), s = 0, zp = z);
  for(n = 0, N - 1, s += zp/(2*n + 1); zp *= z^2);
  return([2*s, 2*s + 2*zp/((2*N + 1)*(1 - z^2))]);
};
\\ log x for rational x >= 1, as [lo, hi]
logbr(x) = {
  my(k = 0, y = x, L2 = logsmall(2, 60), r);
  if(x < 1, error("logbr: x < 1"));
  while(y >= 2, y /= 2; k++);
  r = logsmall(y, 60);
  return([k*L2[1] + r[1], k*L2[2] + r[2]]);
};

\\ cos x for rational x in [0, 4] by integer-interval Taylor arithmetic: [lo, hi]
cosbr(x) = {
  my(Xl = floor(x*SC), Xh = ceil(x*SC), x2l, x2h, ml = SC, mh = SC, sl = SC, sh = SC, k = 0, d);
  if(x < 0 || x > 4, error("cosbr: x out of [0,4]"));
  x2l = (Xl*Xl) \ SC; x2h = -((-Xh*Xh) \ SC);              \\ floor, ceil
  while(1,
    k++; d = (2*k - 1)*(2*k);
    ml = (ml*x2l) \ (SC*d); mh = -((-mh*x2h) \ (SC*d));    \\ magnitude of x^(2k)/(2k)! * SC, floor / ceil
    if(k % 2 == 1, sl -= mh; sh -= ml, sl += ml; sh += mh);
    if(mh == 0 || (k >= 4 && mh < 2), break);
    if(k > 400, error("cosbr: no convergence")));
  \\ Taylor remainder after the x^(2k) term: |R| <= x^(2k+2)/(2k+2)! <= mh_k * x^2/((2k+1)(2k+2)) <= mh_k (x <= 4, k >= 4)
  if(mh > 0 && k < 4, error("cosbr: too few terms"));   \\ mh == 0 only for x == 0, where the remainder is 0
  return([(sl - mh - 1)/SC, (sh + mh + 1)/SC]);
};

\\ ---------- (A) the identity ----------
secA() = {
  my(Tr, s, lhs, rhs);
  print("### (A) h-type condition for u^m as an identity in X = Lam^(1/2), C = cos(m psi) ###");
  Tr = X^2 + 2*C/X; s = X^(-2) + 2*X*C;                 \\ Tr u^m, Tr u^-m
  lhs = 3*Tr - (s^2 - 3*s + 9);
  rhs = X^2*((1 - 2*(2*C^2 - 1)) - (-6*C/X + 9/X^2 - 2*C/X^3 - 3/X^4 + 1/X^6));
  check(lhs - rhs == 0, "3Tr - (s^2-3s+9) = Lam [ (1 - 2cos 2phi) - RHS ]");
  print("   identity: ", lhs - rhs == 0);
  return(0);
};

\\ ---------- (B), (E): the numerical constants of the angle lemmas ----------
secB(PI) = {
  my(s3lo = 866/1000, ok);
  print("### (B)/(E) constants of the angle lemmas ###");
  check(s3lo^2 < 3/4, "sqrt(3)/2 > 0.866");
  \\ refined lemma: for eps <= 0.1, |cos x - 1/2| >= 2 sin(eps/2) sin(pi/3 - 0.05) >= (1 - 0.1^2/24) eps (0.866 - 0.05)
  check((1 - (1/10)^2/24)*(s3lo - 5/100) >= 815/1000, "refined constant 0.815");
  \\ crude step: eps <= pi r and r <= 3.5 Lam^(-1/2), Lam >= 9.3^31: eps <= 0.1
  check(PI[2]*(7/2)/sqrtint(floor((93/10)^31)) < 1/10, "crude step gives eps <= 0.1 (m >= 31)");
  \\ (B): |RHS| <= 6 Lam^-1/2 + 10 Lam^-1 <= 7 Lam^-1/2 for Lam >= 100;  r <= 3.5 Lam^-1/2;  eps <= 3.5/0.815 <= 4.3
  check((7/2)/(815/1000) <= 43/10, "3.5/0.815 <= 4.3");
  check(3*(43/10) <= 13, "3 * 4.3 <= 13");
  \\ (E): m = 1, lam > 10^8 (|b| >= 10^4, as lam >= T - 2 >= 3b^2 - 3|b| + 1): r <= 3 lam^-1/2 + 5 lam^-1, crude: pi r <= 0.1
  check(PI[2]*(3 + 5/10^4)/10^4 < 1/10, "(E) crude step, lam >= 1e8");
  \\ eps |b| <= (3/0.815)(1 + 5/3 lam^-1/2) / sqrt(3 (1 - 1/N)) with N >= 10^4; compare squares
  ok = ((3/(815/1000))*(1 + 5/(3*10^4)))^2 <= (213/100)^2 * 3*(1 - 1/10^4);
  check(ok, "(E) eps_b |b| <= 2.13 for |b| >= 10^4");
  \\ lower bound on eps_b for the 'small m eps' case: eps >= 2.4 lam^-1/2 - 5 lam^-1 > 4.3 lam^-15.5
  check(s3lo*(1 - (5/100)^2/2) - (1/2)*(5/100) >= 8/10, "(E) |cos psi| >= 0.8 when psi is within 0.05 of pi/6 or 5pi/6");
  check(24/10 - 5/10^4 > 43/10 / 10^60, "(E) eps_b >= 2.4 lam^-1/2 - 5 lam^-1 > 4.3 lam^-15.5 = tau");
  return(0);
};

\\ ---------- (C)-(E): the LMN inequality in the two regions ----------
\\ upper bound for Hmax(m), m rational
Hup(m) = { my(L = logbr(3*m/40 + 3*m/(689/10))); return(max(17, 3*L[2] + 1208/100)); };
\\ lower bound for G(m, l) given a lower bound l for log lam (G increases in l when the slope is > 0)
Glo(m, l, PI) = {
  my(H = Hup(m), L13 = logbr(13));
  return(m/2*l - L13[2] - (887/100)*((1098/100)*PI[2] + (15/10)*l)*H^2);
};
\\ upper bound for G(m, l) given an UPPER bound l for log lam (used only to show a test is not vacuous)
Ghi(m, l, PI) = {
  my(L = logbr(3*m/40 + 3*m/(689/10)), H = max(17, 3*L[1] + 1208/100), L13 = logbr(13));
  return(m/2*l - L13[1] - (887/100)*((1098/100)*PI[1] + (15/10)*l)*H^2);
};
\\ the two monotonicity conditions: slope in l, slope in m (worst case at the smallest l)
condmono(m, l, PI) = {
  my(H = Hup(m));
  return([m/2 - (887/100)*(15/10)*H^2 > 0, m > (10644/100)*(((1098/100)*PI[2] + (15/10)*l)/l)*H]);
};

secD(PI) = {
  my(lmin = logbr(93/10)[1], c, g);
  print("### (D) region I: m >= MCAP, any b ###");
  check(sign(subst(hb(-2), x, 93/10)) < 0, "lam_{-2} > 9.3 (sign of h_{-2}(9.3); one real root)");
  \\ every other b in range has T - 2 >= 19 and lam >= T - 2
  check(3*((-3)^2 - 3 + 1) - 2 >= 19 && 3*(3^2 + 3 + 1) - 2 >= 19, "lam_b >= T - 2 >= 19 for b != -2");
  c = condmono(MCAP, lmin, PI); g = Glo(MCAP, lmin, PI);
  printf("   MCAP = %d: slope_l > 0: %d, slope_m > 0: %d, G >= %.3f\n", MCAP, c[1], c[2], g*1.);
  check(c[1] && c[2] && g > 0, "region I");
  \\ discrimination: the same test fails far below MCAP
  check(Glo(MCAP\20, lmin, PI) <= 0, "region I test is not vacuous (fails at MCAP/20)");
  return(0);
};

secE(PI) = {
  my(kap = (PI[1]/3 - 1/10^9)/(213/100), m0, l0, c, g);
  print("### (E) region II: |b| >= B0, m >= kappa |b| ###");
  check(B0 >= 10^4, "B0 >= 10^4 (needed by the eps_b bound)");
  m0 = kap*B0; l0 = logbr(3*B0^2 - 3*B0 + 1)[1];
  c = condmono(m0, l0, PI); g = Glo(m0, l0, PI);
  printf("   B0 = %d, kappa B0 = %.1f: slope_l > 0: %d, slope_m > 0: %d, G >= %.3f\n", B0, m0*1., c[1], c[2], g*1.);
  check(c[1] && c[2] && g > 0, "region II");
  check(Glo(kap*(B0\10), logbr(3*(B0\10)^2)[1], PI) <= 0, "region II test is not vacuous (fails at B0/10)");
  \\ the per-b scan (F) must reach every m in [31, MCAP] that region II does not exclude: m >= kappa B0 is
  \\ excluded only for |b| >= B0, so (F) covers |b| < B0 with MCAP; and region I covers m >= MCAP for all b.
  return(0);
};

\\ ---------- (F): per-b certificate ----------
lambr(b) = {
  my(h = hb(b), r = polrootsreal(h)[1], L = floor(r*SC), lo, hi);
  lo = (L - 4)/SC; hi = (L + 4)/SC;
  if(sign(subst(h, x, lo))*sign(subst(h, x, hi)) >= 0, return(0));
  return([lo, hi]);
};
cfun(y, T) = { return(y*(T - y)^2/2 - 1); };
fnorm(t) = { return(abs(t - round(t))); };

\\ theta-interval certificate on a given rational interval [th1, th2]: every m <= M has
\\ ||m theta|| > (13/pi) lam^(-e); returns [ok, gap, rhs].  Valid for the m in a block
\\ [mlo, M] with e <= mlo/2, since then lam^(-m/2) <= lam^(-e)  (E140: blocks)
cfcertM(th1, th2, lamlo, PI, M, e) = {
  my(cf = contfrac(th1), qp = 0, qc = 1, qn = 0, gap, rhs);
  for(k = 2, #cf, qn = cf[k]*qc + qp; if(qn > M, break); qp = qc; qc = qn);
  if(qn <= M, return([0, "cf too short", 0]));
  gap = fnorm(qc*th1) - M*(th2 - th1);
  rhs = (13/PI[1]) / lamlo^e;
  return([gap > rhs, gap, rhs]);
};
cfcert(th1, th2, lamlo, PI) = { return(cfcertM(th1, th2, lamlo, PI, MCAP, 15)); };

\\ exact enclosure [theta_lo, theta_hi] of theta = 3 theta'/pi, and lam_lo; or [0, reason]
thetabr(b, PI) = {
  my(T = 3*(b^2+b+1), L = lambr(b), w, E, cl, ch, tt, tlo, thi, C1, C2);
  if(L == 0, return([0, "lam bracket"]));
  w = L[2] - L[1];
  E = w^2*(3*L[2] + 2*T)/8;
  cl = min(cfun(L[1], T), cfun(L[2], T)) - E; ch = max(cfun(L[1], T), cfun(L[2], T)) + E;
  tt = acos(((cl + ch)/2)*1.);
  tlo = floor((tt - 2.^(-250))*SC)/SC; thi = ceil((tt + 2.^(-250))*SC)/SC;
  if(!(tlo > 0 && thi < PI[1]), return([0, "theta' range"]));
  C1 = cosbr(thi); C2 = cosbr(tlo);
  if(!(C1[2] <= cl && ch <= C2[1]), return([0, "theta' bracket"]));
  return([3*tlo/PI[2], 3*thi/PI[1], L[1]]);
};

cert(b, PI) = {
  my(t = thetabr(b, PI));
  if(t[1] == 0, return(t));
  return(cfcert(t[1], t[2], t[3], PI));
};

\\ blocks: [[M_1, e_1], ..., [M_k, e_k]] covering 31 <= m <= M_k; block i is
\\ M_{i-1} <= m <= M_i (M_0 = 31), and needs e_i <= M_{i-1}/2.  Returns [ok, reason]
certblocks(b, PI, blocks) = {
  my(t = thetabr(b, PI), mlo = 31, r);
  if(t[1] == 0, return(t));
  for(i = 1, #blocks,
    if(2*blocks[i][2] > mlo, return([0, Str("block ", i, ": e > mlo/2")]));
    r = cfcertM(t[1], t[2], t[3], PI, blocks[i][1], blocks[i][2]);
    if(r[1] != 1, return([0, Str("block ", i, " fails: ", r)]));
    mlo = blocks[i][1]);
  return([1, "ok"]);
};

secF(PI) = {
  my(n = 0, ok = 0, r, t0 = getabstime());
  print("### (F) per-b certificates, 2 <= |b| < B0 ###");
  for(b = -(BSCAN - 1), BSCAN - 1, if(inrange(b),
    n++; r = cert(b, PI);
    if(r[1] == 1, ok++, printf("   b=%d NOT certified: %s\n", b, r))));
  printf("   certified %d of %d (|b| < %d) in %.1f s\n", ok, n, BSCAN, (getabstime() - t0)/1000.);
  check(ok == n, "every b certified");
  check(BSCAN == B0, Str("full range scanned (BSCAN = ", BSCAN, ", B0 = ", B0, ")"));
  return(0);
};

\\ ---------- (G): positive controls / sanity of the exact primitives ----------
secG(PI) = {
  my(r, L2, c);
  print("### (G) controls ###");
  check(PI[1] < 314159265358979/10^14 + 1/10^14 && PI[2] > 314159265358979/10^14, "pi bracket sane");
  r = cosbr(0); check(r[1] <= 1 && 1 <= r[2], "cos 0 = 1 enclosed");
  r = cosbr(PI[2]/3); check(r[1] <= 1/2, "cos(pi_hi/3) <= 1/2 enclosed from below");
  r = cosbr(PI[1]/3); check(r[2] >= 1/2, "cos(pi_lo/3) >= 1/2 enclosed from above");
  L2 = logbr(2); check(L2[1] < 6931471805599454/10^16 && L2[2] > 6931471805599453/10^16, "log 2 bracket sane");
  check(L2[2] - L2[1] < 1/10^50, "log 2 bracket narrow");
  \\ planted: theta = 355/113 + 1e-40, so ||113 theta|| ~ 1.1e-38, must NOT be certified
  c = cfcert(355/113 + 1/10^40, 355/113 + 1/10^40 + 1/10^60, 10, PI);
  check(c[1] == 0, "planted near-rational theta (q = 113) is rejected");
  \\ planted: a 'generic' theta (sqrt 2 interval) must be certified at lam = 10
  c = cfcert(14142135623730950488016887242096980785696/10^40, 14142135623730950488016887242096980785697/10^40, 10, PI);
  check(c[1] == 1, "planted badly-approximable theta (sqrt 2) is accepted");
  return(0);
};

\\ ---------- (H) E140: the two parameters outside paper 1's range, b = 2 and b = -1 ----------
\\ b = 2: lam_2 > 19 (so Lemma iso:linear and region I apply as for |b| >= 3); certificate as in (F).
\\ b = -1: lam = 3.10..; m >= 31 still gives the crude step, region I is redone at l = log lam_{-1}
\\ with its own cap M1, and 31 <= m <= M1 is certified in two blocks (one block fails: the
\\ convergent gap 1.6e-7 is below (13/pi) lam^-15 = 1.7e-7, while the true min ratio is 3e6).
secH(PI) = {
  my(L, llo, c, g, r);
  print("### (H) E140: b = 2 and b = -1 ###");
  check(sign(subst(hb(2), x, 19)) < 0, "lam_2 > 19 (sign of h_2(19); one real root)");
  r = cert(2, PI); printf("   b=2: %s\n", r[1]);
  check(r[1] == 1, "b = 2 certified for 31 <= m <= MCAP");
  L = lambr(-1); check(L != 0, "lam_{-1} bracket");
  llo = logbr(L[1])[1];
  check((35*PI[2])^2 < L[1]^31, "b=-1: crude step 3.5 pi lam^(-31/2) < 1/10");
  check(L[1]^31 >= 100, "b=-1: lam^m >= 100 (|R_m| <= 7 lam^(-m/2))");
  c = condmono(M1, llo, PI); g = Glo(M1, llo, PI);
  printf("   b=-1: M1 = %d, l >= %.6f: slope_l > 0: %d, slope_m > 0: %d, G >= %.3f\n", M1, llo*1., c[1], c[2], g*1.);
  check(c[1] && c[2] && g > 0, "b=-1: region I at l = log lam_{-1}, m >= M1");
  check(Glo(M1\20, llo, PI) <= 0, "b=-1: region test is not vacuous (fails at M1/20)");
  r = certblocks(-1, PI, [[1000, 15], [M1, 500]]); printf("   b=-1 (two blocks): %s\n", r);
  check(r[1] == 1, "b = -1 certified for 31 <= m <= M1");
  r = thetabr(-1, PI); r = cfcertM(r[1], r[2], r[3], PI, M1, 15);
  printf("   b=-1 (one block, expected to fail): ok = %d, gap = %.3g, rhs = %.3g\n", r[1], r[2]*1., r[3]*1.);
  check(r[1] == 0, "b=-1: the single-block certificate fails (the blocks are needed)");
  return(0);
};

\\ ---------- (I): E152, every unit lam > 1, region IV ----------
secI(PI) = {
  my(x0 = 13247/10000, l0 = logbr(x0), c, g, gm);
  print("### (I) E152: any unit lam > 1 of a cubic field with one real place, m >= M0 ###");
  check(subst(x^3 - x - 1, x, x0) < 0, "rho > 1.3247 (x^3 - x - 1 < 0 at 1.3247; one real root)");
  check(x0^124 > 10^15, "lam^m >= 1.3247^124 > 10^15 for m >= 124");
  \\ (B) needs lam^m >= 100 (|R_m| <= 7 lam^(-m/2)) and the crude step 3.5 pi lam^(-m/2) < 1/10
  check((35*PI[2])^2 < 10^15, "crude step: 3.5 pi lam^(-m/2) < 1/10 when lam^m > 10^15");
  check(3*124 > 689/10, "(C): b2/68.9 > 1 for m >= 124, so H increases with d");
  check(3*logbr(124*(3/40 + 3/(689/10)))[1] + 1208/100 > 17, "(C): Hmax(m) is the log branch for m >= 124");
  c = condmono(M0, l0[1], PI); g = Glo(M0, l0[1], PI);
  printf("   M0 = %d, l >= log 1.3247: slope_l > 0: %d, slope_m > 0: %d, G >= %.6f\n", M0, c[1], c[2], g*1.);
  check(c[1] && c[2] && g > 0, "region IV: G > 0 for m >= M0, l >= log 1.3247");
  gm = Ghi(M0 - 1, l0[2], PI);
  printf("   G(M0 - 1, log 1.3247) <= %.6f\n", gm*1.);
  check(gm < 0, "region IV test is not vacuous (fails at M0 - 1)");
  \\ sanity: the bound is attained in spirit by b = 3, eta_0 = rho, n(3) = 13 < M0
  check(13 < M0, "n(3) = 13 < M0");
  return(0);
};

run() = {
  my(PI);
  default(realprecision, 120);
  PI = pibr();
  secA(); secB(PI); secG(PI); secD(PI); secE(PI); secH(PI); secI(PI); secF(PI);
  printf("\nE139+E140+E152 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
  if(FAIL, quit(1));
  return(0);
};

run();
