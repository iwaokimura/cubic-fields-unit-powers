\\ check-field-iso.gp --- E138: is b -> K_b injective?  (K_b = K_b' => b = b' ?)
\\
\\ Reformulation [T]: K_b has one real embedding, so a field isomorphism preserves
\\ "u > 1".  Hence for b != b',  K_b = K_b'  <=>  K_b contains a unit u > 1 with
\\ charpoly h_b'(X) = X^3 - 3(b'^2+b'+1) X^2 + 3(b'+1) X - 1  (u is the image of
\\ eta_b').  Writing eta_b = eta_0^k, eta_b' = eta_0^k' (k = n(b), k' = n(b') in
\\ paper2's notation), b != b' forces k != k'.
\\ "u is of h-type"  <=>  charpoly(u) = X^3 - T X^2 + S X - 1 with 3T = S^2 - 3S + 9
\\ (then 3 | S and c = S/3 - 1).  This is paper2's F_q restricted to u^q.
\\
\\ Two ranges of b:  paper1 / Umemoto's observation  "b < -1 or b > 2"  (inrange), and
\\ paper2  "b != 0, 1"  (okb), which adds b = -1 and b = 2.
\\ Found in the first Tier 1 run (2026-10-18): K_{-1} = K_5, eta_5 = eta_{-1}^4.
\\ So the map is NOT injective on paper2's range; the question is for paper1's range.
\\
\\ Sections
\\  (1) sanity: f_b and h_b define the same field (polredabs), |b| <= NSAME.
\\  (2) P_m(b) := S^2 - 3S + 9 - 3T for charpoly(eta_b^m), as a polynomial in b.
\\      P_1 == 0 identically; P_m = paper2's F_m(3(b+1), 3(b^2+b+1)) (independent
\\      Newton-identity computation); integer roots of P_m for 2 <= m <= MMAX.
\\      A root b with b != 0, 1 means eta_b^m = eta_c, c = S(b)/3 - 1.
\\      Expected: the single pair (m, b, c) = (4, -1, 5).
\\  (3) the fields with n(b) >= 3 and |b| <= 10^30
\\      (paper2 Thm C: b in {-75,-3,3,5,9,96}):
\\      eta_0 = the positive n(b)-th root of eta_b in K_b (exact: eta_0^n == eta_b),
\\      and for 1 <= j <= JMAX, is eta_0^j of h-type, and for which c?
\\      Expected: only j = n(b), c = b; and for b = 5 also j = 1, c = -1.
\\  (4) polredabs collisions among f_b, |b| <= NCOLL.  Positive control: h_b planted
\\      for inrange |b| <= 20 must each collide with f_b.  Expected collisions:
\\      none on paper1's range, exactly {-1, 5} on paper2's range.
\\
\\ Inputs from paper2 (not re-proved here): n(b) for the six b of (3) (Thm C).

if(default(parisize) < 400000000, default(parisize, 400000000));

FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };

if(type(NSAME) != "t_INT", NSAME = 200);
if(type(MMAX) != "t_INT", MMAX = 30);
if(type(JMAX) != "t_INT", JMAX = 30);
if(type(NCOLL) != "t_INT", NCOLL = 1000);

fb(b) = { return(x^3 - 3*b*x - b^3); };
hb(b) = { return(x^3 - 3*(b^2+b+1)*x^2 + 3*(b+1)*x - 1); };
okb(b) = { return(b != 0 && b != 1); };
inrange(b) = { return(b < -1 || b > 2); };

\\ [is_h, c] for a monic cubic cp in x
htype(cp) = {
  my(T = -polcoef(cp, 2, x), S = polcoef(cp, 1, x), N = -polcoef(cp, 0, x));
  if(N != 1 || 3*T != S^2 - 3*S + 9, return([0, 0]));
  return([1, S/3 - 1]);
};

sec1() = {
  my(bad = 0);
  print("### (1) f_b and h_b define the same field ###");
  for(b = -NSAME, NSAME, if(okb(b), if(polredabs(fb(b)) != polredabs(hb(b)), bad++)));
  printf("   mismatches for |b| <= %d: %d\n", NSAME, bad);
  check(bad == 0, "f_b vs h_b");
  return(0);
};

\\ paper2 (eq:newton): p_0 = 3, p_1 = B, p_2 = B^2 - 2A, p_{k+1} = B p_k - A p_{k-1} + p_{k-2}
pnewton(q, A, B) = {
  my(p = vector(q + 1));
  p[1] = 3; if(q >= 1, p[2] = B); if(q >= 2, p[3] = B^2 - 2*A);
  for(k = 2, q - 1, p[k+2] = B*p[k+1] - A*p[k] + p[k-1]);
  return(p[q+1]);
};
Fq(q, A, B) = { my(s = pnewton(q, B, A)); return(s^2 - 3*s + 9 - 3*pnewton(q, A, B)); };

\\ [P_m(t), S(t)]
Pm(m) = {
  my(cp = charpoly(Mod(x, hb(t))^m, x), T = -polcoef(cp, 2, x), S = polcoef(cp, 1, x));
  return([S^2 - 3*S + 9 - 3*T, S]);
};

introots(P) = {
  my(R = [], f = factor(P), r);
  for(i = 1, #f~, if(poldegree(f[i,1], t) == 1,
    r = -polcoef(f[i,1], 0, t)/polcoef(f[i,1], 1, t);
    if(type(r) == "t_INT", R = concat(R, [r]))));
  return(R);
};

sec2() = {
  my(PS, R, hits = [], c);
  print("### (2) eta_b^m of h-type: integer roots of P_m(b) ###");
  check(Pm(1)[1] == 0, "P_1 == 0 identically");
  for(m = 2, MMAX,
    PS = Pm(m);
    check(PS[1] == Fq(m, 3*(t+1), 3*(t^2+t+1)), Str("P_", m, " = paper2 F_", m, " on the family"));
    check(PS[1] != 0, Str("P_", m, " != 0"));
    R = select(r -> okb(r), introots(PS[1]));
    for(i = 1, #R, c = subst(PS[2], t, R[i])/3 - 1; hits = concat(hits, [[m, R[i], c]])));
  printf("   2 <= m <= %d, roots b != 0,1 as [m, b, c] (eta_b^m = eta_c): %s\n", MMAX, hits);
  check(hits == if(MMAX >= 4, [[4, -1, 5]], []), "only (m, b, c) = (4, -1, 5)");
  check(#select(h -> inrange(h[2]), hits) == 0, "no root in paper1's range");
  return(0);
};

\\ eta_0 for b with known n = n(b): the root r of X^n = eta_b in K_b with real embedding > 0.
\\ Chosen EXACTLY (2026-10-28; it used to be a floating-point evaluation at the real
\\ root): a unit u of the complex cubic field K_b has N(u) = u |sigma(u)|^2, so the
\\ real embedding of u has the sign of N(u) = +-1.  So the positive root is the one of
\\ norm +1, and then u^n = eta_b > 1 forces u > 1.
eta0(b, n) = {
  my(fy = subst(fb(b), x, y), nf = nfinit(fy), eta = Mod(1/((b+1) - y), fy),
     R = nfroots(nf, x^n - lift(eta)), cand = []);
  for(i = 1, #R, if(nfeltnorm(nf, R[i]) == 1, cand = concat(cand, [Mod(R[i], fy)])));
  check(#cand == 1, Str("b=", b, ": exactly one ", n, "-th root of eta_b of norm +1 (hence > 0, hence > 1)"));
  check(cand[1]^n == eta, Str("b=", b, ": eta_0^n == eta_b exactly"));
  return(cand[1]);
};

sec3() = {
  my(SP = [[-75,4],[-3,8],[3,13],[5,4],[9,6],[96,4]], e0, ht, hits, want);
  print("### (3) fields with n(b) >= 3: which eta_0^j are of h-type ###");
  for(i = 1, #SP,
    e0 = eta0(SP[i][1], SP[i][2]); hits = [];
    for(j = 1, JMAX, ht = htype(charpoly(e0^j, x)); if(ht[1], hits = concat(hits, [[j, ht[2]]])));
    printf("   b=%4d n=%2d: h-type powers [j, c] = %s\n", SP[i][1], SP[i][2], hits);
    want = if(SP[i][1] == 5, [[1, -1], [4, 5]], [[SP[i][2], SP[i][1]]]);
    check(hits == want, Str("b=", SP[i][1], ": h-type powers as expected")));
  return(0);
};

\\ pairs of labels with equal polredabs; L = [[key, label], ...]
collide(L) = {
  my(pairs = []);
  L = vecsort(L, 1);
  for(i = 2, #L, if(L[i][1] == L[i-1][1], pairs = concat(pairs, [[L[i-1][2], L[i][2]]])));
  return(pairs);
};

sec4() = {
  my(L = List(), Lin, Lc, C, nplant = 0, got);
  print("### (4) polredabs collisions among the K_b ###");
  for(b = -NCOLL, NCOLL, if(okb(b), listput(L, [Vec(polredabs(fb(b))), b])));
  L = Vec(L);
  Lin = select(e -> inrange(e[2]), L);
  Lc = Lin;
  for(b = -20, 20, if(inrange(b), nplant++; Lc = concat(Lc, [[Vec(polredabs(hb(b))), Str("h", b)]])));
  got = #select(p -> type(p[1]) == "t_STR" || type(p[2]) == "t_STR", collide(Lc));
  printf("   positive control (h_b planted, inrange |b| <= 20): %d of %d found\n", got, nplant);
  check(got == nplant, "positive control finds every planted duplicate");
  C = collide(Lin);
  printf("   paper1 range, |b| <= %d (%d fields): collisions %s\n", NCOLL, #Lin, C);
  check(C == [], "no two K_b coincide on paper1's range");
  C = collide(L);
  printf("   paper2 range, |b| <= %d (%d fields): collisions %s\n", NCOLL, #L, C);
  check(#C == 1 && vecsort(C[1]) == [-1, 5], "on paper2's range only K_{-1} = K_5");
  return(0);
};

run() = {
  sec1(); sec2(); sec3(); sec4();
  printf("\nE138 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
  if(FAIL, quit(1));
  return(0);
};

run();
