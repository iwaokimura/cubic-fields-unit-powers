\\ check-c4-elllog.gp --- E154: the integral points of C_4 by elliptic logarithms,
\\ without quadratic Chabauty.  Paper 2, Section 9.7, Remark 9.12 (a second proof of
\\ Theorem D); the constants printed below are the ones quoted there.
\\
\\ Run: gp -q -f -D parisizemax=8000000000 check-c4-elllog.gp < /dev/null > e154.log 2>&1
\\ (a fixed stack of parisize=2G, as in run-all.sh, is also enough; about 5 s)
\\ GLOBALS: FAIL (failure count), LN2N LOGN NBITS NBITS2 (precisions), LN2CACHE (cache).
\\ gp2c -W reports these as undeclared, and does not know the prototype of ellrank;
\\ both are expected.
\\
\\ INPUT FROM PAPER 2 (eq:E): E(Q) = Z P_0 + (Z/2)^2, P_0 = (-3,9).  Rank and torsion
\\ are re-checked in (A); that P_0 generates modulo torsion is proved in (H).
\\
\\ TARGET.  {(A,B) in Z^2 : F_4(A,B) = 0}.  Expected (paper2 sec:tob table plus
\\ the two base points): (-2,1), (-4,11), (0,3), (1,13), (3,3), (1,1), (-1,-1).
\\
\\ THE ARGUMENT (each step is one section below).
\\  (A) [T(CAS)] The four places of C_4 over A = oo, their images Q_i on
\\      E: Y^2 = X^3 - 36X, and R := 2Q_i = (12,-36) = -P_0 + (0,0).  The
\\      pull-back of dX/2Y to H is (3/2) dt/y.
\\  (B) [T(CAS)] Explicit nearness: for |A| >= A0 every integral point lies on
\\      one of four branches B/A^2 = v_i(1/A) (Rouche), and
\\      |delta| <= c1/|A| (Schwarz), where 2*delta is the linear form
\\      L = (2m+1) z(P_1) + k omega_1/2,  P_1 = P_0 + (-6,0) = (18,-72),
\\      phi(P) = m P_0 + tau.
\\  (C) [T(CAS)] Heights: h(X(phi P)) <= 8 log|A| + log CN, Silverman 1990
\\      (Thm 1.1 / Example 2.2), and a certified enclosure of hhat(P_0) from
\\      2^k P_0.  Hence |L| <= 2 c1 exp(-(m^2 hhat - c)/4).
\\  (D) [T(CAS)] Certified enclosures of
\\      z(P_1) = R_F(12,18,24) and omega_1 = 2 R_F(0,6,12), from the duplication
\\      theorem and the monotonicity of R_F, at two precisions.
\\  (E) [T(CAS), with David 1995 Theoreme 2.1] M0.
\\  (F) [T(CAS)] Reduction to M1 by an elementary lemma on one fraction p/q.
\\  (G) [T(CAS)] Search: |A| < A0 directly, |m| <= M1 by pulling back.
\\  (H) [T(CAS), with Silverman's lower bound] P_0 is not divisible in E(Q):
\\      a finite search over the points of small naive height.
\\
\\ EXACTNESS.  Every inequality that bounds something from above or below is
\\ checked in rational arithmetic.  Logarithms, e, pi, square roots and powers
\\ with real exponents enter only through rational enclosures computed here
\\ (series with explicit tails, sqrtint).  Floating point is used only to CHOOSE
\\ parameters and in the [E] cross-checks, which are labelled.

FAIL = 0;

check(c, msg) =
{
  if(c, printf("   [ok]  %s\n", msg), printf("   [FAIL] %s\n", msg); FAIL++);
  return(c);
};

\\ ====================================================================
\\ rational interval arithmetic: an interval is [lo, hi] with rationals
\\ ====================================================================

iv(a) = { return([a, a]); };
ivadd(x, y) = { return([x[1] + y[1], x[2] + y[2]]); };
ivneg(x) = { return([-x[2], -x[1]]); };
ivsub(x, y) = { return(ivadd(x, ivneg(y))); };
ivmul(x, y) =
{
  my(p = [x[1]*y[1], x[1]*y[2], x[2]*y[1], x[2]*y[2]]);
  return([vecmin(p), vecmax(p)]);
};
ivabsmax(x) = { return(max(abs(x[1]), abs(x[2]))); };
ivabsmin(x) =
{
  if(x[1] <= 0 && x[2] >= 0, return(0));
  return(min(abs(x[1]), abs(x[2])));
};

\\ polynomial in one variable at an interval (Horner)
ivpoleval(P, x) =
{
  my(r = iv(0), v = variable(P));
  forstep(k = poldegree(P, v), 0, -1, r = ivadd(ivmul(r, x), iv(polcoef(P, k, v))));
  return(r);
};

\\ --------------------------------------------------------------------
\\ certified constants
\\ --------------------------------------------------------------------

\\ log 2 = sum_{k>=1} 1/(k 2^k); tail after n terms <= 1/((n+1) 2^n)
LN2N = 600;
ln2iv() =
{
  my(s = 0);
  if(type(LN2CACHE) == "t_VEC", return(LN2CACHE));
  for(k = 1, LN2N, s += 1/(k*2^k));
  LN2CACHE = [s, s + 1/((LN2N + 1)*2^LN2N)];
  return(LN2CACHE);
};

\\ atanh(z) = sum z^(2k+1)/(2k+1), 0 <= z < 1; tail after terms k < n is
\\ <= z^(2n+1)/((2n+1)(1-z^2))
atanhiv(z, n) =
{
  my(s = 0);
  for(k = 0, n - 1, s += z^(2*k + 1)/(2*k + 1));
  return([s, s + z^(2*n + 1)/((2*n + 1)*(1 - z^2))]);
};

\\ log of a positive rational x, as an interval: x = 2^e y with 1 <= y < 2,
\\ log y = 2 atanh((y-1)/(y+1)), (y-1)/(y+1) < 1/3
LOGN = 120;
NBITS = 600;
NBITS2 = 900;
logiv(x) =
{
  my(e, y, L2 = ln2iv(), a);
  if(x <= 0, error("logiv: nonpositive argument"));
  e = logint(numerator(x), 2) - logint(denominator(x), 2);
  y = x/2^e;
  while(y >= 2, y /= 2; e++);
  while(y < 1, y *= 2; e--);
  a = atanhiv((y - 1)/(y + 1), LOGN);
  return(ivadd(ivmul(iv(e), L2), [2*a[1], 2*a[2]]));
};

\\ outward roundings to 64 fractional bits, and logs of rounded arguments
rup(x) = { return(ceil(x*2^64)/2^64); };
rdn(x) = { return(floor(x*2^64)/2^64); };
loghi(x) = { return(logiv(rup(x))[2]); };
loglo(x) = { if(rdn(x) <= 0, error("loglo: too small")); return(logiv(rdn(x))[1]); };

\\ e = sum 1/k!, tail after k <= n is <= 2/(n+1)!
eiv() =
{
  my(s = 0, n = 80);
  for(k = 0, n, s += 1/k!);
  return([s, s + 2/(n + 1)!]);
};

\\ atan(1/q) by its alternating series; the partial sums bracket the value
atanrecip(q, n) =
{
  my(s = 0, t);
  for(k = 0, n - 1, s += (-1)^k/((2*k + 1)*q^(2*k + 1)));
  t = (-1)^n/((2*n + 1)*q^(2*n + 1));
  return(if(t > 0, [s, s + t], [s + t, s]));
};

\\ pi = 16 atan(1/5) - 4 atan(1/239)  (Machin)
piiv() =
{
  my(a = atanrecip(5, 120), b = atanrecip(239, 120));
  return(ivsub([16*a[1], 16*a[2]], [4*b[1], 4*b[2]]));
};

\\ square root of a nonnegative rational, as an interval with denominator 2^N
sqrtiv(x, N) =
{
  my(sc = 2^(2*N), lo, hi);
  if(x < 0, error("sqrtiv: negative"));
  lo = sqrtint(floor(x*sc));
  hi = sqrtint(ceil(x*sc));
  if(hi^2 < x*sc, hi++);
  return([lo/2^N, hi/2^N]);
};

\\ ====================================================================
\\ the curves
\\ ====================================================================

c4poly(A, B) =
{
  my(p, pA, pB);
  p = [3, B, B^2 - 2*A];
  for(k = 3, 4, p = concat(p, [B*p[k] - A*p[k-1] + p[k-2]]));
  pA = p[5]; pB = substvec(pA, [A, B], [B, A]);
  return(pB^2 - 3*pB + 9 - 3*pA);
};

F4() = { return(c4poly('A, 'B)); };
gg1() = { return('A^4 + 3*'A^3 - 3*'A^2*'B - 6*'A*'B + 4*'B^2 - 'A + 'B + 1); };
gg2() = { return(3*'A^3 - 'A^2*'B - 6*'A*'B + 4*'B^2 - 'A - 'B + 2); };
gg3() = { return('A^2*'B - 'B^2 - 2*'A + 'B + 1); };
fH() = { return(-18*'t^4 - 36*'t^3 + 54*'t^2 + 72*'t + 9); };
mapX(tt, yy) = { return((6*tt^2 + 24*tt + 6 - 2*yy)/(3*tt^2)); };
mapY(tt, yy) = { return((36*tt^4 + 36*tt^3 + (72 - 24*yy)*tt + 2*(yy - 3)^2)/(9*tt^3)); };

\\ s^w * P(1/s, v/s^2) for P in Z[A,B] of weighted degree <= w
weighted(P, w) =
{
  my(Q = substvec(P, ['A, 'B], [1/'s, 'v/'s^2])*'s^w);
  Q = simplify(Q);
  if(type(Q) != "t_POL", error("weighted: not a polynomial"));
  return(Q);
};

\\ ====================================================================
\\ (A) places at infinity, R, the differential
\\ ====================================================================

sectionA() =
{
  my(G, g, gu, u, N = 8, v, A, B, t, w, y, X, Y, Z, E, Ka, ip, im, R, ok,
     tpol, Q, Kt, Eq, dif, f = fH(), a);
  print("(A) THE PLACES AT INFINITY, THE POINT R, THE DIFFERENTIAL");
  G = weighted(F4(), 8);
  check(type(G) == "t_POL" && poldegree(G, 'v) == 4 && pollead(G, 'v) == 1,
        "G(s,v) = s^8 F_4(1/s, v/s^2) is a polynomial, monic of degree 4 in v");
  g = subst(G, 's, 0);
  check(g == 'v^4 - 16*'v^3 + 20*'v^2 - 8*'v + 1, Str("G(0,v) = ", g));
  check(polisirreducible(g) && polsturm(g) == 4 && poldisc(g) == 2^8*3^2
        && polgalois(subst(g, 'v, 'x))[1] == 4 && polgalois(subst(g, 'v, 'x))[2] == 1
        && polgalois(subst(g, 'v, 'x))[3] == 1,
        "g irreducible, 4 real roots, disc 2^8 3^2, Galois group V_4 (4,+1,1): one Galois orbit of 4 real places");
  \\ branches as power series in s over Q(u)
  u = Mod('u, subst(g, 'v, 'u));
  v = u + O('s^N);
  for(k = 1, 6, v = v - subst(G, 'v, v)/subst(deriv(G, 'v), 'v, v));
  check(subst(G, 'v, v) == O('s^N) && polcoef(lift(v), 1, 's) == 0
        && polcoef(lift(v), 2, 's) == 0,
        "branch v(s) = u + O(s^3) (Newton in Q(u)[[s]])");
  A = 1/'s; B = v/'s^2;
  X = substvec(gg1(), ['A, 'B], [A, B]); Y = substvec(gg2(), ['A, 'B], [A, B]);
  Z = substvec(gg3(), ['A, 'B], [A, B]);
  t = X/Z - Y/Z - 1; w = Y/Z + 1; y = w^2 - 3*(t - 1)^2;
  tpol = lift(polcoef(t, 0, 's));
  check(tpol == -1/2*'u^3 + 17/2*'u^2 - 35/2*'u + 11/2
        && subst(2*'x^4 + 4*'x^3 - 6*'x^2 - 8*'x - 1, 'x, polcoef(t, 0, 's)) == 0,
        "t(P_i) = -u^3/2 + 17u^2/2 - 35u/2 + 11/2, root of 2t^4+4t^3-6t^2-8t-1");
  check(polcoef(t, 1, 's) == 0, "t - t_i vanishes to order >= 2 in s");
  check(valuation(y, 's) == 1, "y has a simple zero in s at each P_i: P_i -> Q'_i = (t_i, 0) on H");
  check(minpoly(polcoef(w, 0, 's)) != 'x && polcoef(w, 0, 's) != 0,
        "w(P_i) != 0, so C_4 -> H is unramified at P_i");
  \\ the points at infinity of H, over Q(a), a^2 = -18
  a = Mod('a, 'a^2 + 18);
  ip = infimage(a, 1); im = infimage(a, -1);
  E = ellinit([0, 0, 0, -36, 0]);
  Ka = nfinit('a^2 + 18);
  Eq = ellinit([0, 0, 0, -36, 0], Ka);
  R = elladd(Eq, ip, im);
  R = [lift(R[1]), lift(R[2])];
  check(R == [12, -36], Str("R = inf_+ (+) inf_- = ", R));
  check(elladd(E, ellneg(E, [-3, 9]), [0, 0]) == [12, -36], "R = -P_0 + (0,0)");
  check(elltors(E)[2] == [2, 2] && ellrank(E)[1] == 1 && ellrank(E)[2] == 1,
        "E(Q) has torsion (Z/2)^2 and rank 1 (ellrank: lower = upper bound)");
  check(ellheight(E, [-3, 9]) > 0, "P_0 has infinite order");
  check(elladd(E, [-3, 9], [-6, 0]) == [18, -72], "P_1 := P_0 + (-6,0) = (18,-72)");
  check(elladd(E, ellneg(E, [18, -72]), [6, 0]) == [12, -36], "R = -P_1 + (6,0)");
  \\ 2 Q_i = R exactly, over Q(t_i)
  Kt = 2*'t^4 + 4*'t^3 - 6*'t^2 - 8*'t - 1;
  Q = [Mod(mapX('t, 0), Kt), Mod(mapY('t, 0), Kt)];
  check(Q[2]^2 == Q[1]^3 - 36*Q[1], "Q_i lies on E over Q(t_i)");
  Q = edouble(Q);
  check([lift(Q[1]), lift(Q[2])] == [12, -36], "2 Q_i = R in E(Q(t_i)), Q_i the image of (t_i, 0) (tangent law by hand)");
  \\ C_4 -> H: with t, w the canonical coordinates, y = w^2 - 3(t-1)^2 satisfies
  \\ y^2 = f(t) on F_4 = 0
  my(tt = (gg1() - gg2() - gg3())/gg3(), ww = (gg2() + gg3())/gg3(), q);
  q = numerator((ww^2 - 3*(tt - 1)^2)^2 - subst(f, 't, tt));
  check(q % F4() == 0, "F_4 divides the numerator of y^2 - f(t): the canonical map lands on H");
  \\ the differential
  dif = deriv(mapX('t, 'y), 't) + deriv(mapX('t, 'y), 'y)*deriv(f, 't)/(2*'y);
  dif = numerator(dif/(2*mapY('t, 'y))*'y - 3/2);
  check(redH(dif) == 0, "the pull-back of dX/(2Y) to H is (3/2) dt/y");
  \\ no real point of the quartic at infinity: the canonical image of a real
  \\ non-base point has g3 != 0
  check(polsturm(subst('w^4 - 6*'w^2 + 27, 'w, 'x)) == 0,
        "w^4 - 6t^2w^2 + 27t^4 has no real zero with t != 0: no real points at infinity on the quartic");
  print("");
  return([G, g]);
};

\\ doubling on Y^2 = X^3 - 36X, Y != 0
edouble(P) =
{
  my(l = (3*P[1]^2 - 36)/(2*P[2]), X2);
  X2 = l^2 - 2*P[1];
  return([X2, l*(P[1] - X2) - P[2]]);
};

\\ y^2 = f reduction of a polynomial in t, y
redH(P) =
{
  my(q = P, f = fH());
  while(poldegree(q, 'y) >= 2,
    my(d = poldegree(q, 'y));
    q = q - polcoef(q, d, 'y)*'y^(d - 2)*('y^2 - f));
  return(simplify(q));
};

\\ image on E of the point at infinity of H with y ~ sg * a * t^2
infimage(a, sg) =
{
  my(gs, sq, yy, X, Y);
  gs = subst(fH(), 't, 1/'e)*'e^4/(-18) + O('e^12);
  sq = sqrt(gs);
  yy = sg*a*sq/'e^2;
  X = mapX(1/'e, yy); Y = mapY(1/'e, yy);
  if(valuation(lift(X), 'e) < 0 || valuation(lift(Y), 'e) < 0, error("infimage: pole"));
  return([polcoef(lift(X), 0, 'e)*Mod(1, 'a^2 + 18), polcoef(lift(Y), 0, 'e)*Mod(1, 'a^2 + 18)]);
};

\\ ====================================================================
\\ (B) nearness: Rouche and Schwarz on the polydisc |s| <= rho, |v - c_i| <= r_i
\\ ====================================================================

\\ sum |coeff| rho^a R^b of a polynomial in s, v
nrm(P, rho, R) =
{
  my(S = 0);
  if(type(P) != "t_POL", return(abs(P)));
  for(a = 0, poldegree(P, 's),
    my(c = polcoef(P, a, 's));
    if(type(c) == "t_POL",
      for(b = 0, poldegree(c, 'v), S += abs(polcoef(c, b, 'v))*rho^a*R^b),
      S += abs(c)*rho^a));
  return(S);
};

\\ the part of P of positive degree in s
spart(P) = { return(P - subst(P, 's, 0)); };

\\ rational isolating intervals of the real roots of a squarefree polynomial,
\\ located by floating point and then CERTIFIED by exact sign changes
isolate(P, bits) =
{
  my(rt = real(polroots(P)), out = vector(#rt), sc = 2^bits);
  rt = vecsort(rt);
  for(i = 1, #rt,
    my(lo = floor(rt[i]*sc)/sc - 1/sc, hi = ceil(rt[i]*sc)/sc + 1/sc);
    if(subst(P, variable(P), lo)*subst(P, variable(P), hi) >= 0, error("isolate: no sign change"));
    out[i] = [lo, hi]);
  for(i = 1, #rt - 1, if(out[i][2] >= out[i+1][1], error("isolate: overlap")));
  return(out);
};

\\ largest rho = 2^-j (j >= 0) for which Rouche holds on the circle |v-c| = r
rouche_rho(Gs, c, r, gLow) =
{
  my(R = abs(c) + r);
  for(j = 0, 60, my(rho = 1/2^j); if(nrm(Gs, rho, R) < gLow, return(rho)));
  return(0);
};

sectionB(G, g) =
{
  my(I, c, eps, Gs, Ghat3, That, What, Ny, best, rhos, out, rho, A0, lam, c1,
     tpoly, fp);
  print("(B) NEARNESS: ROUCHE + SCHWARZ (exact rational bounds)");
  I = isolate(g, 80);
  c = vector(4, i, (I[i][1] + I[i][2])/2);
  eps = vecmax(vector(4, i, (I[i][2] - I[i][1])/2));
  check(eps < 2^-70, Str("the 4 real roots u_i of g isolated in intervals of half-width < 2^-70; centres ~ ",
        apply(x -> precision(x*1., 6), c)));
  Gs = spart(G);
  Ghat3 = weighted(gg3(), 4);
  That = weighted(gg1() - gg2() - gg3(), 4);
  What = weighted(gg2() + gg3(), 4);
  Ny = What^2 - 3*(That - Ghat3)^2;
  check(subst(Ghat3, 's, 0) == 'v - 'v^2, "s^4 g_3(1/s, v/s^2) = v - v^2 + O(s)");
  tpoly = -1/2*'v^3 + 17/2*'v^2 - 35/2*'v + 11/2;
  fp = deriv(fH(), 't);
  \\ per branch: choose r_i among a few candidates to maximise rho_i
  out = vector(4);
  for(i = 1, 4,
    best = [0];
    foreach([1/400, 1/200, 1/100, 1/50, 1/25, 1/12, 1/6, 1/3, 1, 2, 4], r,
      my(ok = 1, gLow, rh);
      for(j = 1, 4, if(j != i && abs(c[i] - c[j]) <= r + 2*eps + 1/1000, ok = 0));
      if(abs(c[i]) <= r + 1/1000 || abs(1 - c[i]) <= r + 1/1000, ok = 0);
      if(!ok, next);
      gLow = (r - eps)*prod(j = 1, 4, if(j == i, 1, abs(c[i] - c[j]) - r - 2*eps));
      rh = rouche_rho(Gs, c[i], r, gLow);
      if(rh > best[1], best = [rh, r, gLow]));
    if(best[1] == 0, error("no admissible r"));
    out[i] = best);
  rho = vecmin(vector(4, i, out[i][1]));
  printf("   chosen: r_i = %s, rho_i = %s; common rho = %s\n",
         vector(4, i, out[i][2]), vector(4, i, out[i][1]), rho);
  \\ certify, with the common rho, every inequality the argument uses
  my(My = vector(4), Mt = vector(4), G3low = vector(4), ti = vector(4), mf = vector(4), tau, lamv);
  for(i = 1, 4,
    my(r = out[i][2], R = abs(c[i]) + r, gLow = out[i][3], uI = [c[i] - eps, c[i] + eps]);
    check(nrm(Gs, rho, R) < gLow,
          Str("branch ", i, ": Rouche on |v - c_", i, "| = ", r, ", |s| <= ", rho,
              " (so exactly one root v_", i, "(s) in the disc)"));
    G3low[i] = (abs(c[i]) - r)*(abs(1 - c[i]) - r) - nrm(spart(Ghat3), rho, R);
    check(G3low[i] > 0, Str("branch ", i, ": |s^4 g_3| >= ", precision(G3low[i]*1., 4), " > 0 on the polydisc"));
    My[i] = nrm(Ny, rho, R)/G3low[i]^2;
    ti[i] = ivpoleval(tpoly, uI);
    Mt[i] = nrm(That, rho, R)/G3low[i] + ivabsmax(ti[i]));
  for(i = 1, 4, for(j = i + 1, 4,
    check(abs(c[i] - c[j]) > out[i][2] + out[j][2] + 2*eps, Str("discs ", i, " and ", j, " are disjoint"))));
  \\ lambda: |t - t_i| <= Mt (|s|/rho)^2 <= Mt/lambda^2 =: tau, with |s| <= 1/A0, A0 >= lambda/rho
  lam = vecmax(vector(4, i, sqrtint(ceil(20*Mt[i])) + 1));
  A0 = ceil(lam/rho);
  for(i = 1, 4,
    my(tauI = Mt[i]/lam^2, J = [ti[i][1] - Mt[i]/lam^2, ti[i][2] + Mt[i]/lam^2], fpI);
    \\ f' on J by subdividing J into 64 pieces
    fpI = vecmin(vector(64, k, ivabsmin(ivpoleval(fp,
            [J[1] + (k - 1)*(J[2] - J[1])/64, J[1] + k*(J[2] - J[1])/64]))));
    mf[i] = fpI;
    check(J[1] > 0 || J[2] < 0, Str("branch ", i, ": 0 is not in t_i +- tau, so t != 0 (D != 0 in (C)) for |A| >= A0"));
    check(mf[i] > 0, Str("branch ", i, ": |f'| >= ", precision(mf[i]*1., 4),
          " on t_i +- ", precision(tauI*1., 3), " (f monotone there, y a coordinate on the arc)")));
  c1 = vecmax(vector(4, i, 3*My[i]/(rho*mf[i])));
  printf("   My = %s\n   Mt = %s\n   lambda = %d, A0 = %d, c1 = %s\n",
         apply(x -> precision(x*1., 4), My), apply(x -> precision(x*1., 4), Mt), lam, A0, precision(c1*1., 6));
  check(A0*rho >= lam && lam >= 1 && c1 > 0,
        "for every integral point with |A| >= A0: it lies on a branch and |delta| <= c1/|A|");
  \\ [E] cross-check against the floating-point delta*A of the scratch run
  check(c1 > 0.56, "[E] c1 exceeds the observed limit |delta*A| -> 0.5577");
  print("");
  return([A0, c1, rho, c, eps, out, vecmax(vector(4, i, abs(c[i]) + out[i][2]))]);
};

\\ log of a positive integer from its bit length: n in [2^(b-1), 2^b)
logZiv(n) =
{
  my(b = #binary(abs(n)), L2 = ln2iv());
  return([(b - 1)*L2[1], b*L2[2]]);
};

\\ naive height of a rational x, as an interval (h(0) = 0)
hiv(x) =
{
  my(n = max(abs(numerator(x)), abs(denominator(x))));
  if(n == 1, return([0, 0]));
  return(logZiv(n));
};

\\ weighted degree (weights 1, 2) of a polynomial in A, B
wdegAB(P) =
{
  my(m = -1);
  for(i = 0, poldegree(P, 'B),
    my(c = polcoef(P, i, 'B));
    if(c != 0, m = max(m, poldegree(c, 'A) + 2*i)));
  return(m);
};

\\ David's quantities as functions of M (see sectionE)
LBf(M, K, ev, h) = { return(max(logZiv(2*M + 2 + K)[2], ev[2]*h[2])); };
rhsf(M, K, ev, h, LE, Cd) =
{
  my(lb = LBf(M, K, ev, h));
  return(Cd*(lb + LE[2])/LE[1]^5*(loghi(lb) + h[2] + LE[2])^3*h[2]^2);
};
lhsf(M, hlo, chi, l2c1) = { return((M^2*hlo - chi)/4 - l2c1); };

\\ ====================================================================
\\ (C) heights
\\ ====================================================================

sectionC(A0, beta) =
{
  my(Xf, N, D, CN, l36, muup, mulo, k = 9, P, Q, hx, hlo, hhi, chi, E, z);
  print("(C) HEIGHTS");
  Xf = mapX((gg1() - gg2() - gg3())/gg3(),
            ((gg2() + gg3())/gg3())^2 - 3*((gg1() - gg2() - gg3())/gg3() - 1)^2);
  N = numerator(Xf); D = denominator(Xf);
  check(wdegAB(N) == 8 && wdegAB(D) == 8
        && D == ('A^4 - 3*'A^2*'B + 'B^2 + 2*'A + 'B - 2)^2,
        "X o phi = N/D, N, D in Z[A,B] of weighted degree 8, D = (A^4 - 3A^2B + B^2 + 2A + B - 2)^2 = (numerator of t)^2");
  \\ |N(A,B)| <= CN |A|^8 when |A| >= A0, |B| <= beta A^2
  CN = 0;
  foreach([N, D], P,
    my(S = 0);
    for(b = 0, poldegree(P, 'B), my(cA = polcoef(P, b, 'B));
      for(a = 0, poldegree(cA, 'A), my(cc = polcoef(cA, a, 'A));
        if(cc, S += abs(cc)*beta^b*A0^(a + 2*b - 8))));
    CN = max(CN, S));
  printf("   CN = %s  (log CN <= %s)\n", precision(CN*1., 6), precision(loghi(CN)*1., 6));
  \\ Silverman 1990, Example 2.2 (y^2 = x^3 + Ax, A = -36):
  \\   -(1/4)h(A) - 2.252 <= hhat_S - h(x)/2 <= (1/4)h(A) + 2.038
  l36 = logiv(36);
  muup = l36[2]/4 + 2038/1000;
  mulo = l36[2]/4 + 2252/1000;
  \\ hhat_S(P_0) = hhat_S(2^k P_0)/4^k
  E = ellinit([0, 0, 0, -36, 0]);
  Q = [-3, 9];
  for(i = 1, k, Q = elladd(E, Q, Q));
  hx = hiv(Q[1]);
  hlo = (hx[1]/2 - mulo)/4^k;
  hhi = (hx[2]/2 + muup)/4^k;
  check(hlo > 0 && hhi - hlo < 1/10^4,
        Str("hhat_S(P_0) = hhat_S(P_1) in [", precision(hlo*1., 8), ", ", precision(hhi*1., 8),
            "]  (from x(2^", k, " P_0), ", #Str(numerator(Q[1])), " digits)"));
  check(abs(ellheight(E, [-3, 9])/2 - (hlo + hhi)/2) < hhi - hlo,
        "[E] PARI's ellheight/2 lies in the enclosure (PARI normalises hhat = 2 hhat_S)");
  \\ m^2 hhat_S(P_0) = hhat_S(phi P) <= h(X)/2 + muup <= 4 log|A| + (log CN)/2 + muup
  chi = loghi(CN)/2 + muup;
  printf("   so |A| >= exp((m^2 hhat - c)/4) with hhat >= %s, c <= %s\n",
         precision(hlo*1., 8), precision(chi*1., 6));
  check(chi > 0, "c computed");
  print("");
  return([hlo, hhi, chi]);
};

\\ ====================================================================
\\ (D) certified enclosures of z(P_1) = R_F(12,18,24), omega_1 = 2 R_F(0,6,12)
\\ ====================================================================

\\ R_F is decreasing in each argument and R_F(a,a,a) = a^(-1/2).  Duplication
\\ (Carlson 1979): R_F(x,y,z) = R_F((x+l)/4, (y+l)/4, (z+l)/4),
\\ l = sqrt(xy) + sqrt(yz) + sqrt(zx).  Rounding l DOWN lowers the arguments,
\\ which can only RAISE R_F: an upper chain.  Rounding UP gives a lower chain.
rfchain(x, y, z, dir, nsteps, N) =
{
  my(a = [x, y, z], l, sq);
  for(i = 1, nsteps,
    sq = vector(3, j, sqrtiv(a[j], N));
    if(dir > 0,
      l = sq[1][1]*sq[2][1] + sq[2][1]*sq[3][1] + sq[3][1]*sq[1][1],
      l = sq[1][2]*sq[2][2] + sq[2][2]*sq[3][2] + sq[3][2]*sq[1][2]);
    a = vector(3, j, (a[j] + l)/4);
    \\ keep the arguments as dyadic rationals of bounded size: round them in
    \\ the safe direction (down for the upper chain, up for the lower one)
    a = vector(3, j, if(dir > 0, floor(a[j]*2^N)/2^N, ceil(a[j]*2^N)/2^N)));
  if(dir > 0,
    return(1/sqrtiv(vecmin(a), N)[1]),
    return(1/sqrtiv(vecmax(a), N)[2]));
};

rfiv(x, y, z, nsteps, N) =
{
  return([rfchain(x, y, z, -1, nsteps, N), rfchain(x, y, z, 1, nsteps, N)]);
};

\\ THE DUPLICATION THEOREM, proved here rather than cited.  For x, y, z >= 0 put
\\ a = sqrt x etc., p(T) = (T+x)(T+y)(T+z) and C: W^2 = p(T).  On C the
\\ T-coordinate of 2Q is p'(T)^2/(4p(T)) - (x+y+z) - 2T, so T(2Q) = 0 iff
\\ N(T) := p'^2 - 4p(x+y+z+2T) = 0, and N(T) is the product of T - r over the
\\ four r = +-ab +-bc +-ca with an even number of minus signs (identity below).
\\ The largest is l = ab+bc+ca.  On the identity component (T >= -min(x,y,z)),
\\ T decreases from oo as the elliptic logarithm z = int_T^oo dT/(2W) goes from 0
\\ to omega/2; the two halves there of P = (0, -sqrt p(0)) (z(P) = z0 in
\\ (0, omega/2]) have z = z0/2 and omega/2 - z0/2 >= z0/2, so the one with the
\\ larger T, namely T = l, has z = z0/2.  Hence int_0^oo = 2 int_l^oo, i.e.
\\ R_F(x,y,z) = 2 R_F(x+l, y+l, z+l) = R_F((x+l)/4, (y+l)/4, (z+l)/4).
\\ (This is Carlson's duplication theorem, Numer. Math. 33 (1979), DLMF 19.26.18.)
dupidentity() =
{
  my(p, N, rr);
  p = ('T + 'a^2)*('T + 'b^2)*('T + 'c^2);
  N = deriv(p, 'T)^2 - 4*p*('a^2 + 'b^2 + 'c^2 + 2*'T);
  rr = ['a*'b + 'b*'c + 'c*'a, 'a*'b - 'b*'c - 'c*'a, -'a*'b + 'b*'c - 'c*'a, -'a*'b - 'b*'c + 'c*'a];
  return(N == prod(i = 1, 4, 'T - rr[i]));
};

sectionD(N) =
{
  my(nst = N\2 + 20, u0, Rh, om, al, E);
  print(Str("(D) ENCLOSURES OF z(P_1) AND omega_1 BY R_F (N = ", N, " bits, ", nst, " duplications)"));
  check(dupidentity(), "p'(T)^2 - 4p(T)(x+y+z+2T) = prod (T - (+-ab +-bc +-ca)): the duplication theorem (proof in the comment)");
  u0 = rfiv(12, 18, 24, nst, N);
  Rh = rfiv(0, 6, 12, nst, N);
  om = [2*Rh[1], 2*Rh[2]];
  al = [u0[1]/Rh[2], u0[2]/Rh[1]];
  check(u0[1] < u0[2] && om[1] < om[2] && al[2] - al[1] < 2^(-N + 20),
        Str("alpha = 2 z(P_1)/omega_1 enclosed to width ", precision((al[2] - al[1])*1., 3)));
  E = ellinit([0, 0, 0, -36, 0]);
  check(abs(ellpointtoz(E, [18, -72]) - (u0[1] + u0[2])/2) < 10^-30
        && abs(E.omega[1] - (om[1] + om[2])/2) < 10^-30,
        "[E] z(P_1) and omega_1 agree with PARI's ellpointtoz and E.omega (the duplication theorem as transcribed)");
  check(al[2] < 1 && al[1] > 0, "0 < alpha < 1, i.e. 0 < z(P_1) < omega_1/2");
  print("");
  return([u0, om, al]);
};

\\ ====================================================================
\\ (E) David's lower bound -> M0
\\ ====================================================================

sectionE(c1, A0, hc, enc) =
{
  my(hlo = hc[1], hhi = hc[2], chi = hc[3], om = enc[2], al = enc[3],
     h, ev, pv, EE, LE, q3, Cd, l2c1, K, j0, Jmax = 400, ok, Cp, M);
  print("(E) DAVID 1995, THEOREME 2.1, WITH k = 2, D = 1 -> M0");
  h = logiv(1728);           \\ h = max{1, h(1:144:0), h(j)} = log 1728
  check(logiv(144)[2] < h[1] && h[1] > 1, "David's h = log 1728 (> log 144 = h(1:g2:g3), > 1)");
  ev = eiv(); pv = piiv();
  EE = 24/5;
  check(EE >= ev[2], "E = 24/5 >= e (condition (4), left)");
  check(EE^2*3*pv[2] <= 4*ev[1]^2*h[1],
        "E <= 2e sqrt(log V_2)/sqrt(3 pi) with log V_2 = h: condition (4) for u_2 = omega_1/2");
  check(al[2] <= 1, "u_1 = z(P_1) <= omega_1/2 = u_2, so (4) holds for u_1 too");
  \\ condition (3): log V_i := h_hi; need hhat_D(gamma_1) = 3 hhat_S(P_1) <= h, and 3pi|u_i|^2/|omega_1|^2 <= 3pi/4 <= h
  check(3*hhi <= h[1] && 3*pv[2]/4 <= h[1],
        "condition (3): log V_1 = log V_2 = h dominates 3 hhat_S(P_1) and 3pi/4");
  LE = logiv(EE);
  \\ C = 2.9e6 * 10^(6k) * 4^(2k^2) * (k+1)^(2k^2+9k+12.3), k = 2; 3^0.3 <= q3
  q3 = 13904/10000;
  check(q3^10 >= 27, "3^(3/10) <= 1.3904");
  Cd = 29/10*10^6*10^12*4^8*3^38*q3;
  l2c1 = loghi(2*c1);
  \\ |k| <= |2m+1| + K, K from |L| <= 2 c1/A0 and |k| omega_1/2 <= |2m+1| u_0 + |L|
  K = ceil(2*(2*c1/A0)/om[1]) + 1;
  \\ log B := max(log(2M+2+K), e h): conditions (1), (2) hold
  printf("   C = %s, log(2 c1) <= %s, K = %d\n", precision(Cd*1., 4), precision(l2c1*1., 5), K);
  \\ large M: for M >= 2^Jmax, x := log B <= M^(1/4), a, b, log x <= x, so
  \\ RHS <= 16 C' M with C' = Cd h^2 / LE^5; and lhs(M) - 16 C' M is increasing and positive
  Cp = Cd*h[2]^2/LE[1]^5;
  \\ for M >= 2^Jmax: log(2M+2+K) <= log(4M) and M^(1/4) - log(4M) is increasing
  \\ once M^(1/4) > 4, so the two pointwise checks below extend to all M >= 2^Jmax
  M = 2^Jmax;
  check(2^(Jmax/4) > 4 && LBf(M, K, ev, h) <= 2^(Jmax/4) && ev[2]*h[1] >= h[2] + LE[2]
        && lhsf(M, hlo, chi, l2c1) > 16*Cp*M && M*hlo/2 > 16*Cp,
        Str("M >= 2^", Jmax, ": log B <= M^(1/4), and (M^2 hhat - c)/4 - log 2c1 > 16 C' M >= RHS, increasing"));
  \\ dyadic: m in [2^j, 2^(j+1)) is impossible if lhs(2^j) > rhs(2^(j+1))
  j0 = Jmax;
  forstep(j = Jmax - 1, 0, -1, if(lhsf(2^j, hlo, chi, l2c1) > rhsf(2^(j + 1), K, ev, h, LE, Cd), j0 = j, break));
  check(j0 < Jmax, Str("every dyadic block [2^j, 2^(j+1)) with ", j0, " <= j < ", Jmax, " is excluded"));
  printf("   M0 = 2^%d ~ %s: every integral point with |A| >= A0 has |m| < M0\n", j0, precision(2.^j0, 4));
  print("");
  return(2^j0);
};

\\ ====================================================================
\\ (F) reduction by continued fractions
\\ ====================================================================

\\ ELEMENTARY LEMMA.  Let p/q be a fraction in lowest terms with q > X.  For
\\ integers N, k with 0 < |N| <= X, Np + kq != 0 (q does not divide N p), so
\\   |N alpha + k| >= |N p/q + k| - |N| |alpha - p/q| >= 1/q - X |alpha - p/q|.
\\ No continued-fraction theory is needed; the convergents only SUPPLY a good
\\ p/q, and the bound is then checked exactly with the enclosure of alpha.
sectionF(M0, c1, hc, enc) =
{
  my(al = enc[3], om = enc[2], cv, X = 2*M0, p, q, err, kap = 0, M1sq, M1,
     chi = hc[3], hlo = hc[1]);
  print("(F) REDUCTION");
  cv = contfracpnqn(contfrac(al[1]), #contfrac(al[1]));
  for(i = 1, #cv,
    p = cv[1, i]; q = cv[2, i];
    if(q <= X, next);
    err = max(abs(al[1] - p/q), abs(al[2] - p/q));
    kap = 1/q - X*err;
    if(kap > 0, break));
  check(kap > 0 && gcd(p, q) == 1 && q > X,
        Str("p/q with q = ", precision(q*1., 4), " > X = 2 M0 and 1/q - X |alpha - p/q| = ",
            precision(kap*1., 4), " > 0"));
  if(kap <= 0, return(0));
  \\ |L|/(omega_1/2) = |(2m+1) alpha + k| >= kap, and <= (4 c1/omega_1) exp(-(m^2 hhat - c)/4)
  M1sq = (chi + 4*loghi(4*c1/(om[1]*kap)))/hlo;
  M1 = sqrtint(floor(M1sq)) + 1;
  check(M1 < M0, Str("|m| <= M1 = ", M1, "  (m^2 <= ", precision(M1sq*1., 6), ")"));
  print("");
  return([M1, [p, q]]);
};

\\ ====================================================================
\\ (G) the search
\\ ====================================================================

\\ integral B with F_4(A0,B) = 0, for an integer A0
introotsB(a) =
{
  my(P = subst(F4(), 'A, a), fa, out = List());
  if(P == 0, error("F_4(a, B) identically zero"));
  fa = factor(P);
  for(i = 1, matsize(fa)[1],
    if(poldegree(fa[i, 1], 'B) == 1,
      my(r = -polcoef(fa[i, 1], 0, 'B)/polcoef(fa[i, 1], 1, 'B));
      if(denominator(r) == 1, listput(out, r))));
  return(Vec(out));
};

\\ integral (A,B) on C_4 over a rational point (t,w) of the quartic
fibre(tt, ww) =
{
  my(e1, e2, rs, out = List(), F = F4());
  e1 = gg1() - (tt + ww)*gg3();
  e2 = gg2() - (ww - 1)*gg3();
  \\ common zeros of e1, e2 = {g = 0} u {e1/g = e2/g = 0}, g = gcd(e1, e2);
  \\ on {g = 0} intersect with F_4 instead (this happens over (-1,3), where g =
  \\ A^2 - 2B + 1: the branch through the base point (1,1))
  my(g = gcd(e1, e2), parts);
  parts = [polresultant(e1/g, e2/g, 'B)];
  if(poldegree(g, 'A) + poldegree(g, 'B) > 0, parts = concat(parts, [polresultant(F, g, 'B)]));
  foreach(parts, rs,
    if(rs == 0, error("fibre: resultant vanishes"));
    foreach(nfroots(, rs), a,
      if(denominator(a) == 1,
        foreach(introotsB(a), b,
          if(substvec(e1, ['A, 'B], [a, b]) == 0 && substvec(e2, ['A, 'B], [a, b]) == 0,
            listput(out, [a, b]))))));
  return(Set(Vec(out)));
};

\\ E -> H, inverse of (eq:HtoE): via check-c4-rational.gp's W-model, then
\\ verified forward
EtoH(P) =
{
  my(EW = ellinit([0, 216, 0, -31104, -2985984]), vch = 0, M, Pw, m, n, tt, yy,
     aa = -18, bb = -36, dd = 72, qq = 3, al = -24);
  if(#P == 1, return([0, -3]));
  if(P == [12, -36], return([0, 3]));
  M = ellminimalmodel(EW, &vch);
  Pw = ellchangepointinv(P, vch);
  m = Pw[1]/al; n = Pw[2]/al;
  tt = (n - bb + dd*m/qq)/(2*(aa - m^2));
  yy = qq + dd*tt/(2*qq) + m*tt^2;
  if(tt == 0 || [mapX(tt, yy), mapY(tt, yy)] != P, error(Str("EtoH failed at ", P)));
  return([tt, yy]);
};

sectionG(A0, M1) =
{
  my(found = List(), E = ellinit([0, 0, 0, -36, 0]), tors = [[0], [0, 0], [-6, 0], [6, 0]],
     cnt = 0, expected, S);
  print(Str("(G) SEARCH: |A| < A0 = ", A0, " directly, |m| <= M1 = ", M1, " by pulling back"));
  for(a = -A0 + 1, A0 - 1, foreach(introotsB(a), b, listput(found, [a, b])));
  printf("   |A| < A0: %s\n", Vec(found));
  S = Set(Vec(found));
  for(m = -M1, M1, for(j = 1, 4,
    my(P = elladd(E, ellmul(E, [-3, 9], m), tors[j]), ty, sv, w);
    ty = EtoH(P);
    sv = 3*(ty[1] - 1)^2 + ty[2];
    if(issquare(sv, &w),
      cnt++;
      foreach(Set([w, -w]), ww,
        foreach(fibre(ty[1], ww), ab, S = setunion(S, [ab]))))));
  printf("   %d rational points (t,w) up to sign with |m| <= M1; integral points: %s\n", cnt, S);
  expected = Set([[-2, 1], [-4, 11], [0, 3], [1, 13], [3, 3], [1, 1], [-1, -1]]);
  foreach(S, ab, check(substvec(F4(), ['A, 'B], ab) == 0, Str(ab, " lies on F_4 = 0")));
  check(S == expected, Str("the integral points of F_4(A,B) = 0 are exactly ", expected));
  print("");
  return(S);
};

\\ ====================================================================
\\ (H) P_0 generates E(Q) modulo torsion (the input eq:E of paper 2)
\\ ====================================================================
\\ Rank 1 and torsion (Z/2)^2 are checked in (A).  Let G generate E(Q) modulo
\\ torsion, P_0 = nG + T with n >= 1.  If n >= 2, hhat_S(G) = hhat_S(P_0)/n^2
\\ <= hhi/4, and Silverman's lower bound hhat_S >= h(x)/2 - mulo gives
\\ h(x(G)) <= 2(hhi/4 + mulo).  Write x(G) = a/d^2 in lowest terms; then
\\ max(|a|, d^2) <= HMAX.  We list every rational point with such an x and check
\\ that each is a torsion point or k P_0 + T with 1 <= |k| <= 5.  A torsion G would
\\ make P_0 torsion; G = k P_0 + T would give hhat(G) = k^2 hhat(P_0) > hhat(P_0)/n^2.
\\ So n = 1.  (The search finds 2 P_0 + T and the like: the bound HMAX is not sharp,
\\ and those points are harmless for the same reason.)
sectionH(hc) =
{
  my(E, l36, mulo, bnd, HMAX, allowed, found, x, T, P0);
  print("(H) P_0 GENERATES E(Q) MODULO TORSION");
  E = ellinit([0, 0, 0, -36, 0]);
  l36 = logiv(36);
  mulo = l36[2]/4 + 2252/1000;
  bnd = 2*(hc[2]/4 + mulo);
  HMAX = floor(exp(bnd*1.)) + 1;
  check(loglo(HMAX + 1) > bnd,
        Str("every x with h(x) <= ", precision(bnd*1., 6), " has max(|a|, d^2) <= HMAX = ", HMAX));
  P0 = [-3, 9];
  allowed = Set([0, 6, -6]);
  foreach([[0], [0, 0], [6, 0], [-6, 0]], T,
    for(k = 1, 5,
      my(R = elladd(E, ellmul(E, P0, k), T));
      if(#R == 2, allowed = setunion(allowed, Set([R[1]])))));
  found = List();
  for(d = 1, sqrtint(HMAX),
    for(a = -HMAX, HMAX,
      if(gcd(a, d) == 1,
        x = a/d^2;
        if(issquare(x^3 - 36*x), listput(found, x)))));
  found = Set(Vec(found));
  printf("   x-coordinates found: %s\n", found);
  check(#setminus(found, allowed) == 0,
        "every rational point with small height is torsion or k P_0 + T (1 <= |k| <= 5), so P_0 is not divisible");
  check(hc[1] > 0, "hhat(P_0) > 0 (P_0 has infinite order)");
  print("");
  return(0);
};

run() =
{
  my(t0 = getwalltime(), rA, rB, rC, rD, rD2, rE, rF, rF2, rG);
  print("=== check-c4-elllog.gp --- E154: integral points of C_4 by elliptic logarithms ===");
  rA = sectionA();
  rB = sectionB(rA[1], rA[2]);
  rC = sectionC(rB[1], rB[7]);
  rD = sectionD(NBITS);
  rD2 = sectionD(NBITS2);
  rE = sectionE(rB[2], rB[1], rC, rD);
  rF = sectionF(rE, rB[2], rC, rD);
  rF2 = sectionF(rE, rB[2], rC, rD2);
  check(rF != 0 && rF2 != 0 && rF[1] == rF2[1] && rF[2] == rF2[2],
        Str("the reduction at ", NBITS, " and ", NBITS2, " bits gives the same p/q and the same M1"));
  rG = sectionG(rB[1], rF[1]);
  sectionH(rC);
  print("========================================================================");
  printf("E154 GATE: %s   (%d failures, %.1f s)\n",
         if(FAIL, "*** RED ***", "GREEN"), FAIL, (getwalltime() - t0)/1000.);
  if(FAIL, quit(1));
  return(FAIL);
};

run();
