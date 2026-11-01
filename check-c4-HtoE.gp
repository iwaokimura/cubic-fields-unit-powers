\\ check-c4-HtoE.gp --- E144: the isomorphism H -> E
\\ of paper 2, equation (16), and the multipliers (m, tau) of the nine rational points.
\\
\\ Run: gp -q check-c4-HtoE.gp < /dev/null
\\
\\ WHY.  The second adversarial review (2026-10-31) found that paper2 named an
\\ isomorphism H -> E without writing it, so m(z) and (eq:sieveout) could not be
\\ reproduced from the paper.  The text said "H carries the rational point
\\ (t,y) = (0,3)", which reads as if (0,3) were the origin.  The map the sieve
\\ actually uses -- check-c4-sieve.gp: toW followed by ellminimalmodel -- sends
\\ (0,-3), the image of the rational point (0,0) of C_4, to the origin.  This
\\ gate fixes the closed form printed in paper2 and checks:
\\
\\   (1) it maps H into E exactly (identity modulo y^2 - f_H);
\\   (2) it IS the sieve's map (difference zero modulo y^2 - f_H);
\\   (3) it has degree 1: x has a single pole, of order 2, at (0,-3); (0,3) goes
\\       to the finite point (12,-36);
\\   (4) the nine rational points of C_4 give the (m, tau) printed in paper2's
\\       control sentence, and those are admissible in (eq:sieveout):
\\       tau = O with m in {0,-1}, tau = (6,0) with m in {0,-1,-2}.
\\
\\ Everything is exact rational arithmetic (power series with rational
\\ coefficients in (3)).  Status of the conclusions: [T(CAS)].

FAIL = 0;

check(c, msg) =
{
  if(c, printf("   [ok]  %s\n", msg), printf("   [FAIL] %s\n", msg); FAIL++);
  return(c);
};

\\ H : y^2 = f_H(t), with y = w^2 - 3(t-1)^2 on C_4 (paper2 Lemma 9.1)
fH() =
{
  return(-18*'t^4 - 36*'t^3 + 54*'t^2 + 72*'t + 9);
};

\\ the closed form of paper2 (eq:HtoE)
mapX() =
{
  return((6*'t^2 + 24*'t + 6 - 2*'y)/(3*'t^2));
};

mapY() =
{
  return((36*'t^4 + 36*'t^3 + (72 - 24*'y)*'t + 2*('y - 3)^2)/(9*'t^3));
};

\\ reduce a rational function in t, y (denominator a power of t times a
\\ constant) modulo y^2 - f_H; returns the reduced numerator
redH(ex) =
{
  my(rr = numerator(ex), f = fH());
  while(poldegree(rr, 'y) >= 2,
    my(dg = poldegree(rr, 'y), lc = polcoef(rr, dg, 'y));
    rr = rr - lc*'y^(dg - 2)*('y^2 - f));
  return(simplify(rr));
};

\\ the sieve's map, verbatim from check-c4-sieve.gp
sieveW(tt, vv) =
{
  my(aa = -18, bb = -36, dd = 72, qq = 3, al = -24, m, n);
  m = (vv - qq - dd*tt/(2*qq))/tt^2;
  n = 2*(aa - m^2)*tt + (bb - dd*m/qq);
  return([al*m, al*n]);
};

\\ (m, tau) of a point R of E(Q), by search over |m| <= 20
mtau(E, R) =
{
  my(P0 = [-3, 9], tors = [[0], [0, 0], [-6, 0], [6, 0]]);
  for(n = -20, 20,
    for(k = 1, 4,
      if(elladd(E, ellmul(E, P0, n), tors[k]) == R, return([n, tors[k]]))));
  return(0);
};

\\ the image of (0, y0) on H, y0 = 3 or -3, by expanding along the branch
imageAtZero(sg) =
{
  my(ys = sg*sqrt(subst(fH(), 't, 'e) + O('e^12)), A, B);
  A = subst(subst(mapX(), 'y, ys), 't, 'e);
  B = subst(subst(mapY(), 'y, ys), 't, 'e);
  return([valuation(A, 'e), valuation(B, 'e), A, B]);
};

run() =
{
  my(t0 = getwalltime(), E, EW, vch, M, S, im, pts, R, obs, mO, m6);
  print("=== check-c4-HtoE.gp --- E144: the isomorphism H -> E of paper2 ===");
  E = ellinit([0, 0, 0, -36, 0]);

  print("(1) THE CLOSED FORM MAPS H INTO E");
  check(redH(mapY()^2 - mapX()^3 + 36*mapX()) == 0,
        "Y^2 - X^3 + 36X = 0 modulo y^2 - f_H, identically in t");

  print("(2) IT IS THE MAP THE SIEVE USES");
  EW = ellinit([0, 216, 0, -31104, -2985984]);
  vch = 0;
  M = ellminimalmodel(EW, &vch);
  check(M[1..5] == E[1..5], Str("the minimal model of check-c4-sieve.gp's EW is "
        "y^2 = x^3 - 36x (change of variables ", vch, ")"));
  S = ellchangepoint(sieveW('t, 'y), vch);
  check(redH(S[1] - mapX()) == 0 && redH(S[2] - mapY()) == 0,
        "check-c4-sieve.gp's toW followed by ellminimalmodel equals (eq:HtoE) on H");

  print("(3) DEGREE 1, AND WHERE t = 0 GOES");
  im = imageAtZero(-1);
  check(im[1] == -2 && im[2] == -3,
        "at (0,-3), the image of (0,0) of C_4: x has a pole of order 2 and y of "
        "order 3, so (0,-3) goes to the origin");
  im = imageAtZero(1);
  check(im[1] >= 0 && im[2] >= 0
        && [polcoef(im[3], 0, 'e), polcoef(im[4], 0, 'e)] == [12, -36],
        "(0,3) goes to the finite point (12,-36), which is -P_0 + (0,0)");
  check(mtau(E, [12, -36]) == [-1, [0, 0]], "(12,-36) = -P_0 + (0,0)");
  \\ poles of x on H: 3t^2 x is a polynomial in t, y, so poles lie over t = 0
  \\ or at infinity.  At infinity y/t^2 is bounded (y^2 = f_H has degree 4), and
  \\ substituting y = t^2 u shows 3t^2 x has t-degree 2, so x stays bounded.
  \\ Over t = 0: order 2 at (0,-3), none at (0,3).  So x has degree 2 on H, as
  \\ on E, and the map has degree 1.
  check(type(3*'t^2*mapX()) == "t_POL"
        && poldegree(subst(3*'t^2*mapX(), 'y, 't^2*'u), 't) == 2,
        "3t^2 x = 6t^2 + 24t + 6 - 2y is a polynomial of t-degree 2 after "
        "y = t^2 u: x is regular off t = 0 and bounded at infinity, so its only "
        "pole is the double pole at (0,-3); the map has degree 1, an "
        "isomorphism of genus-1 curves");

  print("(4) THE NINE RATIONAL POINTS: (m, tau)");
  \\ [t, w, expected m, expected tau]
  pts = [[1, 3, 0, [6, 0]], [1, -3, 0, [6, 0]], [-1, 3, -1, [6, 0]],
         [-1, -3, -1, [6, 0]], [-2, 6, -1, [0]], [-2, -6, -1, [0]],
         [-1/11, 15/11, -2, [6, 0]], [-1/11, -15/11, -2, [6, 0]]];
  obs = vector(#pts);
  for(k = 1, #pts,
    my(tt = pts[k][1], ww = pts[k][2], yy, mt);
    check(ww^4 - 6*(tt - 1)^2*ww^2 + 27*tt*(tt^3 - 4) == 0,
          Str("(", tt, ",", ww, ") lies on C_4"));
    yy = ww^2 - 3*(tt - 1)^2;
    R = [subst(subst(mapX(), 'y, yy), 't, tt), subst(subst(mapY(), 'y, yy), 't, tt)];
    mt = mtau(E, R);
    obs[k] = mt;
    check(ellisoncurve(E, R) && mt == [pts[k][3], pts[k][4]],
          Str("(", tt, ",", ww, ") -> H (", tt, ",", yy, ") -> E ", R,
              ":  (m, tau) = (", pts[k][3], ", ", pts[k][4], ")")));
  check(imageAtZero(-1)[1] < 0, "(0,0) -> H (0,-3) -> origin:  (m, tau) = (0, O)");

  print("(5) AGREEMENT WITH (eq:sieveout)");
  \\ the observed m, sorted by tau; (0,0) of C_4 contributes (0, O) by (3)
  mO = Set(concat([0], [o[1] | o <- obs, o != 0 && o[2] == [0]]));
  m6 = Set([o[1] | o <- obs, o != 0 && o[2] == [6, 0]]);
  check(#select(o -> o == 0, obs) == 0, "every one of the eight points was found");
  check(mO == Set([0, -1]) && m6 == Set([0, -1, -2])
        && #select(o -> o != 0 && (o[2] == [0, 0] || o[2] == [-6, 0]), obs) == 0,
        Str("observed: tau = O with m in ", mO, ", tau = (6,0) with m in ", m6,
            ", and no point with tau = (0,0) or (-6,0) -- exactly the residues "
            "(eq:sieveout) allows"));

  print("========================================================================");
  printf("E144 GATE: %s   (%d failures, %.1f s)\n",
         if(FAIL, "*** RED ***", "GREEN"), FAIL, (getwalltime() - t0)/1000.);
  if(FAIL, quit(1));
  return(FAIL);
};

run();
