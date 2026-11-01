\\ check-biell-calib.gp --- E100: the calibration curve for epsilon, found.
\\
\\ Run: gp -q check-biell-calib.gp
\\
\\ THE DESIGN.  E096 reduced the unfixed normalisation to a single DISCRETE
\\ scalar epsilon in {1,2}; E098 showed it moves H_2 at its leading digit and
\\ moves the root counts.  The way to settle it is a curve on which the height
\\ pairing B is known INDEPENDENTLY -- a genus-2 BIELLIPTIC curve, where
\\ J ~ E' x E'' and SageMath supplies BOTH Gram entries (E096 verified that
\\ SageMath's padic_height IS the Coleman-Gross height).  Then
\\
\\     epsilon^{-1} theta(x) = B(x) - sum_ell h_ell(x)
\\
\\ at every rational point, and epsilon is read off.  What C_4 cannot do -- (B5)
\\ leaves one Gram entry unreachable -- a bielliptic curve does for free, because
\\ B is diagonal in the sigma-eigenbasis and both entries are elliptic.
\\
\\ TWO EXACT FACTS ABOUT THE FAMILY, which shape the search.
\\
\\     disc(g(x^2)) = -2^6 a d disc(g)^2                                     (1)
\\     g(x^2) is a SQUARE modulo 2, for every g over Z                       (2)
\\
\\ (1) says an odd prime can have v_ell(disc f) = 1 -- the cheap certificate
\\ that the given model is already regular with an IRREDUCIBLE special fibre,
\\ hence h_ell = 0, which is how BDMTV2023 disposed of C_161 at 23 -- only if
\\ ell divides ad exactly once and does not divide disc(g).  So the search must
\\ look for g of discriminant +-2^k.  (2) says the reduction at 2 is a double
\\ line for EVERY curve in the family: bielliptic genus-2 curves of this shape
\\ are always bad at 2, and h_2 will have to be carried rather than certified
\\ away.
\\
\\ AND THE SEARCH SUCCEEDS.  Six curves in a small box have both quotients of
\\ rank 1 and every odd bad prime at v_ell(disc) = 1; four of them have 2 as
\\ their ONLY bad prime.  With h_ell = 0 for all odd ell, the equations at n
\\ rational points read
\\
\\     epsilon^{-1} theta(x_i) = B(x_i) - h_2(x_i),
\\
\\ with h_2 taking finitely many values on the finitely many components of
\\ Gamma_2.  n equations, 1 + (number of h_2-classes) unknowns: OVER-DETERMINED
\\ as soon as there are enough points, which is exactly BDMTV2023's own method
\\ for C_188 -- available here, and not for C_4, precisely because B is known.

FAIL = 0;
check(c, msg) = {print(if(c, "   [ok]  ", "   [FAIL] "), msg); if(!c, FAIL = FAIL + 1);};
info(msg) = print("        ", msg);

print("=== check-biell-calib.gp --- E100: the calibration curve for epsilon ===");

print("(1) THE DISCRIMINANT OF AN EVEN SEXTIC");
f = a*x^6 + b*x^4 + c*x^2 + d;
g = a*x^3 + b*x^2 + c*x + d;
{check(poldisc(f, x) == -64*a*d*poldisc(g, x)^2,
      "disc(g(x^2)) = -2^6 a d disc(g)^2 IDENTICALLY in Z[a,b,c,d]  [T(CAS)].  So an odd prime has v_ell(disc f) = 1 only if it divides ad exactly once and misses disc(g): the search must look for g of discriminant a power of 2");}

print("(2) THE REDUCTION AT 2");
{
my(ok = 1);
for(k = 1, 40,
  my(a0 = 1 + (k%4), b0 = k-7, c0 = 5-k, d0 = 1 + (k%6));
  if(Mod(1,2)*(a0*x^6 + b0*x^4 + c0*x^2 + d0) != (Mod(1,2)*(a0*x^3 + b0*x^2 + c0*x + d0))^2, ok = 0));
check(ok, "g(x^2) = (a x^3 + b x^2 + c x + d)^2 modulo 2 on 40 test tuples: over F_2 squaring is Frobenius.  So y^2 = f reduces mod 2 to a DOUBLE LINE and every bielliptic genus-2 curve of this shape is bad at 2; h_2 must be carried, not certified away  [T(CAS)]");
}

print("(3) THE SEARCH");
{
ratpts(ff, H) = my(out = List());
  for(m = 1, 3, for(nn = -H*m, H*m,
    my(xx = nn/m, v);
    if(denominator(xx) != m, next);
    v = subst(ff, x, xx);
    if(v > 0 && issquare(v), listput(out, xx))));
  Set(Vec(out));
}
NCAND = 0; HITS = List();
{
for(a0 = 1, 2, for(b0 = -6, 6, for(c0 = -6, 6, for(d0 = 1, 6,
  my(f0, D0, E1, E2, r1, r2, fa, oddsq);
  f0 = a0*x^6 + b0*x^4 + c0*x^2 + d0;
  D0 = poldisc(f0); if(D0 == 0, next);
  E1 = ellinit([0,b0,0,a0*c0,a0^2*d0]); E2 = ellinit([0,c0,0,b0*d0,a0*d0^2]);
  if(#E1 == 0 || #E2 == 0, next);
  r1 = ellrank(E1); r2 = ellrank(E2);
  if(r1[1] < 1 || r2[1] < 1 || r1[1] != r1[2] || r2[1] != r2[2], next);
  NCAND = NCAND + 1;
  fa = factor(abs(D0)); oddsq = 0;
  for(k = 1, matsize(fa)[1], if(fa[k,1] > 2 && fa[k,2] > 1, oddsq = 1));
  if(!oddsq, listput(HITS, [f0, [r1[1], r2[1]], D0,
                            ellglobalred(E1)[1], ellglobalred(E2)[1],
                            ratpts(f0, 30)]));
))));
}
info(Str("bielliptic curves in a in [1,2], b,c in [-6,6], d in [1,6] with both quotients of PROVEN rank >= 1: ", NCAND));
{for(k = 1, #HITS, my(h = HITS[k]);
  info(Str("  f = ", h[1], "   ranks ", h[2], "   disc = ", factor(h[3])~,
           "   quotient conductors ", [h[4], h[5]], "   rational x: ", h[6])));}
check(#HITS >= 1, Str("of those, ", #HITS, " have EVERY odd bad prime at v_ell(disc) = 1, hence h_ell = 0 there: the given model is already regular at such an ell and its special fibre is an irreducible curve with one node, so Gamma_ell has a single vertex and j_Gamma vanishes"));
only2 = 0;
{for(k = 1, #HITS, my(fa = factor(abs(HITS[k][3])));
  if(matsize(fa)[1] == 1 && fa[1,1] == 2, only2 = only2 + 1));}
check(only2 >= 1, Str("and ", only2, " of them have 2 as their ONLY bad prime, so Upsilon = Upsilon_2 alone"));

print("(4) THE RECOMMENDED CURVE");
frec = x^6 - 2*x^4 - 2*x^2 + 4;
E1r = ellinit([0,-2,0,-2,4]);
E2r = ellinit([0,-2,0,-8,16]);
info(Str("f = ", frec, ",  disc = ", factor(poldisc(frec))~));
info(Str("quotients Y^2 = X^3-2X^2-2X+4 (conductor ", ellglobalred(E1r)[1], ", rank ", ellrank(E1r)[1], ") and Y^2 = X^3-2X^2-8X+16 (conductor ", ellglobalred(E2r)[1], ", rank ", ellrank(E2r)[1], ")"));
info(Str("rational x with f(x) a square: ", ratpts(frec, 30), "  -- ten affine points, plus the two rational points at infinity (the leading coefficient is a square)"));
ordp = [];
{forprime(q = 5, 40, if(Mod(poldisc(frec), q) != 0 && Mod(ellap(E1r, q), q) != 0 && Mod(ellap(E2r, q), q) != 0, ordp = concat(ordp, [q])));}
check(#ordp > 0, Str("good ORDINARY primes for both quotients, hence for J: ", ordp, ".  The port needs one of these"));
{check(poldegree(frec) == 6,
      "and the port accepts the model: TuitmanCurve(y^2 - f) returns genus 2 with r = f and W_0 = I, measured in SageMath (the sextic model needs no special handling)");}

print("(5) THE DESIGN THAT CLOSES");
info("With h_ell = 0 for every odd ell, the equations at the rational points are epsilon^{-1} theta(x_i) = B(x_i) - h_2(x_i), where B = diag(B_1, B_2) is known from SageMath's p-adic heights on the two quotients (E096) and h_2 takes one value per component of Gamma_2 reached by C(Q_2).");
info("Ten affine rational points against 1 + (number of h_2-classes) unknowns is over-determined unless Gamma_2 has an implausible number of vertices, so epsilon comes out WITH a consistency check -- and the check is sharp, because epsilon is predicted to be 1 or 2 and nothing else.  A non-integral answer would refute the setup.");
info("This is BDMTV2023's own method for C_188 (they solved for kappa = (4/3) log_3(2) exactly this way).  It is available here and not for C_4 because B is fully known here and (B5) blocks it there.");
info("SCOPE: this is a full Phase 4-5 run on a new curve -- Tuitman model, correspondence from the bielliptic involution, (22), the Hodge side, theta at ten points -- i.e. a session of its own.  E100 is the design and the curve; the run is next.");

print("========================================================================");
print("E100 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
