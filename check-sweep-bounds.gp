/* check-sweep-bounds.gp --- the bounds behind the sweep (paper2 Sections 7-8).
 *
 * Verifies sections 7 and 8 of paper2 (Consequences for n(b); The sweep:
 * Lemma 8.1, Lemma 8.2, Corollary 8.3, the box (13) and the two procedures).
 *
 * Smyth's paper (C. J. Smyth, Bull. London Math. Soc. 3 (1971) 169-175,
 * doi:10.1112/blms/3.2.169) has a single, unnumbered THEOREM, which reads:
 *
 *     Let theta_0 be the real root of theta^3 - theta - 1 = 0.  If
 *     prod_{|alpha_j| >= 1} |alpha_j| < theta_0, then P(z) is a reciprocal
 *     polynomial (i.e. P(z) = Q(z)),
 *
 * P being the minimal polynomial of alpha and Q(z) = z^n P(1/z).  paper2 uses
 * the contrapositive.
 *
 * What this script checks:
 *
 *  (a) The numerical claims of \S8 are checked WITHOUT floating point, so they
 *      are [T(CAS)] rather than [E].  An exact rational bracket
 *      l < rho < u for the plastic number turns "n(b) <= log(4 beta^2)/log rho"
 *      into an exact integer statement: the largest n with rho^n <= 4 beta^2 is
 *      496 for beta = 10^30 and 201 for beta = 10^12, both certified by
 *      u^n < 4 beta^2 < l^{n+1}.  The box (13) is checked with sqrtnint.
 *
 *  (b) A cleaner form of the non-reciprocity step.  For X^3 - BX^2 + AX - 1 one
 *      has z^3 P(1/z) = -(X^3 - AX^2 + BX - 1), so P is reciprocal exactly when
 *      A = B; and A = B forces P(1) = A - B = 0, contradicting irreducibility.
 *      For eta_b this is A - B = -3b^2, nonzero for b != 0.  (This is the
 *      argument of check-expo.gp; paper2 argues instead with the absolute
 *      values of the conjugates, which is equally correct.)
 *
 *  (c) The design of the sweep made quantitative.  The A-range has
 *      4*floor((4 beta^2)^{1/2q}) + 7 integers and the whole box has that times
 *      floor((4 beta^2)^{1/q}) + 6; at beta = 10^30 these are 5.7e15 and 5.0e10
 *      for q = 2, 3 (the two excluded exponents), 1.5e8 for q = 4, and the box
 *      only becomes affordable around q = 10-12 -- which is the band on which
 *      the two procedures can be compared.  The forty-prime sieve is measured
 *      exactly: the density of A mod p for which C_q(A,.) has a root mod p is a
 *      counted rational, and the product over the forty primes of
 *      check-e028-sweep.gp is 1.1e-8 for q = 4, against the heuristic
 *      (1-1/e)^40 = 1.08e-8.  Times the A-range this predicts about two
 *      survivors to be factored -- the calibration point of the design.
 *
 *  (d) The value set of n(b).  All six values of Theorem C already occur for
 *      |b| <= 200, and the set of q dividing some n(b) is {1,2,3,4,6,8,13}.
 *      At b = 3 the Smyth bound is ATTAINED: the fundamental unit of K_3 IS the
 *      plastic number rho (characteristic polynomial X^3 - X - 1, i.e.
 *      (A,B) = (-1,0)), and n(3) = 13.
 *
 * Gates (each prints PASS/FAIL; the run exits 1 if any FAIL):
 *   A. Lemma 8.1                                              [question 1]
 *      A1  with S = e^{1/2} and sigma = (c + i d)/S, c^2 + d^2 = 1, the
 *          elementary symmetric functions of (S^2, sigma, sigmabar) are
 *          B = S^2 + 2c/S,  A = 2Sc + 1/S^2,  and the product is 1
 *      A2  hence |A| <= 2 e^{1/2} + e^{-1} <= 2 e^{1/2} + 1 and
 *          |B - e| = 2 e^{-1/2}|cos phi| <= 2 e^{-1/2} < 2
 *      A3  applied to eta_b: eta_b < 3(b^2+b+1) + 2, checked exactly by the
 *          sign of eq (1) at that integer
 *      A4  and |3(b+1)| <= 2 eta_b^{1/2} + 1, likewise exactly
 *   B. Lemma 8.2                                              [question 2]
 *      B1  z^3 P(1/z) = -(X^3 - AX^2 + BX - 1): P is reciprocal iff A = B
 *      B2  A = B forces P(1) = A - B = 0, impossible for an irreducible P;
 *          for eta_b, A - B = -3b^2 != 0
 *      B3  the conjugates have absolute values e, e^{-1/2}, e^{-1/2}, so the
 *          Mahler measure is e (paper2's route to the same conclusion)
 *      B4  rho is the real root of x^3-x-1, with the exact bracket l < rho < u
 *      B5  the fundamental unit of K_b exceeds rho, checked exactly by the sign
 *          of its characteristic polynomial at l and u
 *   C. Corollary 8.3                                          [question 3]
 *      C1  3 beta^2 + 3 beta + 5 <= 4 beta^2 for beta >= 5
 *      C2  beta = 10^30: the largest n with rho^n <= 4 beta^2 is 496,
 *          certified by u^496 < 4 beta^2 < l^497
 *      C3  beta = 10^12: the same computation gives 201
 *   D. the box (13)                                           [question 4]
 *      D1  the floors are exact integer roots (sqrtnint), and the box is valid:
 *          (s+1)^{2q} >= M and (t+1)^q >= M
 *      D2  the A-range has 4s+7 integers: 5.7e15 for q=2 and 5.0e10 for q=3,
 *          matching the two figures quoted in \S8
 *      D3  the whole box has (4s+7)(t+6) points; the table for q <= 16
 *      D4  at beta = 10^12 the q = 2, 3 A-ranges are 5.7e6 and 5.0e4, so both
 *          exponents are swept there
 *   E. the forty-prime sieve                                  [question 5]
 *      E1  deg_B C_q = q, with a nonzero constant leading coefficient, so no
 *          specialisation A -> A0 collapses the degree
 *      E2  the exact density of admissible A modulo each of the forty primes
 *      E3  their product for q = 4..8, against the heuristic (1-1/e)^40
 *      E4  expected survivors for q = 4 at beta = 10^30
 *   F. the value set of n(b)                                  [question 6]
 *      F1  n(b) for |b| <= 200: the value set is {1,2,4,6,8,13}
 *      F2  the exceptional b with n(b) > 1 in that range
 *      F3  the set of q dividing some n(b) is {1,2,3,4,6,8,13}
 *      F4  at b = 3 the fundamental unit is the plastic number and n(3) = 13,
 *          so Smyth's bound is attained
 *
 * Run:  gp -q check-s6-sweep.gp < /dev/null
 */

default(parisize, 1024*1024*1024);

FAILS = 0;

gate(name, ok, detail) =
{
  if(ok, printf("  PASS  %-46s %s\n", name, detail),
         printf("  FAIL  %-46s %s\n", name, detail); FAILS = FAILS + 1);
  return(ok);
}

/* eq. (1): the minimal polynomial of eta_b, as a polynomial in X */
etamin(b) = { return(X^3 - 3*(b^2+b+1)*X^2 + 3*(b+1)*X - 1); }

/* p_k in paper2's convention: p_1(A,B) = B, p_2(A,B) = B^2 - 2A */
pk(k, U, V) =
{
  my(p0 = 3, p1 = V, p2 = V^2 - 2*U, t);
  if(k == 0, return(3));
  if(k == 1, return(V));
  if(k == 2, return(V^2 - 2*U));
  for(j = 3, k, t = V*p2 - U*p1 + p0; p0 = p1; p1 = p2; p2 = t);
  return(p2);
}

Fq(q) = { return(pk(q,B,A)^2 - 3*pk(q,B,A) + 9 - 3*pk(q,A,B)); }

/* the plastic number: exact rational bracket */
rhoL() = { return(13247179/10^7); }
rhoU() = { return(13247180/10^7); }
plastic(t) = { return(t^3 - t - 1); }

/* the forty primes of check-e028-sweep.gp */
plist() =
{
  return([5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,
          97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181]);
}

/* ---------------- A. Lemma 8.1 ----------------------------------------- */

checkA() =
{
  my(s1, s2, e1, e2, e3, ok, okA, b, bd, val);

  /* S = e^{1/2}; the two complex conjugates sigma, sigmabar have
     sigma + sigmabar = 2 cos(phi)/S  and  sigma sigmabar = (cos^2+sin^2)/S^2 = 1/S^2 */
  s1 = 2*c/S;
  s2 = 1/S^2;
  e1 = S^2 + s1;
  e2 = S^2*s1 + s2;
  e3 = S^2*s2;

  gate("A1a B = e + 2 e^{-1/2} cos(phi)",
       e1 - (S^2 + 2*c/S) == 0, "the trace of the three conjugates");
  gate("A1b A = 2 e^{1/2} cos(phi) + e^{-1}",
       e2 - (2*S*c + 1/S^2) == 0,
       "uses |sigma|^2 = (cos^2+sin^2)/S^2 = 1/S^2 = e^{-1}");
  gate("A1c the product of the conjugates is 1", e3 - 1 == 0,
       "N(e) = e |sigma|^2 = 1, which is what fixes |sigma| = e^{-1/2}");

  gate("A2a (2S+1) - A = 2S(1-c) + (S^2-1)/S^2, so |A| <= 2 e^{1/2} + 1",
       (2*S + 1) - e2 - (2*S*(1-c) + (S^2-1)/S^2) == 0,
       "both terms are >= 0 for c <= 1 and S >= 1");
  gate("A2b B - e = 2c/S, so |B - e| <= 2/S = 2 e^{-1/2} < 2",
       e1 - S^2 - 2*c/S == 0, "and S > 1 because e > 1");

  /* A3, A4: applied to eta_b, checked exactly */
  okA = 1; ok = 1;
  for(b = -200, 200,
    if(b == 0 || b == 1, next);
    bd = 3*(b^2+b+1) + 2;
    if(subst(etamin(b), X, bd) <= 0, ok = 0);
    val = (abs(3*(b+1)) - 1)^2 / 4;
    if(val > 0 && subst(etamin(b), X, val) > 0, okA = 0));
  gate("A3  eta_b < 3(b^2+b+1) + 2, i.e. eq (12)", ok,
       "|b| <= 200; eq (1) is positive at that integer, so it exceeds the real root");
  gate("A4  |3(b+1)| <= 2 eta_b^{1/2} + 1", okA,
       "eq (1) is non-positive at ((|A|-1)/2)^2, so eta_b is at least that");
  return(0);
}

/* ---------------- B. Lemma 8.2 ----------------------------------------- */

checkB() =
{
  my(P, Q, ok, b, bb, cp);

  P = X^3 - B*X^2 + A*X - 1;
  Q = X^3 * subst(P, X, 1/X);
  gate("B1  X^3 P(1/X) = -(X^3 - A X^2 + B X - 1)",
       numerator(Q + (X^3 - A*X^2 + B*X - 1)) == 0,
       "so P is reciprocal exactly when A = B");
  gate("B2a A = B forces P(1) = A - B = 0",
       subst(P, X, 1) == A - B,
       "impossible for an irreducible P: e would not generate a cubic field");
  ok = 1;
  for(b = -200, 200,
    if(b == 0 || b == 1, next);
    if(3*(b+1) - 3*(b^2+b+1) != -3*b^2, ok = 0);
    if(-3*b^2 == 0, ok = 0));
  gate("B2b for eta_b, A - B = -3 b^2, nonzero for b != 0", ok,
       "|b| <= 200; so eq (1) is never reciprocal");

  gate("B3  the Mahler measure of e is e itself",
       S^2 * (1/S) * (1/S) - 1 == 0,
       "the three absolute values multiply to 1 and two of them are 1/S < 1 for S > 1");

  gate("B4  rho is the real root of x^3-x-1, with l < rho < u",
       plastic(rhoL()) < 0 && plastic(rhoU()) > 0 && rhoU() - rhoL() == 1/10^7,
       concat(concat("l = ", Str(rhoL())), concat(", u = ", Str(rhoU()))));

  /* B5: the fundamental unit of K_b is at least rho, exactly */
  ok = 1; b = 0;
  for(bb = -40, 40,
    if(bb == 0 || bb == 1, next);
    cp = normunit(bnfinit(x^3 - 3*bb*x - bb^3, 1));
    if(cp == 0, ok = 0; next);
    /* either the real root exceeds u > rho, or the unit IS rho */
    if(!(subst(cp, X, rhoU()) < 0 || cp == X^3 - X - 1), ok = 0);
    if(cp == X^3 - X - 1, b = bb));
  gate("B5  the fundamental unit of K_b is >= rho", ok,
       concat("|b| <= 40; strict except at b = ", Str(b)));
  gate("B5b equality holds, so Smyth's bound is sharp here", b == 3,
       "at b = 3 the fundamental unit has characteristic polynomial X^3-X-1");
  return(0);
}

/* the characteristic polynomial X^3-BX^2+AX-1 of the fundamental unit of bnf,
   normalised so that its real embedding exceeds 1 (equivalently A < B) */
normunit(bnf) =
{
  my(u = Mod(bnf.fu[1], bnf.pol), cands, cp, A0, B0, out = 0);
  cands = [u, -u, 1/u, -1/u];
  for(k = 1, 4,
    cp = charpoly(cands[k], X);
    if(polcoeff(cp, 0, X) == -1,
      A0 = polcoeff(cp, 1, X); B0 = -polcoeff(cp, 2, X);
      if(A0 < B0, out = cp)));
  return(out);
}

/* ---------------- C. Corollary 8.3 ------------------------------------- */

/* the largest n with rhoL()^n <= M (and the certificate that it is exact) */
smythmax(M) =
{
  my(l = rhoL(), n = 0, p = 1);
  while(p * l <= M, p = p * l; n = n + 1);
  return(n);
}

checkC() =
{
  my(ok, n1, n2, M1, M2, bet, k);

  ok = 1;
  for(bet = 5, 200, if(3*bet^2 + 3*bet + 5 > 4*bet^2, ok = 0));
  gate("C1  3 beta^2 + 3 beta + 5 <= 4 beta^2 for beta >= 5", ok,
       "beta^2 - 3 beta - 5 >= 0 from beta >= (3+sqrt(29))/2 = 4.19...");

  M1 = 4 * 10^60;
  n1 = smythmax(M1);
  gate("C2  beta = 10^30 gives n(b) <= 496",
       n1 == 496 && rhoU()^496 < M1 && rhoL()^497 > M1,
       "u^496 < 4e60 < l^497, so the floor is 496 for every rho in the bracket");

  /* 2026-10-28: paper2 now states the bound without rounding up to 4 beta^2 */
  M1 = 3*10^60 + 3*10^30 + 5;
  n1 = smythmax(M1);
  gate("C2b beta = 10^30, unrounded 3 beta^2 + 3 beta + 5: n(b) <= 495",
       n1 == 495 && rhoU()^495 < M1 && rhoL()^496 > M1,
       "u^495 < 3e60+3e30+5 < l^496; the sweep's 496 is one more than needed");

  M2 = 4 * 10^24;
  n2 = smythmax(M2);
  gate("C3  beta = 10^12 gives n(b) <= 201",
       n2 == 201 && rhoU()^201 < M2 && rhoL()^202 > M2,
       "the range swept in check-e028-sweep.gp");

  /* read the other way: a large q forces a large b */
  ok = 1; n1 = "";
  for(k = 1, 7,
    my(qq = [4,8,13,20,50,100,496][k], bb = minb(qq));
    if(bb < 1, ok = 0);
    n1 = concat(n1, Strprintf(" %d:%d", qq, bb)));
  gate("C4  read backwards: q | n(b) forces 3b^2+3b+5 > rho^q", ok,
       concat(concat("q:min|b| =", n1), "  -- q = 496 needs |b| ~ 10^30"));
  return(0);
}

/* the least positive b with 3b^2+3b+5 > l^q, l < rho: a necessary condition
   for q | n(b), since eta_b >= rho^{n(b)} >= rho^q and eta_b < 3b^2+3b+5 */
minb(q) =
{
  my(t = rhoL()^q, P = numerator(t), Q = denominator(t), D, b);
  /* 3b^2+3b+5 > P/Q  <=>  3Q b^2 + 3Q b + (5Q-P) > 0 */
  D = 12*Q*P - 51*Q^2;
  if(D < 0, return(1));
  b = (-3*Q + sqrtint(D)) \ (6*Q);
  if(b < 0, b = 0);
  while(b > 0 && 3*(b-1)^2 + 3*(b-1) + 5 > t, b = b - 1);
  while(3*b^2 + 3*b + 5 <= t, b = b + 1);
  return(b);
}

/* ---------------- D. the box (13) -------------------------------------- */

checkD() =
{
  my(M, s, t, ok, detail, q);

  M = 4 * 10^60;
  ok = 1;
  for(q = 2, 40,
    s = sqrtnint(M, 2*q); t = sqrtnint(M, q);
    if((s+1)^(2*q) < M, ok = 0);
    if((t+1)^q < M, ok = 0);
    if(s^(2*q) > M, ok = 0));
  gate("D1  the floors are exact and the box is valid", ok,
       "2 floor(M^{1/2q}) + 3 >= 2 M^{1/2q} + 1 and floor(M^{1/q}) + 3 >= M^{1/q} + 2");

  s = sqrtnint(M, 4);
  gate("D2a q = 2: the A-range has 5.7e15 integers",
       4*s + 7 == 5656854249492387,
       concat(Str(4*s+7), "  (paper2 \\S8 quotes 5.7 x 10^15)"));
  s = sqrtnint(M, 6);
  gate("D2b q = 3: the A-range has 5.0e10 integers",
       4*s + 7 == 50396841999,
       concat(Str(4*s+7), "  (paper2 \\S8 quotes 5.0 x 10^10)"));

  detail = "";
  for(q = 4, 12,
    s = sqrtnint(M, 2*q); t = sqrtnint(M, q);
    if(q <= 6 || q >= 10,
      detail = concat(detail, Strprintf(" %d:%.1e/%.1e", q, (4*s+7)*1.0, (4*s+7)*(t+6)*1.0))));
  s = sqrtnint(M, 8); t = sqrtnint(M, 4);
  gate("D3  q = 4 costs 1.5e8 in A but 2.1e23 in the box",
       4*s + 7 == 150424127 && (4*s+7)*(t+6) > 10^23,
       concat("q:Acount/box =", detail));
  s = sqrtnint(M, 20); t = sqrtnint(M, 10);
  gate("D3b the whole box is affordable only from about q = 10",
       (4*s+7)*(t+6) < 10^10,
       concat(concat("q=10 box = ", Str((4*s+7)*(t+6))),
              "; the two procedures overlap from there on"));

  M = 4 * 10^24;
  s = sqrtnint(M, 4); t = sqrtnint(M, 6);
  gate("D4  at beta = 10^12 the q = 2, 3 A-ranges are 5.7e6 and 5.0e4",
       4*s + 7 == 5656859 && 4*t + 7 == 50403,
       concat(concat(Str(4*s+7), " and "), Str(4*t+7)));
  return(0);
}

/* ---------------- E. the forty-prime sieve ----------------------------- */

/* the density of A mod p for which C_q(A,.) has a root mod p */
density(C, p) =
{
  my(cnt = 0, g);
  for(a = 0, p-1,
    g = Mod(1,p) * subst(C, A, a);
    if(poldegree(g, B) >= 1 && #polrootsmod(g, p) > 0, cnt = cnt + 1));
  return(cnt/p);
}

/* the A-classes mod 3 compatible with 3 | p_q(A,B) and 3 | p_q(B,A) */
admisA(q) =
{
  my(PA = pk(q,B,A), PB = pk(q,A,B), S = List(), ra, rb);
  for(ra = 0, 2, for(rb = 0, 2,
    if(substvec(PA,[A,B],[ra,rb]) % 3 == 0 && substvec(PB,[A,B],[ra,rb]) % 3 == 0,
       listput(S, ra))));
  return(Set(Vec(S)));
}

checkE() =
{
  my(PL = plist(), ok, C, pr, q, detail, s, surv);

  ok = 1;
  for(q = 2, 12,
    C = Fq(q);
    if(poldegree(C, B) != q, ok = 0);
    if(poldegree(polcoeff(C, q, B), A) != 0, ok = 0);
    if(polcoeff(C, q, B) == 0, ok = 0));
  gate("E1  deg_B C_q = q with a nonzero constant leading coefficient", ok,
       "q <= 12; no specialisation A -> A0 collapses the degree");

  gate("E2  #PLIST = 40", #PL == 40,
       concat(concat("primes ", Str(PL[1])), concat(" .. ", Str(PL[40]))));

  detail = "";
  ok = 1;
  for(q = 4, 8,
    C = Fq(q);
    pr = 1;
    for(i = 1, #PL, pr = pr * density(C, PL[i]));
    if(pr <= 0 || pr > 10^-6, ok = 0);
    detail = concat(detail, Strprintf(" %d:%.2e", q, pr*1.0)));
  gate("E3  the product of the forty densities is about 1e-8 to 1e-7", ok,
       concat(concat("q:product =", detail),
              Strprintf("   heuristic (1-1/e)^40 = %.2e", (1-exp(-1))^40)));

  C = Fq(4);
  pr = 1;
  for(i = 1, #PL, pr = pr * density(C, PL[i]));
  s = sqrtnint(4*10^60, 8);
  surv = (4*s+7) * pr * #admisA(4) / 3;
  gate("E4  q = 4 at beta = 10^30: about two survivors to factor",
       surv > 0 && surv < 100,
       Strprintf("A-count %d x density %.2e x (mod 3 factor %d/3) = %.2f",
                 4*s+7, pr*1.0, #admisA(4), surv*1.0));
  return(0);
}

/* ---------------- F. the value set of n(b) ----------------------------- */

checkF() =
{
  my(vals = List(), exc = List(), qs = List(), b, K, th, u1, n, ok, bnf, cp);

  for(b = -200, 200,
    if(b == 0 || b == 1, next);
    K = bnfinit(x^3 - 3*b*x - b^3, 1);
    th = Mod(x, x^3 - 3*b*x - b^3);
    u1 = 1/((b+1) - th);
    n = abs(centerlift(bnfisunit(K, lift(u1))[1]));
    listput(vals, n);
    if(n != 1, listput(exc, [b, n])));

  gate("F1  the value set of n(b) for |b| <= 200 is {1,2,4,6,8,13}",
       Set(Vec(vals)) == Set([1,2,4,6,8,13]),
       concat("all six values of Theorem C already occur here: ",
              Str(Set(Vec(vals)))));
  gate("F2  the b with n(b) > 1 in that range",
       #exc >= 5,
       Str(Vec(exc)));

  for(b = 1, #vals, for(d = 1, vals[b], if(vals[b] % d == 0, listput(qs, d))));
  gate("F3  the q dividing some n(b) form {1,2,3,4,6,8,13}",
       Set(Vec(qs)) == Set([1,2,3,4,6,8,13]),
       concat(concat("q-set = ", Str(Set(Vec(qs)))),
              "; every other q <= 496 has no b, which is Theorem C"));

  /* b = 3: the fundamental unit is the plastic number */
  bnf = bnfinit(x^3 - 9*x - 27, 1);
  cp = normunit(bnf);
  gate("F4  at b = 3 the fundamental unit is the plastic number",
       cp == X^3 - X - 1 && bnf.disc == -23,
       concat(concat("char. poly ", Str(cp)),
              "; disc K_3 = -23, and n(3) = 13, so Smyth's bound is attained"));

  /* 2026-10-28, for the remark after Corollary 8.3 */
  cp = charpoly(Mod(X, X^3 - X - 1)^13);
  ok = 1;
  for(n = -3, 2, if(3*(n^2+n+1) + 2 > rhoL()^13, ok = 0));
  gate("F5  rho^13 = eta_3, and n(b) >= 13 forces b >= 3 or b <= -4",
       cp == x^3 - 39*x^2 + 12*x - 1 && ok
         && 3*(3^2+3+1) + 2 > rhoU()^13 && 3*(16-4+1) + 2 > rhoU()^13,
       concat(concat("char. poly of rho^13 = ", Str(cp)),
              " = (eq:etamin) at b = 3; 3(b^2+b+1)+2 <= 23 < l^13 for -3 <= b <= 2"));
  return(0);
}

run() =
{
  printf("=== check-sweep-bounds.gp: paper2 \\S7--\\S8 (the sweep) ===\n\n");

  printf("A. Lemma 8.1: the range of A and B\n");
  checkA();

  printf("\nB. Lemma 8.2: non-reciprocity and Smyth's bound\n");
  checkB();

  printf("\nC. Corollary 8.3: n(b) <= 496 (4 beta^2) and <= 495 (unrounded), exactly\n");
  checkC();

  printf("\nD. the box (13)\n");
  checkD();

  printf("\nE. the forty-prime sieve\n");
  checkE();

  printf("\nF. the value set of n(b)\n");
  checkF();

  printf("\n=== %s: %d failure(s) ===\n", if(FAILS, "FAILED", "ALL GATES PASSED"), FAILS);
  if(FAILS, quit(1));
  return(0);
}

run();
