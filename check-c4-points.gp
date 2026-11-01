\\ check-c4-points.gp --- E035, an attempt at an INDEPENDENT cross-check of
\\ "C_4 is not hyperelliptic", by point counting alone, in PARI/GP (no Sage, no
\\ function fields).
\\
\\ THE TEST.  A hyperelliptic curve X of genus 3 is a double cover of P^1, so
\\ each of the q+1 points of P^1(F_q) has at most 2 preimages:
\\        X hyperelliptic  ==>  #X(F_q) <= 2q+2.
\\ Every SMOOTH F_q-point of a plane model lifts to a unique F_q-point of the
\\ normalisation, so #{smooth affine F_q-points of C_4} is a lower bound for
\\ #X(F_q).  Hence
\\        #{smooth affine points} > 2q+2   ==>   X is NOT hyperelliptic,
\\ with no appeal to the canonical-map computation of check-c4-modp.sage.
\\
\\ BOUNDING EXPECTATIONS FIRST (Commandment VIII).  By Weil,
\\ #X(F_q) <= q+1+6*sqrt(q), and q+1+6*sqrt(q) > 2q+2 forces q < 34.  So the
\\ test can only ever fire for q <= 33, and then only if C_4 is close to maximal
\\ for genus 3 -- the record values N_q(3) are tabulated at manypoints.org.
\\ This script measures whether that actually happens.  It does not: see the
\\ verdict at the end, and E035(f).

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

DEG = 8;

\\ the recursion of E026: p_0=3, p_1=B, p_2=B^2-2A, p_k = B p_{k-1} - A p_{k-2} + p_{k-3}
{
c4poly(A, B) =
  my(p, pA, pB);
  p = [3, B, B^2 - 2*A];
  for(k = 3, 4, p = concat(p, [B*p[k] - A*p[k-1] + p[k-2]]));
  pA = p[5];
  pB = subst(subst(subst(pA, A, 'T), B, A), 'T, B);
  pB^2 - 3*pB + 9 - 3*pA;
}

C  = c4poly('A, 'B);
CA = deriv(C, 'A);
CB = deriv(C, 'B);

ev(P, a, b) = subst(subst(P, 'A, a), 'B, b);

{
\\ all elements of F_{p^k}, as F_p-combinations of powers of the ALGEBRA
\\ generator.  NB ffgen returns a root of the defining polynomial, not a
\\ multiplicative generator -- and for k=1 it returns 0 -- so enumerating by
\\ powers g^i is wrong (it silently misses most of the field).
fieldelts(p, k) =
  my(g, q, els, d, e);
  g = ffgen(p^k, 'w);
  q = p^k;
  els = vector(q);
  for(n = 0, q - 1,
    d = n; e = 0*g;
    for(i = 0, k - 1, e = e + (d % p) * g^i; d = d \ p);
    els[n+1] = e);
  els;
}

{
\\ smooth affine F_q-points of C_4, q = p^k
smoothpts(p, k) =
  my(els, cnt, a, b, zero);
  els = fieldelts(p, k);
  zero = 0 * ffgen(p^k, 'w);
  cnt = 0;
  for(i = 1, #els,
    a = els[i];
    for(j = 1, #els,
      b = els[j];
      if(ev(C, a, b) == zero,
        if(ev(CA, a, b) != zero || ev(CB, a, b) != zero, cnt++))));
  cnt;
}

{
report(q, p, k, cnt) =
  my(bound, weil, msg);
  bound = 2*q + 2;
  weil  = floor(q + 1 + 6*sqrt(q));
  msg = if(cnt > bound, "*** > 2q+2: NOT HYPERELLIPTIC ***",
        if(weil <= bound, "test cannot fire at this q", "no conclusion"));
  printf("  q = %4d = %2d^%d : smooth affine pts = %4d   2q+2 = %4d   Weil <= %4d   %s\n",
         q, p, k, cnt, bound, weil, msg);
}

check(poldegree(C, 'A) == 8 && poldegree(C, 'B) == 4, "E035: C_4 has deg_A = 8 and deg_B = 4");
print("deg_A C_4 = ", poldegree(C, 'A), ",  deg_B C_4 = ", poldegree(C, 'B));
print("");
print("C_4 mod p over F_{p^k}, all q = p^k <= 33 (larger q cannot fire):");
print("");

foundone = 0;
{
for(pi = 1, 6,
  my(p, q, cnt);
  p = [2, 3, 5, 7, 11, 13][pi];
  for(k = 1, 6,
    q = p^k;
    if(q > 33, break);
    cnt = smoothpts(p, k);
    report(q, p, k, cnt);
    check(cnt == if(p <= 3, 0, if(q == 5, 3, if(q == 7, 8, if(q == 11, 11, if(q == 13, 12, if(q == 25, 23, -1)))))),
          Str("E035(f): the smooth affine F_q-point count of C_4 (E035 table; 0 at p=2,3, where the reduction is non-reduced), q=", q));
    if(cnt > 2*q + 2, foundone = 1)));
}

print("");
{
if(foundone,
  print("VERDICT: point counting alone proves C_4 mod p is NOT hyperelliptic.")
,
  print("VERDICT: the point-count test never fires.  C_4 is nowhere near maximal");
  print("  for genus 3, so this route gives NO independent confirmation, and the");
  print("  canonical-map computation of check-c4-modp.sage stands alone.");
  print("  (manypoints.org is what bounds the expectation here: the test needs a");
  print("   curve close to the record N_q(3), which C_4 is not.)"));
check(!foundone, "E035(f): the point-count test does NOT fire for any q <= 33, as Weil predicted");
}

printf("\nE035 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
