\\ check-audit-post-trim.gp --- E024: the two numerical claims that the
\\ post-trim consistency pass of a draft of paper 1 depends on.
\\
\\ Context.  The long remarks on q >= 5 and the
\\ subsection on the sporadic b=3 were removed from that draft and
\\ deferred to a sequel.  Two statements in the trimmed text still rest on
\\ computation, and both are checked here.
\\
\\ (A) thm:idx is an EQUIVALENCE, not merely an implication.
\\     For a prime p with p !| b,
\\         p | [O_{K_b} : Z[theta]]   <=>   b^3 = 4  (mod p^2).
\\     The statement had been weakened to "implies" while the Introduction
\\     (Theorem B) still claims "such p are exactly the primes p !| b dividing
\\     [O_K:Z[theta]], and they are characterized by b^3 = 4 mod p^2", and while
\\     the proof in fact establishes the equivalence.  This run confirms the
\\     equivalence numerically before it is restored in the text.
\\     Method: a = |sqrt(disc(f_b)/D_K)| from nfinit, compared prime by prime
\\     with the congruence.  Note both sides fail for p = 2,3 when p !| b, which
\\     is the p in {2,3} half of the proof.
\\
\\ (B) The exponents behind Remark 5.7 of that draft (Remark 5.8 of paper 1).
\\     Under (star), "not fundamental <=> square" (thm:starq), so for |b| <= 3000
\\     the b with eta_b not fundamental are exactly the square-exceptions of
\\     thm:closed lying in that range, together with the four b where (star)
\\     fails (b = -75,-3,3,9; the first three are square-exceptions anyway).
\\     Writing eta_b = eta_0^n with eta_0 the fundamental unit, the prime
\\     divisors of n are exactly the exponents q that occur.  Remark 5.7 claims
\\     q = 2 (infinitely often), q = 3 only at b = 9, q = 13 at b = 3, and no
\\     q >= 17 for |b| <= 3000; this run produces the table of n.
\\
\\ NB: `eta` is a PARI built-in (Dedekind eta), so the unit is called u1 below.
\\
\\ Usage:  gp -q check-audit-post-trim.gp        (a few minutes)

default(realprecision, 60);

\\ --- E119 gate harness (added 2026-08-19; see E119) ---
FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };
\\ --- end gate harness ---

\\ ---------------------------------------------------------------- (A)
print("### (A) thm:idx:  p | [O_K:Z[theta]]  <=>  b^3 = 4 (mod p^2),  p !| b ###");
{
my(fail = 0, tested = 0, BB = 400, PB = 200);
for(b = -BB, BB,
  if(b == 0 || b == 1, next);
  my(f = x^3 - 3*b*x - b^3);
  my(nf = nfinit(f));
  my(a = abs(round(sqrt(poldisc(f)/nf.disc))));   \\ index [O_K : Z[theta]]
  forprime(p = 2, PB,
    if(b % p == 0, next);
    tested++;
    my(lhs = (a % p == 0));
    my(rhs = (Mod(b, p^2)^3 == Mod(4, p^2)));
    if(lhs != rhs,
      fail++;
      print("  MISMATCH  b = ", b, "  p = ", p, "  lhs = ", lhs, "  rhs = ", rhs);
    );
  );
);
check(fail == 0, "E024(f): p | [O_K:Z[theta]] <=> b^3 = 4 mod p^2, 35238 pairs (|b|<=400, p<200, p nmid b)");
print("  |b| <= ", BB, ",  p < ", PB, ":  pairs tested = ", tested,
      ",  mismatches = ", fail);
print(if(fail == 0, "  => equivalence confirmed on this range.",
                    "  => EQUIVALENCE FAILS; do not restore the iff."));
}

\\ ---------------------------------------------------------------- (B)
print("");
print("### (B) eta_b = eta_0^n for every non-fundamental b with |b| <= 3000 ###");
print("    (the 12 square-exceptions of thm:closed in range, plus the sporadic b=3)");
{
my(bs = [5, 9, 96, 112, 1425, 1485, -3, -16, -75, -135, -1344, -1568, 3]);
my(qs = List());
print("       b        n     prime factors of n");
for(i = 1, #bs,
  my(b = bs[i]);
  my(f = x^3 - 3*b*x - b^3);
  my(K = bnfinit(f, 1));
  my(th = Mod(x, f));
  my(u1 = 1/((b+1) - th));                        \\ eta_b = ((b+1)-theta)^(-1)
  my(ex = bnfisunit(K, lift(u1)));
  my(n = abs(centerlift(ex[1])));
  my(pf = if(n > 1, factor(n)[,1]~, []));
  for(j = 1, #pf, listput(qs, pf[j]));
  print("  ", b, "\t", n, "\t", pf);
);
my(occ = vecsort(Vec(qs), , 8));
check(occ == [2,3,13],
      "E024(g): the exponents q for |b|<=3000 are exactly 2,3,13 -- ASSUMES GRH (bnfinit, no bnfcertify)");
print("  exponents q occurring for |b| <= 3000 : ", occ);
print("  max q = ", vecmax(occ),
      "   (Remark 5.7 claims q = 2, 3, 13 only, hence none >= 17)");
}

printf("\nE024 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);

quit

