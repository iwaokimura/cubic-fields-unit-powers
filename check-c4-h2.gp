/* check-c4-h2.gp --- E092: why the h_2 decomposition is read off by ONE-term
 * rational reconstruction and not by lindep, demonstrated on numbers whose
 * answer is known in advance.
 *
 * E092 needs to split two measured p-adic numbers along
 *     Q log_13(3)  +  Q log_13(2) ,
 * h_3 living in the first summand and h_2 in the second ([BDMTV2023] Thm 3.2).
 * The obvious tool is a three-term integer relation, lindep([theta, l2, l3]).
 * It does not work at the precision this project can reach, and the reason is
 * counting, not implementation:
 *
 *   - a relation among THREE p-adic numbers known modulo p^k with coefficients
 *     of size H exists by pigeonhole as soon as H^3 > p^k, so lindep returns
 *     SOMETHING of height about p^{k/3} whatever the input.  At k = 9 that is
 *     13^3 = 2197 -- below the 4212 and 2808 we are looking for, so the true
 *     relation is indistinguishable from noise.
 *
 *   - a ONE-term reconstruction theta/log in Q is a different problem: the
 *     structure derived in check-c4-h2.sage says which single log each
 *     combination must be a multiple of, so there is no search over two
 *     coefficients.  Reconstruction below sqrt(p^k/2) is unique.
 *
 *   - but "a rational below the bound exists" is still weak: the fractions a/b
 *     with |a|, b under sqrt(p^k/2) already cover about 6/pi^2 = 61% of all
 *     residues.  What is rare is an INTEGER: those cover 2*13^{k/2}/13^k.
 *     THAT is E092's criterion, and it is what the gate reports.
 *
 * Usage:  gp -q check-c4-h2.gp
 */

p = 13;

demo(k) =
{
  my(l2, l3, A, B, C);
  l2 = log(2 + O(p^k));  l3 = log(3 + O(p^k));
  A = -4212*l3;                      /* pure log 3, as A should be */
  B = -4212*l3 - 2808*l2;            /* both, as B should be */
  C = A + 7*p^3 + O(p^k);            /* neither: a control */
  printf("  k = %2d   lindep(A)  = %s   (true: [1,0,4212])\n", k, lindep([A,l2,l3]));
  printf("           lindep(B)  = %s   (true: [1,2808,4212])\n", lindep([B,l2,l3]));
  printf("           lindep(C)  = %s   (true: none)\n", lindep([C,l2,l3]));
  printf("           pigeonhole height p^(k/3) = %.0f\n", p^(k/3.0));
}

oneterm(name, a, k) =
{
  my(r, lim);
  r = iferr(bestappr(Mod(a, p^k)), e, 0);
  lim = p^(k/2.0);
  printf("  %-22s mod %d^%-2d : %-10s", name, p, k, if(r==0, "(none)", r));
  if (r != 0 && type(r) == "t_INT" && abs(r) < lim,
      printf("  INTEGER, |r| = %d < %.0f; %.1e of residues\n", abs(r), lim, 2/lim),
      printf("  -- not an integer below %.0f\n", lim));
}

/* ------------------------------------------------------------ the partition
 * C_4 -> E = C_4/sigma is branched at t = 0 and at the three roots of t^3 = 4
 * (E065(a)).  For t in Q the three roots are Galois-conjugate, so
 *     v_ell(t - alpha) = v_ell(t^3 - 4)/3   for each of them,
 * and "t lies in the disk of the cube-root cluster" is the exact condition
 *     v_ell(t^3 - 4) > 0 .
 * AT ell = 3 THAT CONDITION REPRODUCES E084's j_Gamma TABLE EXACTLY -- and
 * E084's table came from a semistable model computed independently (E083, and
 * MCLF in E085).  So the rule is not a guess at ell = 3; E092 applies the same
 * rule at ell = 2, where the model is wild and out of reach.
 */
TS  = [1, -2, -1/11, -1, 0];
J3  = [0, 0, 0, 1/8, 1/8];          /* E084's j_Gamma, in E084's normalisation */

incluster(t, l) = valuation(t^3 - 4, l) > 0;

partition(l) =
{
  my(inn = [], out = []);
  for (i = 1, #TS,
    if (incluster(TS[i], l), inn = concat(inn, [TS[i]]),
                             out = concat(out, [TS[i]])));
  printf("  ell = %d:  in the cluster  %s\n", l, inn);
  printf("            outside         %s\n", out);
  [inn, out];
}

{
  print("E092: lindep is the wrong tool here, and why.");
  print("");
  print("(1) three-term lindep on SYNTHETIC numbers with known relations:");
  demo(9);
  print("");
  demo(15);
  print("");
  print("  At k = 9 -- the certified precision of theta at a good rational");
  print("  point when N = 12 -- lindep cannot see 4212 or 2808 at all.  It");
  print("  needs k > 3 log_13(4212) = 9.8, and comfortably more.");
  print("");
  print("(2) the one-term criterion, applied to the two values the Sage gate");
  print("    REPORTS (the measurement is there, where the p-adic numbers are;");
  print("    what is checked here is that those values pass the criterion):");
  print("    A = theta(-1,3), certified 13^9, so A/log_13(3) is known mod 13^8");
  print("    D = theta(0,0) + theta(-2,6)/3 - A, measured floor p^{67/8} at");
  print("        e = 104, so D/log_13(2) is known mod 13^7");
  oneterm("A / log_13(3)", -4212, 8);
  oneterm("D / log_13(2)", -2808, 7);
  print("");
  print("  and the same residues against the OTHER log are not integers --");
  print("  that half of the test is in the Sage gate, where the numbers are.");
  print("");
  print("(3) the arithmetic of the two rationals:");
  printf("    h_3(-1,3) = 4212 log_13(3),  4212 = %s\n", factor(4212));
  printf("    h_2(0,0) + h_2(-2,6)/3 = 2808 log_13(2),  2808 = %s\n", factor(2808));
  printf("    ratio 4212/2808 = %s\n", 4212/2808);
  printf("    if (0,0) and (-2,6) share a vertex of Gamma_2 [P], each is\n");
  printf("      3*2808/4 = %s log_13(2),  %s = %s\n", 3*2808/4, 3*2808/4,
         factor(3*2808/4));
  printf("    and then h_2/h_3 = %s\n", (3*2808/4)/4212);
  print("");
  print("(4) WHERE THAT PARTITION COMES FROM, and why it is not numerology.");
  print("    C_4 -> E is branched at t = 0 and t^3 = 4; for t in Q the three");
  print("    cube roots are conjugate, so v_ell(t-alpha) = v_ell(t^3-4)/3 and");
  print("    \"t is in the cube-root cluster\" reads v_ell(t^3-4) > 0.");
  my(P3, P2, ok);
  P3 = partition(3);
  ok = 1;
  for (i = 1, #TS,
    my(inn = incluster(TS[i], 3));
    /* E084: j_Gamma = 0 exactly on the cluster side, which contains t = 1 = b */
    if ((J3[i] == 0) != inn, ok = 0));
  printf("  ell = 3 against E084's j_Gamma table %s : %s\n", J3,
         if (ok, "AGREES on all five points", "*** DISAGREES ***"));
  print("  E084's table came from a semistable model computed independently");
  print("  (E083, and MCLF in E085), so at ell = 3 the rule is verified, not");
  print("  assumed.  The same rule at ell = 2, where the model is wild:");
  P2 = partition(2);
  printf("  which is the t-even / t-odd split, now with a reason: at ell = 2\n");
  printf("  ALL FOUR branch points collide (E065(a): mutual distance 2/3), so\n");
  printf("  the cluster disk is v_2(t) > 0.\n");
}
