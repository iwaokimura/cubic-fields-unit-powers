/* check-e091-residual.gp --- E091: rational reconstruction of the residual.
 *
 * E091 measures  D := theta_b(0,0) - [ theta(-1,3) - theta(-2,6)/3 ],  the
 * failure of E090's prediction.  Under the framework of [BDM+19] the whole of
 * D is a difference of local heights away from p,
 *     D = -h_2(0,0) + h_2(-1,3) - h_2(-2,6)/3    (up to the overall sign),
 * and [BDMTV2023] Theorem 3.2 makes each h_ell a RATIONAL multiple of
 * log_p(ell): h_ell(x) = c_ell log_p(ell) [ j_Gamma(red x) - j_Gamma(red b) ]
 * with j_Gamma rational.  So D / log_13(2) and D / log_13(3) are the two
 * quantities that ought to be rational, and this script decides -- by rational
 * reconstruction of the p-adic number, NOT by a search over a grid.
 *
 * The input is the p-adic expansion E091 printed, given as the vector of its
 * base-13 digits together with the valuation and the number of digits that are
 * BELOW the certificate.  Nothing beyond the certificate is fed in: feeding
 * garbage digits to bestappr would manufacture a rational out of noise.
 *
 * Usage:  gp -q check-e091-residual.gp
 * Edit the DATA section from the gate's output.
 */

p = 13;

/* rational reconstruction: the rational of least height congruent to a mod p^k,
 * which is what bestappr(Mod(.,.)) computes.  Returns 0 when there is none of
 * height below the Dirichlet bound sqrt(p^k/2). */
recon(a, k) =
{
  my(r);
  r = iferr(bestappr(Mod(a, p^k)), e, 0);
  r;
}

/* a p-adic number from its digit vector (low to high), starting at p^v */
fromdig(v, d) = p^v * sum(i = 1, #d, d[i] * p^(i-1));

report(name, a, k) =
{
  my(r);
  printf("%-22s = %s  mod %d^%d\n", name, lift(Mod(a, p^k)), p, k);
  r = recon(a, k);
  if (r == 0 || type(r) != "t_FRAC" && type(r) != "t_INT",
    printf("%-22s   no rational of height below sqrt(%d^%d/2) = %.0f\n",
           "", p, k, sqrt(p^k/2.0)),
    printf("%-22s   = %s   (height %s, denominator %s)\n", "", r,
           max(abs(numerator(r)), denominator(r)), denominator(r));
    printf("%-22s   check: %s\n", "",
           if (Mod(numerator(r), p^k) == Mod(r * denominator(r), p^k) &&
               Mod(a * denominator(r) - numerator(r), p^k) == 0,
               "congruent", "NOT congruent")));
  print("");
}

/* ------------------------------------------------------------------ DATA
 * From check-c4-iterated.sage at N = 12, e = 52.  DIG2 and DIG3 are the
 * base-13 digits of D/log_13(2) and D/log_13(3) from the valuation VAL upward,
 * read off the Q_p part of the printed pi-expansion -- i.e. only the terms
 * whose pi-exponent is divisible by e, and only those below the measured floor
 * (the first exponent NOT divisible by e, which for D was pi^351/52 = p^6.75).
 * Five digits, so each number is known modulo 13^6.
 */
DIG2 = [5, 9, 11, 12, 12];   VAL2 = 1;   K2 = 5;
DIG3 = [10, 3, 10, 5, 10];   VAL3 = 1;   K3 = 5;

/* The same at e = 104, an independent extension: seven digits, so 13^8, whose
 * Dirichlet bound 20196 EXCEEDS 2808.  There the reconstruction is unique and
 * bestappr returns it outright -- for ell = 2 and for nothing else. */
DIG2b = [5, 9, 11, 12, 12, 12, 12];   VAL2b = 1;   K2b = 7;
DIG3b = [10, 3, 10, 5, 10, 7, 5];     VAL3b = 1;   K3b = 7;

{
  print("E091: is the residual a rational multiple of log_13(2) or log_13(3)?");
  print("");
  print("--- N = 12, e = 52: five digits, 13^6, bound 1554 < 2808 ---");
  report("D / log_13(2)", fromdig(VAL2, DIG2), VAL2 + K2);
  report("D / log_13(3)", fromdig(VAL3, DIG3), VAL3 + K3);
  print("Least absolute residues, which is what decides it at this precision:");
  printf("  D/log_13(2) = %s  = %s\n",
         lift(Mod(fromdig(VAL2, DIG2), p^(VAL2+K2))) - p^(VAL2+K2),
         factor(lift(Mod(fromdig(VAL2, DIG2), p^(VAL2+K2))) - p^(VAL2+K2)));
  printf("  D/log_13(3) = %s\n",
         lift(Mod(fromdig(VAL3, DIG3), p^(VAL3+K3))) - p^(VAL3+K3));
  print("");
  print("--- N = 12, e = 104: seven digits, 13^8, bound 20196 > 2808 ---");
  report("D / log_13(2)", fromdig(VAL2b, DIG2b), VAL2b + K2b);
  report("D / log_13(3)", fromdig(VAL3b, DIG3b), VAL3b + K3b);
  print("");
  print("For comparison, E088 measured -8 theta(-1,3)/log_13(3) = -33696 =");
  print("-2^5 3^4 13, i.e. theta(-1,3) = 4212 log_13(3) -- reconfirmed in E092");
  print("as an integer modulo 13^8, whence h_3(-1,3) = -4212 log_13(3) in the");
  print("sign convention theta = -h_3 there.  j_Gamma takes the value 1/8 at");
  print("(-1,3) and at (0,0) [E084].");
  printf("  -33696 / -2808 = %s\n", 33696/2808);
}
