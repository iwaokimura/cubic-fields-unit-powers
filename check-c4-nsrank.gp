/* check-c4-nsrank.gp --- E089: rho(J_Q) = rk NS(Jac C_4 / Q), and what the
   nine rational points can and cannot say about the height pairing.
   Run: gp -q check-c4-nsrank.gp

   WHY.  E088 ended on blocker (B5): the known rational points determine only
   two of the three coefficients of the Prym block of B.  The route proposed
   there was a SECOND nice correspondence Z_2, since B = h does not depend on
   Z, so fresh rows would come against the same unknowns.  That is what
   [BDM+19] does on X_s(13) with Z_1, Z_2.  It exists iff there is room for it:
   the space of nice Z is Ker(NS(J) -> NS(X)), of rank rho - 1 (E071), with
   rho := rk NS(J_Q) as in [BDM+19] Section 1.3.  So the question is whether
   rho(J_Q) >= 3.

   THE DERIVATION.  J ~_Q E x P over Q (E037, E043), with E : y^2 = x^3-36x and
   P the Prym surface.  NS(J) (x) Q is the Rosati-fixed part of End^0(J)
   ([Mum70] Section IV.20, quoted at [BDM+19] Section 4.1).  End_Q(E) = Z --
   the CM by Z[i] is defined only over Q(i) -- so rho(E_Q) = 1.  If P is
   Q-simple with End^0_Q(P) = Q then Hom_Q(E,P) = 0 by dimension, so
   End^0_Q(J) = Q x Q, every element symmetric, and rho(J_Q) = 2.

   HOW TO DECIDE End^0_Q(P).  Frobenius is central in End^0 of the reduction,
   so End_Q(P) and pi_p commute.  Run through Albert's classification for an
   abelian surface over Q and look at the quartic chi_{P,p}, written in Weil
   form x^4 - c_1 x^3 + c_2 x^2 - p c_1 x + p^2.  Substituting y = x + p/x
   turns it into y^2 - c_1 y + (c_2 - 2p), so chi_{P,p} splits over
   Q(sqrt(D_p)) with

       D_p = c_1^2 - 4 c_2 + 8 p .

     End^0 = F real quadratic (RM)      : V_l is rank 2 over F (x) Q_l, so
                                          chi_P = N_{F/Q}(x^2 - a x + p) and
                                          Q(sqrt D_p) is contained in F ;
     End^0 = K CM quartic               : pi in K and y = pi + pibar lies in
                                          the real quadratic subfield K^+ ;
     End^0 = indefinite quaternion      : chi_P = (x^2-a_p x+p)^2, D_p = 0 ;
     P ~ E_1 x E_2 or E^2               : chi_P splits over Q, D_p a square.

   In EVERY case with End^0_Q(P) =/= Q the squarefree part of D_p lies in
   {1, d} for ONE fixed d.  Hence:

       two distinct non-square values of core(D_p)  ==>  End^0_Q(P) = Q.

   THE CHECKS.
     (1) Point counts on the smooth plane quartic, and the char polynomial.
         chi_C(13) against E059's [1,7,27,74,351,1183,2197], N_1(13) = 21
         against E080's 21 residue disks, and -- for every prime -- chi_E
         DIVIDES chi_C exactly.  That last one has teeth: a single miscounted
         point destroys it, which check (2) demonstrates on purpose.
     (2) Negative control: perturb one point count by 1; the division must fail.
     (3) The squarefree parts of D_p.
     (4) The verdict on rho(J_Q).
     (5) Controls on the criterion itself: a curve whose Jacobian splits over Q
         (E050's bielliptic y^2 = x^6+x^4-x^2+1, all D_p must be squares), a
         synthetic RM surface (core(D_p) must be constant), and a curve
         expected to be generic (the test must NOT say "non-generic", else it
         is vacuous).
     (6) WHAT THE RATIONAL POINTS CAN SAY AT ALL.  With sigma acting as -1 on
         the Prym, write delta(x) := [x - sigma x], so that the Prym projection
         of [x-b] is (delta(x) - delta(b))/2 and that of [x - sigma b] is
         (delta(x) + delta(b))/2.  E088 measured E_2' = m_2 (pi(x-b) - kappa'),
         so the Prym part of the height is

             (m_2/4) [ hhat_P(delta(x)) - hhat_P(delta(b)) ] .

         The x-dependence is through hhat_P(delta(x)) ALONE.  Two consequences,
         both exact: the height is sigma-invariant (delta(sigma x) = -delta(x)
         and hhat is even), which re-derives E088's finding; and CHANGING THE
         BASE POINT CANNOT HELP, because it only shifts by a constant.  The
         span of the functionals q |-> q(delta(x)) is computed here from E088's
         measured delta-values and is 2 out of 3, for every base point. */

FAIL = 0;
PMAX = 80;

check(c, msg) = {
  if(c, printf("   [ok]  %s\n", msg), printf("   [FAIL] %s\n", msg); FAIL++);
  c;
}

info(msg) = printf("        %s\n", msg);

/* ---------------------------------------------------------------- counting */

nroots(f) = {
  my(F = factor(f), n = 0);
  for(i = 1, matsize(F)[1], if(poldegree(F[i,1]) == 1, n++));
  n;
}

/* The projective model is w^4 - 6(t-z)^2 w^2 + 27 t^4 - 108 t z^3, smooth for
   p >= 5 (E086 found the bad primes to be 2 and 3).  Projection away from
   (0:1:0), which is not on the curve, is a degree-4 map to P^1, so the points
   are counted fibre by fibre. */
countC(p, k) = {
  my(g, one, N = 0, t, pw);
  if(k == 1, g = Mod(1,p), g = ffgen(ffinit(p,k), 'a));
  one = g^0;
  pw = vector(k, i, g^(i-1));
  forvec(v = vector(k, i, [0, p-1]),
    t = sum(i = 1, k, v[i]*pw[i]);
    N += nroots(one*'w^4 - 6*(t-one)^2*'w^2 + (27*t^4 - 108*t));
  );
  N + nroots(one*'w^4 - 6*one*'w^2 + 27*one);    /* the fibre over (1:0) */
}

chiFrom(p, N1, N2, N3) = {
  my(s1 = p+1-N1, s2 = p^2+1-N2, s3 = p^3+1-N3, e1, e2, e3);
  e1 = s1; e2 = (s1^2-s2)/2; e3 = (s1^3 - 3*s1*s2 + 2*s3)/6;
  'x^6 - e1*'x^5 + e2*'x^4 - e3*'x^3 + p*e2*'x^2 - p^2*e1*'x + p^3;
}

/* D_p of a Weil quartic x^4 - c1 x^3 + c2 x^2 - p c1 x + p^2 */
discOf(q, p) = (-polcoef(q,3))^2 - 4*polcoef(q,2) + 8*p;

weilOK(q, p) = {
  my(c1);
  if(type(q) != "t_POL" || poldegree(q) != 4, return(0));
  c1 = -polcoef(q,3);
  polcoef(q,4) == 1 && polcoef(q,0) == p^2 && polcoef(q,1) == -p*c1;
}

/* the squarefree part, with D = 0 counted as a square: a double root means
   chi splits over Q, which is the same case as "D_p is a square" */
sfpart(D) = if(D == 0, 1, core(D));

nonsq(v) = Set(select(d -> d != 1, v));

/* --------------------------------------------------------------- the parts */

part1() = {
  my(c, ap, qr, N1, N2, N3, ok);
  print("(1) POINT COUNTS, chi_C, AND chi_E | chi_C");
  E = ellinit([0,0,0,-36,0]);
  N13 = countC(13,1);
  check(N13 == 21, Str("N_1(13) = ", N13, ", which is E080's count of 21 "
        "residue disks at p = 13"));
  CHI13 = chiFrom(13, N13, countC(13,2), countC(13,3));
  check(CHI13 == 'x^6 + 7*'x^5 + 27*'x^4 + 74*'x^3 + 351*'x^2 + 1183*'x + 2197,
        Str("chi_C(13) = ", CHI13, ", which is E059's "
            "[1,7,27,74,351,1183,2197] -- computed here by brute-force point "
            "counting, there by the Frobenius matrix of the port"));
  PS = []; CHIP = []; DS = [];
  forprime(p = 5, PMAX,
    N1 = countC(p,1); N2 = countC(p,2); N3 = countC(p,3);
    c = chiFrom(p, N1, N2, N3);
    ap = ellap(E,p);
    qr = divrem(c, 'x^2 - ap*'x + p);
    if(qr[2] != 0,
      check(0, Str("chi_E does NOT divide chi_C at p = ", p)),
      PS = concat(PS, p); CHIP = concat(CHIP, [qr[1]]);
      DS = concat(DS, sfpart(discOf(qr[1], p)));
    );
  );
  check(#PS == #primes([5,PMAX]),
        Str("chi_E divides chi_C exactly at all ", #PS, " good primes "
            "5 <= p < ", PMAX, ": the point counts over F_p, F_{p^2}, F_{p^3} "
            "are consistent with the isogeny J ~ E x P, which they would not "
            "be if a single point were miscounted"));
  ok = 1;
  for(i = 1, #PS, if(!weilOK(CHIP[i], PS[i]), ok = 0));
  check(ok, "and every chi_P has the Weil shape x^4 - c1 x^3 + c2 x^2 "
            "- p c1 x + p^2");
  ok = 1;
  for(i = 1, #PS, if(abs(-polcoef(CHIP[i],3)) > 4*sqrt(PS[i]), ok = 0));
  check(ok, "and satisfies the Weil bound |c1| <= 4 sqrt(p)");
}

part2() = {
  my(cbad);
  print("(2) NEGATIVE CONTROL ON THE COUNTS");
  cbad = chiFrom(13, N13+1, countC(13,2), countC(13,3));
  check(divrem(cbad, 'x^2 - ellap(E,13)*'x + 13)[2] != 0,
        "moving N_1(13) by one makes chi_E fail to divide chi_C: the "
        "divisibility in (1) is a real constraint, not an identity");
}

part3() = {
  my(s = "");
  print("(3) THE SQUAREFREE PARTS OF D_p");
  for(i = 1, #PS, s = Str(s, PS[i], ":", DS[i], "  "));
  info(s);
  info(Str("distinct values of core(D_p): ", Set(DS)));
  check(#nonsq(DS) >= 2,
        Str("at least two DISTINCT NON-SQUARE values occur (", nonsq(DS),
            ").  By the case analysis in the header, End^0_Q(P) = Q"));
}

part4() = {
  print("(4) THE VERDICT ON rho(J_Q)");
  check(#nonsq(DS) >= 2,
        "End^0_Q(P) = Q, so P is Q-simple; being of dimension 2 against E's 1 "
        "it is not Q-isogenous to E, so Hom_Q(E,P) = 0 and End^0_Q(J) = Q x Q");
  info("End_Q(E) = Z because the CM by Z[i] is defined only over Q(i), so "
       "rho(E_Q) = 1; and rho(P_Q) = 1.");
  check(#nonsq(DS) >= 2,
        "HENCE rho(J_Q) = 2, the space of nice correspondences "
        "Ker(NS(J) -> NS(X)) has rank rho - 1 = 1, and THE Z WE ALREADY HAVE "
        "IS THE ONLY ONE up to scale.  E088's proposed route to (B5) -- a "
        "second correspondence Z_2 -- DOES NOT EXIST.");
}

ctrl_split() = {
  my(DD = [], q);
  forprime(p = 5, 60,
    q = iferr(hyperellcharpoly(Mod(1,p)*('x^6 + 'x^4 - 'x^2 + 1)), e, 0);
    if(weilOK(q,p), DD = concat(DD, sfpart(discOf(q,p))));
  );
  check(#DD > 5 && #nonsq(DD) == 0,
        Str("SPLIT CONTROL: E050's bielliptic y^2 = x^6+x^4-x^2+1, whose "
            "Jacobian splits over Q, gives a SQUARE D_p at all ", #DD,
            " good primes tested (three of them D_p = 0, the two elliptic "
            "factors sharing a_p) -- the criterion does detect a non-generic "
            "surface"));
}

/* An abelian surface with RM by F = Q(sqrt 5): chi = N_{F/Q}(x^2 - alpha x + p)
   with alpha = u + v phi, phi = (1+sqrt5)/2.  Expanding, c1 = Tr(alpha) = 2u+v
   and c2 = N(alpha) + 2p = u^2+uv-v^2 + 2p.  The quartic is built here and fed
   through the SAME discOf and sfpart the real data goes through, so the
   control tests the pipeline and not just the algebra. */
ctrl_rm() = {
  my(DD = [], u, v, c1, c2, q);
  forprime(p = 5, 60,
    u = p % 7 - 3; v = p % 5 + 1;
    c1 = 2*u + v; c2 = u^2 + u*v - v^2 + 2*p;
    q = 'x^4 - c1*'x^3 + c2*'x^2 - p*c1*'x + p^2;
    if(weilOK(q,p), DD = concat(DD, sfpart(discOf(q,p))));
  );
  check(#DD > 5 && #nonsq(DD) <= 1,
        Str("SYNTHETIC RM CONTROL: for chi = N_{F/Q}(x^2 - alpha x + p) with "
            "alpha in Q(sqrt 5), the pipeline returns core(D_p) in ", Set(DD),
            " over ", #DD, " primes -- one non-square value, the discriminant "
            "of F, as the header claims"));
}

ctrl_generic() = {
  my(DD = [], q);
  forprime(p = 5, 60,
    q = iferr(hyperellcharpoly(Mod(1,p)*('x^5 + 'x + 1)), e, 0);
    if(weilOK(q,p), DD = concat(DD, sfpart(discOf(q,p))));
  );
  check(#nonsq(DD) >= 2,
        Str("NON-VACUITY CONTROL: y^2 = x^5+x+1 gives ", #nonsq(DD),
            " distinct non-square values, so the criterion is not one that "
            "every abelian surface passes"));
}

part5() = {
  print("(5) CONTROLS ON THE CRITERION");
  ctrl_split(); ctrl_rm(); ctrl_generic();
}

/* delta(x) = [x - sigma x] in the Prym, in the basis (kappa', a) fixed by
   E088's measurement AJ_b(x)' = alpha kappa' with alpha = 1, 1, 1/2, -1/2 at
   sigma b, (-1,3), (0,0), (-2,6), and AJ_b((-1/11,15/11))' = a.
   delta(x) = 2 AJ_b(x)' - kappa', and delta(sigma x) = -delta(x). */
part6() = {
  my(nm, aj, del, ev, M, ok);
  print("(6) WHAT THE NINE RATIONAL POINTS CAN SAY, FOR ANY BASE POINT");
  nm = ["b=(1,3)", "sigma b=(1,-3)", "(-1,3)", "(-1,-3)", "(0,0)",
        "(-2,6)", "(-2,-6)", "(-1/11,15/11)", "(-1/11,-15/11)"];
  aj = [[0,0], [1,0], [1,0], [0,0], [1/2,0], [-1/2,0], [3/2,0],
        [0,1], [1,-1]];
  del = vector(9, i, [2*aj[i][1] - 1, 2*aj[i][2]]);
  ev  = vector(9, i, [del[i][1]^2, del[i][1]*del[i][2], del[i][2]^2]);
  for(i = 1, 9, info(Str(nm[i], "   delta = ", del[i], "   ev = ", ev[i])));
  M = matconcat(vector(9, i, Col(ev[i])));
  check(matrank(M) == 2,
        Str("the functionals q |-> q(delta(x)) span rank ", matrank(M),
            " of the 3-dimensional space of quadratic forms on the Prym "
            "plane"));
  ok = 1;
  for(j = 1, 9,
    if(matrank(matconcat(vector(9, i, Col(ev[i] - ev[j])))) != 2, ok = 0));
  check(ok, "and subtracting ANY of the nine as base point leaves the rank at "
            "2: the Prym part of the height depends on x only through "
            "hhat_P(delta(x)), so (B5) cannot be cured by moving b");
  info("what is missing is hhat_P on a third direction, e.g. the cross term "
       "B'(kappa', 2a - kappa').  The two the points do reach are "
       "kappa' = delta(sigma b) and 2a - kappa' = delta((-1/11,15/11)).");
}

main() = {
  my(t0 = getwalltime());
  print("=== check-c4-nsrank.gp --- E089: rho(J_Q), and what the points can "
        "say ===");
  part1(); part2(); part3(); part4(); part5(); part6();
  print("========================================================================");
  printf("E089 GATE: %s   (%d failures, %d s)\n",
         if(FAIL, "*** RED ***", "GREEN"), FAIL, (getwalltime()-t0)\1000);
}

main();
quit;
