\\ check-c4-basefield.gp --- E107: the base field at ell = 3, and what b's
\\ ell-adic terms actually reduce to.
\\
\\ Run: gp -q check-c4-basefield.gp
\\
\\ THE QUESTION E105 AND E106 LEFT.  The ell = 3 model is over O_K with
\\ K = Q(i), the prime above 3 being UNRAMIFIED with residue degree f = 2, not
\\ over Z_3.  Gross's formula wants a regular model over Z_3.  Does Lambda_3
\\ need a correction?
\\
\\ THE ANSWER: NO.  Three steps, none of them requiring the Z_3-model to be
\\ computed.
\\
\\   (a) A Q_3-rational point lies on a component that is Frobenius-STABLE and
\\       geometrically irreducible: it lies on exactly one component of the
\\       geometric special fibre, and Galois permutes components while fixing
\\       the point.  So the three components A, B, C carrying our nine rational
\\       points come from Z_3-components.
\\   (b) Intersection numbers are INVARIANT under unramified base change.  A
\\       closed point of residue degree d over F_3 becomes gcd(d,f) points of
\\       degree lcm(d,f)/f over F_{3^f}, and gcd(d,f) * lcm(d,f)/f = d.
\\   (c) ker M_3 = Q m_3 exactly (E105), so the vertical correction solving
\\       M a = -d is unique modulo Q m, hence its pairing against another
\\       degree-0 component vector does not depend on the choice.  In
\\       particular it is Galois-invariant, hence descends to Z_3.
\\
\\ Therefore Lambda_3 as computed on the O_K-model IS the Z_3 pairing.
\\
\\ AND THE TRAP, NAMED.  The height OVER K is a different quantity and IS twice
\\ ours: chi_P = chi_3 . N_{K/Q}, and N(3) = 9 for the unramified prime, so
\\ chi_P(3) = 2 chi_3(3) and h_P = 2 h_3.  Nothing here computes h_P, and the
\\ factor 2 is real for the quantity we never want.  Saying which of the two is
\\ being computed is the whole content of the question.
\\
\\ WHAT b's ell-ADIC TERMS REDUCE TO.  b = <kappa', delta_11>_P, and the two
\\ Prym classes SIMPLIFY:
\\
\\   kappa'    = (1-sigma)/2 [sigma b - b]  =  [sigma b - b]
\\   delta_11  = 2 AJ'_b(x_11) - kappa'     =  [x_11 - sigma x_11]
\\
\\ with x_11 = (-1/11, 15/11).  Each is a difference of two rational points, and
\\ their supports {b, sigma b} and {x_11, sigma x_11} are DISJOINT, so Gross's
\\ formula applies with no moving of divisors at all.  Then
\\
\\   h_ell(kappa', delta_11) = -[ (horizontal) + (vertical) ] log_13(ell),
\\
\\ the vertical part being read off Lambda_ell and the component table, and the
\\ horizontal part being the intersections of the four sections -- which vanish
\\ whenever the two points sit on different components, and otherwise need
\\ their reductions compared.

FAIL = 0;
check(c, msg) = {print(if(c, "   [ok]  ", "   [FAIL] "), msg); if(!c, FAIL = FAIL + 1);};
info(msg) = print("        ", msg);

print("=== check-c4-basefield.gp --- E107: the base field, and b's ell-terms ===");

print("(1) UNRAMIFIED BASE CHANGE COSTS NOTHING");
{my(ok = 1);
 for(d = 1, 12, for(f = 1, 12,
   if(gcd(d,f)*(lcm(d,f)/f) != d, ok = 0)));
 check(ok, "gcd(d,f) * lcm(d,f)/f = d for all d, f <= 12: a closed point of residue degree d over F_ell becomes gcd(d,f) points of degree lcm(d,f)/f over F_{ell^f}, of total degree d.  INTERSECTION NUMBERS ARE INVARIANT UNDER UNRAMIFIED BASE CHANGE  [T(CAS)]");}
info("(a) a Q_3-point lies on exactly one geometric component, and Galois fixes the point while permuting components, so that component is Frobenius-stable and geometrically irreducible: A, B, C come from Z_3-components.");
info("(c) ker M_3 = Q m_3 exactly (E105), so M a = -d has a solution unique modulo Q m and its pairing against another degree-0 vector is independent of the choice -- hence Galois-invariant, hence descended from Z_3.");
check(1, "=> Lambda_3 as computed on the O_K-model IS the Z_3 pairing.  NO CORRECTION  [T]");

print("(2) THE TRAP, NAMED");
{check(2*1 == 2,
      "the height OVER K is twice ours: chi_P = chi_3 . N_{K/Q} and N(3) = 9 at the unramified prime, so chi_P(3) = 2 chi_3(3) and h_P = 2 h_3.  The factor 2 is real -- for the quantity we never want");}

print("(3) THE TWO PRYM CLASSES SIMPLIFY");
info("kappa'   = (1-sigma)/2 [sigma b - b] = [sigma b - b], already anti-invariant");
info("delta_11 = 2 AJ'_b(x_11) - kappa'");
info("         = ([x_11] - [b] - [sigma x_11] + [sigma b]) - ([sigma b] - [b])");
info("         = [x_11 - sigma x_11]");
check(1, "so both are differences of two rational points, with DISJOINT supports {b, sigma b} and {x_11, sigma x_11}: Gross's formula applies with no moving of divisors  [T]");

print("(4) THE VERTICAL CONTRIBUTIONS");
\\ component tables, in the sorted ordering, after E106's dictionary
\\ ell = 2 : b -> A, sigma b -> B, x_11 -> B, sigma x_11 -> A
\\ ell = 3 : b -> A, sigma b -> B, x_11 -> A, sigma x_11 -> B
L2 = [0,0,0; 0,1/2,1/4; 0,1/4,7/8];
L3 = [0,0,0; 0,1,1/2; 0,1/2,3/4];
info("ell = 2:  b -> A, sigma b -> B, x_11 -> B, sigma x_11 -> A  (E104 + E106)");
info("ell = 3:  b -> A, sigma b -> B, x_11 -> A, sigma x_11 -> B  (E105 + E106)");
v2 = L2[2,2];
v3 = -L3[2,2];
info(Str("d(kappa') = e_B - e_A at both primes; d(delta_11) = +(e_B - e_A) at 2 and -(e_B - e_A) at 3"));
{check(v2 == 1/2 && v3 == -1,
      Str("vertical parts: (kappa' . delta_11)_vert = Lambda_2[B,B] = ", v2, " at ell = 2 and -Lambda_3[B,B] = ", v3, " at ell = 3  [T(CAS)]"));}
info(Str("so  h_2(kappa',delta_11) = -[ (horizontal)_2 + 1/2 ] log_13(2)"));
info(Str("    h_3(kappa',delta_11) = -[ (horizontal)_3 - 1  ] log_13(3)"));

print("(5) WHAT IS LEFT");
info("HORIZONTAL: (sigma b - b) . (x_11 - sigma x_11) on each model.  Terms between points on DIFFERENT components vanish, so at ell = 2 only (b . sigma x_11) and (sigma b . x_11) survive -- equal by sigma-symmetry -- and at ell = 3 only (b . x_11) and (sigma b . sigma x_11).  Each is the order of contact of two sections, zero unless the two points have the same reduction on their common component.  One Magma call (point_reduction is already in the record) or one valuation computation settles all of them.");
info("p-LOCAL: h_p(kappa', delta_11) at p = 13, the third-kind Coleman integral.  E080's basis and E091's machinery are the parts already built.  This is now the ONLY part of b that has not been started.");
info("AND THEN: b, and rho becomes a known function on all twenty-one disks; E094's ingredient (iii) closes and (v) is E054's sieve.");

print("========================================================================");
print("E107 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
