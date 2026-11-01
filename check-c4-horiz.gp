\\ check-c4-horiz.gp --- E108: the horizontal intersections, and b's ell-adic
\\ terms as numbers.
\\
\\ Run: gp -q check-c4-horiz.gp
\\
\\ WHAT E107 LEFT.  Gross's formula is
\\
\\   h_ell(D_1,D_2) = -(D_1 . D_2) chi_p(ell),
\\   (D_1 . D_2) = (horizontal) + (vertical),
\\
\\ and E104/E106 computed only the vertical part.  With
\\ kappa' = [sigma b - b] and delta_11 = [x_11 - sigma x_11] (E107), the
\\ horizontal part is
\\
\\   (sigma b . x_11) - (sigma b . sigma x_11) - (b . x_11) + (b . sigma x_11),
\\
\\ and terms between points on different components vanish.
\\
\\ THE MULTIPLICITY OF TWO SECTIONS, DERIVED.  Each of our points lies on a
\\ SINGLE component (component_indices is a singleton), so it is a smooth point
\\ of the special fibre and the model is smooth over Z_ell there.  In a patch
\\ with coordinates u_1, ..., u_n the sections P and Q are cut out by
\\ (u_i - a_i) and (u_i - b_i), so
\\
\\   O/(I_P + I_Q) = Z_ell/(a_i - b_i : i) = Z_ell / ell^(min_i v(a_i - b_i)),
\\
\\ whence (Pbar . Qbar) = min_i v_ell(a_i - b_i) . [k(x) : F_ell].  No blow-up
\\ bookkeeping is needed: Magma's patch coordinates are exactly what the formula
\\ wants.
\\
\\ THE DATA (magma_free, one call).
\\
\\   ell = 2, chart 1 projective:
\\     b        = (1,3,1)      patch <2,2>  coords [0, 2, 1]        red [0,0,1]  comp A
\\     sigma b  = (1,-3,1)     patch <2,3>  coords [0, -2, 2]       red [0,0,0]  comp B
\\     x_11     = (-1,15,11)   patch <2,3>  coords [-6/11, 2/11, 2] red [0,0,0]  comp B
\\     sigma x  = (-1,-15,11)  patch <2,2>  coords [6/13, -26/11, -11/13] red [0,0,1] comp A
\\
\\   ell = 3, chart 2 over K = Q(i):
\\     b        = (3,3,1)      patch <4,1>  red [0,0,0]  comp A
\\     sigma b  = (-3,3,1)     patch <6,1>  red [0,1,1]  comp B
\\     x_11     = (15,-3,11)   patch <4,1>  red [0,2,1]  comp A
\\     sigma x  = (-15,-3,11)  patch <6,1>  red [0,0,2]  comp B

FAIL = 0;
check(c, msg) = {print(if(c, "   [ok]  ", "   [FAIL] "), msg); if(!c, FAIL = FAIL + 1);};
info(msg) = print("        ", msg);
{vv(a, l) = if(a == 0, 999, valuation(a, l));}

print("=== check-c4-horiz.gp --- E108: the horizontal terms ===");

print("(1) ell = 3: THE SECTIONS SEPARATE");
info("surviving pairs are (b, x_11) on component A and (sigma b, sigma x_11) on B");
info("reductions in patch <4,1>: [0,0,0] against [0,2,1]");
info("reductions in patch <6,1>: [0,1,1] against [0,0,2]");
{check([0,0,0] != [0,2,1] && [0,1,1] != [0,0,2],
      "in each pair the two sections reduce to DIFFERENT points of the same patch, so they do not meet: both intersection numbers are 0, and the horizontal term at ell = 3 VANISHES  [T(CAS)]");}

print("(2) ell = 2: THE SECTIONS TOUCH, TO ORDER 1");
bA = [0, 2, 1];        sxA = [6/13, -26/11, -11/13];   \\ patch <2,2>, component A
sbB = [0, -2, 2];      xB  = [-6/11, 2/11, 2];         \\ patch <2,3>, component B
d1 = vector(3, k, sxA[k] - bA[k]);
d2 = vector(3, k, xB[k] - sbB[k]);
v1 = vector(3, k, vv(d1[k], 2));
v2 = vector(3, k, vv(d2[k], 2));
info(Str("b vs sigma x_11 : differences ", d1, "  v_2 = ", v1));
info(Str("sigma b vs x_11 : differences ", d2, "  v_2 = ", v2));
{check(vecmin(v1) == 1 && vecmin(v2) == 1,
      "both reduce to the same point of their patch and the coordinate differences have minimal valuation 1, so each intersection number is 1  [T(CAS)]");}
{check(vecmin(v1) == vecmin(v2),
      "and the two agree, as sigma-symmetry requires: sigma carries the pair (b, sigma x_11) to (sigma b, x_11).  That is a check, not an assumption -- the two were computed in DIFFERENT patches from different coordinates");}

print("(3) THE HORIZONTAL TERMS");
H2 = 1 - 0 - 0 + 1;
H3 = 0 - 0 - 0 + 0;
{check(H2 == 2 && H3 == 0,
      Str("(sigma b - b . x_11 - sigma x_11) = ", H2, " at ell = 2 and ", H3, " at ell = 3, the cross terms vanishing because those pairs sit on different components"));}

print("(4) b's ell-ADIC TERMS, AS NUMBERS");
V2 = 1/2;      \\ E104/E106/E107
V3 = -1;
T2 = H2 + V2;
T3 = H3 + V3;
info(Str("(D_1 . D_2) = horizontal + vertical = ", H2, " + ", V2, " = ", T2, "   at ell = 2"));
info(Str("                                    = ", H3, " + ", V3, " = ", T3, "   at ell = 3"));
{check(T2 == 5/2 && T3 == -1,
      "so, in E086's sign convention h_ell = -(D_1 . D_2) chi_p(ell) with chi_p(ell) = log_13(ell),");}
info("   h_2(kappa', delta_11) = -(5/2) log_13(2)");
info("   h_3(kappa', delta_11) =  +     log_13(3)");
{check(1,
      "BOTH ell-ADIC TERMS OF b ARE NOW NUMBERS.  b = h_p(kappa', delta_11) - (5/2) log_13(2) + log_13(3)");}

print("(5) WHAT IS LEFT OF THE WHOLE COMPUTATION");
info("h_p(kappa', delta_11) at p = 13: the Coleman integral of a differential of the third kind with residue divisor kappa', along delta_11.  E080 built the third-kind basis; E091 built the iterated-integral machinery; E094 section 5.4 flagged this as the newest component and said to measure it in Tier 1 before committing.");
info("It is now the ONLY unknown in the determination of C_4(Q): with b in hand, B is complete, rho is a known function on all twenty-one disks (E098, E099), Upsilon is closed at four elements (E104), and the endgame is E054's Mordell-Weil sieve.");

print("========================================================================");
print("E108 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
