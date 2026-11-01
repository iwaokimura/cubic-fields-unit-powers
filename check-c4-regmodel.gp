\\ check-c4-regmodel.gp --- E103: the regular model of C_4 over Z_2, from
\\ Magma, and everything about it that can be verified without Magma.
\\
\\ Run: gp -q check-c4-regmodel.gp
\\
\\ WHY MAGMA, AND WHICH MODEL.  E097 stopped Gamma_2 because a regular
\\ SEMISTABLE model needs 24 | e.  But the two things we want from ell = 2 are
\\ different objects:
\\
\\   (A) Upsilon, via Betts-Dogra Theorem 3.2  -> regular SEMISTABLE over O_K,
\\                                                24 | e.  Out of reach.
\\   (B) b = <kappa', delta_11>_P, via Coleman-Gross -> the ell-local term is
\\       Gross's intersection formula h_ell(D_1,D_2) = -(D_1 . D_2) chi_p(ell)
\\       on a model that need only be REGULAR, over Z_2 itself.  No base change.
\\
\\ and (B) is the only unknown left in Phase 5.  So the call to make is
\\ RegularModel(C_4, 2) over Q, with no extension at all.
\\
\\ WHAT WAS SENT AND WHAT CAME BACK (magma_free, five calls, ~1 s each,
\\ 2026-08-18, with the user's permission; the precedent is E043).
\\
\\   P<X,Y,Z> := PolynomialRing(Rationals(), 3);
\\   F := Y^4 - 6*(X-Z)^2*Y^2 + 27*X^4 - 108*X*Z^3;
\\   C := Curve(ProjectiveSpace(P), F);
\\   M2 := RegularModel(C, 2);
\\
\\ Magma 2.29-9 confirmed Genus(C) = 3 and IsNonsingular(C) = true, and
\\ returned the model in 0.11 s of CPU.  Three things were learned that no
\\ amount of local work would have given:
\\
\\   * THE AFFINE MODEL IS REJECTED.  RegularModel(C_affine, 3) fails with
\\     "Bad affine curve (there are nonregular points at infinity on the
\\     special fibre)".  The projective quartic is accepted.
\\   * ell = 3 IS BLOCKED, and by the implementation rather than by us:
\\     "WARNING: Extending the base field to Number Field with defining
\\     polynomial x^2+2x+2" then "Runtime error: Fibre blowups over number
\\     fields not yet implemented".  The singular point of the special fibre at
\\     3 is defined over F_9, and Dokchitser's package does not blow up over
\\     number fields.  No change of model avoids this: the residue field of the
\\     singularity is intrinsic.
\\   * ell = 2 SUCCEEDS.  Six components, multiplicities [1,1,1,2,2,4],
\\     the intersection matrix below, and ComponentGroup = Z/8.
\\
\\ THIS GATE DOES NOT RE-RUN MAGMA.  It records the output as data and checks
\\ everything about it that is checkable from first principles -- which turns
\\ out to be a great deal, including an independent reproduction of Magma's
\\ component group from its own intersection matrix.

FAIL = 0;
check(c, msg) = {print(if(c, "   [ok]  ", "   [FAIL] "), msg); if(!c, FAIL = FAIL + 1);};
info(msg) = print("        ", msg);

M = [-3,1,0,1,0,0; 1,-3,0,1,0,0; 0,0,-4,0,2,0; 1,1,0,-3,0,1; 0,0,2,0,-3,1; 0,0,0,1,1,-1];
mult = [1,1,1,2,2,4]~;
CG = 8;
e(i) = my(v = vectorv(6)); v[i] = 1; v;

print("=== check-c4-regmodel.gp --- E103: the regular model of C_4 over Z_2 ===");

print("(1) THE SPECIAL FIBRE IS A GENUINE ONE");
info(Str("multiplicities ", mult~, ",  component group Z/", CG, " (Magma)"));
{for(i = 1, 6, info(Str("   ", M[i,])));}
check(M == mattranspose(M), "the intersection matrix is symmetric");
check(M*mult == vectorv(6), "M m = 0: the whole fibre meets every component in degree 0, which is the defining property of a fibre and the first thing a wrong matrix would break");
check(matrank(M) == 5 && matker(M) == Mat(mult), "M has rank 5 and its kernel is spanned by m EXACTLY -- Zariski's lemma, so the fibre is connected and the multiplicities are the right ones");
{my(cp = charpoly(M), ok = 1);
 for(k = 0, 6, if(polcoef(cp, k) < 0, ok = 0));
 check(ok, Str("charpoly(M) = ", cp, " has no negative coefficient, so no positive real root: M is NEGATIVE SEMIDEFINITE, as an intersection matrix on a fibre must be"));}

print("(2) MAGMA'S COMPONENT GROUP, REPRODUCED FROM MAGMA'S OWN MATRIX");
{my(ok = 1);
 for(i = 1, 6,
   my(N = matrix(5, 5, a, b, M[if(a<i,a,a+1), if(b<i,b,b+1)]));
   if(abs(matdet(N)) != CG*mult[i]^2, ok = 0);
   info(Str("   delete component ", i, " (multiplicity ", mult[i], "): |det| = ", abs(matdet(N)), " = ", CG, " * ", mult[i], "^2")));
 check(ok, Str("|det M^(i)| = |Phi| m_i^2 for EVERY i, the classical formula, with |Phi| = ", CG));}
{my(sn = matsnf(M), t = select(x -> x > 1, sn));
 info(Str("Smith normal form of M: ", sn));
 check(#t == 1 && t[1] == CG, Str("so Z^6/im(M) has torsion Z/", CG, ": Magma's ComponentGroup recovered from Magma's IntersectionMatrix, by a computation Magma did not do"));}

print("(3) THE POINTS, AND ONE THING THAT DOES NOT ADD UP");
info("PointOnRegularModel reported, for the nine rational points:");
info("   t =  1, w = +-3        -> component_indices 2, 3");
info("   t = -1, w = +-3        -> component_indices 2, 3");
info("   t = -1/11, w = +-15/11 -> component_indices 3, 2");
info("   t = -2, w = +-6        -> component_indices 5, 5");
info("   t =  0, w = 0          -> component_indices 5");
info("The partition that induces -- {1, -1, -1/11} apart from {-2, 0} -- is EXACTLY E092's cluster rule at ell = 2, and exactly E098's j_2.");
{check(mult[5] != 1,
      "BUT component 5 has multiplicity 2, and a Q_2-point CANNOT lie on a component of multiplicity > 1: a section s of a regular proper model satisfies sum_k m_k (sbar . Gamma_k) = 1 with every term non-negative, so exactly one k contributes and it has m_k = 1.  Magma's own numbers are therefore not being read correctly");}
info("The likeliest reading is that component_indices is PATCH-LOCAL: the record returned by PointOnRegularModel carries patch_index and gives component_eqns in that patch's coordinates, while Multiplicities and IntersectionMatrix are global.  If so the indices above cannot be compared across points until the patches are matched.");
check(1, "SO THE PARTITION IS RECORDED AS SUGGESTIVE AND NOT USED.  It agrees with E092, which is encouraging; but E092's rule is not promoted on the strength of an index whose meaning is unsettled");

print("(4) WHAT THIS OPENS, AND WHAT IT DOES NOT");
info("OPENED: the ell = 2 half of route (B).  Gross's formula needs the intersection matrix above and, for each divisor, which components it meets; the first is in hand and verified, the second is one Magma accessor away.  The local pairing is then (d_1)^T M^+ (d_2) chi_p(2) with M^+ the pseudo-inverse, and M's kernel being exactly Q m makes that well posed.");
info("NOT OPENED: ell = 3, which Magma's implementation refuses (F_9), and where E083's semistable model is over a ramified extension and gives no Z_3-intersection matrix.  And Upsilon still needs the SEMISTABLE model over 24 | e, which none of this touches.");
info("ALSO NOT OPENED: the p-local term of Coleman-Gross at p = 13, which remains the largest new component of route (B) -- E080's third-kind basis and E091's iterated integrals are the parts already built.");
info("COST: five magma_free calls, about a second each, well inside the 120 s limit.  The limit was never the obstacle; the obstacles were the model form (affine rejected), the residue field at 3, and now an indexing convention.");

print("========================================================================");
print("E103 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
