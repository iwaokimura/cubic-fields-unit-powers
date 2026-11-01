\\ check-prym-rank.gp --- E044: everything local for the rank of the Prym.
\\
\\ WHAT THIS IS FOR.  E039(e) produced, via Ritzenthaler-Romagny Thm 1.1, an
\\ explicit genus-2 curve X over K = Q(4^(1/3)) with Jac(X) ~ P, the Prym of
\\ C_4 -> E, and E039's verdict recorded that
\\        rank_Q(P) <= rank_K(Jac X)
\\ but that a genus-2 descent over a cubic field was "beyond PARI/GP and Sage".
\\ It still is.  The one step that has to leave this machine is therefore
\\ TwoSelmerGroup(Jac X / K); everything else -- the model, the scaling, the
\\ factorisation, the 2-torsion -- is done here, and this script prints the exact
\\ Magma block to evaluate, so that the remote step has visible provenance.
\\
\\ WHY THE RANK OF P MATTERS, TWICE.
\\   * rank_Q(P) >= 2 is what makes "classical Chabauty is unavailable at q = 4"
\\     (E038, currently [P]) a theorem;
\\   * rank_Q(Jac C_4) = 1 + rank_Q(P) = 3 = g is the standing hypothesis of
\\     quadratic Chabauty (E043 Next Step (i)).
\\
\\ THE 2-TORSION, DERIVED HERE RATHER THAN ASKED FOR.  For y^2 = f(x) with f of
\\ degree 6 and no repeated roots, J[2] is the group of even-cardinality subsets
\\ of the six Weierstrass points modulo complementation, with its Galois action;
\\ the K-rational part is spanned by the Galois-stable subsets.  If f factors
\\ over K into three irreducible quadratics, the orbits are those three pairs,
\\ every union of them has even cardinality, and there are 2^3 / 2 = 4 classes:
\\        dim_F2 J(K)[2] = 2 .
\\ The rank bound then reads rank <= dim_F2 Sel^2 - 2.  (Which convention the
\\ Selmer computation reports is calibrated separately -- see E044;
\\ do not skip that step, it is exactly what went wrong in E041.)

sextic() =
{
  my(T = 'w^3 - 4, A, Ai, aa, bb, cc);
  \\ Theorem 1.1's matrix for our r = 27 T (T^3 - 4 Z^3), as in E039 section 3
  A = [Mod(27,T), Mod(-27*'w,T), Mod(0,T);
       Mod(6,T),  Mod(-12,T),    Mod(6,T);
       Mod(1,T),  Mod('w,T),     Mod('w^2,T)];
  Ai = A^-1;
  aa = Ai[1,1] + 2*Ai[2,1]*'x + Ai[3,1]*'x^2;
  bb = Ai[1,2] + 2*Ai[2,2]*'x + Ai[3,2]*'x^2;
  cc = Ai[1,3] + 2*Ai[2,3]*'x + Ai[3,3]*'x^2;
  return(bb*(bb^2 - aa*cc));
};

magmablock(s) =
{
  my(str = "f := ", c, i);
  forstep(i = 6, 0, -1,
    c = lift(polcoef(s, i, 'x));
    str = concat([str, "(", Str(c), ")*X^", Str(i), if(i > 0, " + ", ";")]));
  return(str);
};

run() =
{
  my(s, s2, nf, fa, degs, i, nfail = 0);
  print("=== 1. the genus-2 curve X/K of E039(e), with integral coefficients ===");
  s = sextic();
  s2 = 108^2 * s;
  printf("  degree %d, discriminant nonzero: %d\n", poldegree(s2), poldisc(s2) != 0);
  printf("  scaling factor 11664 = 108^2 is a SQUARE, so y -> 108y is an\n");
  printf("  isomorphism of curves and the rank is unchanged: %d\n", 11664 == 108^2);
  printf("  coefficients integral over Z[w]: %d\n",
         denominator(content(lift(s2))) == 1);
  if(poldisc(s2) == 0 || denominator(content(lift(s2))) != 1, nfail++);
  print("  (E039's own print of this sextic left the denominators in place --");
  print("   its `denominator(content(lift(sext)))` does not clear them.  Cosmetic,");
  print("   but it is why the model is rebuilt here rather than copied.)");
  print("");

  print("=== 2. factorisation over K and the 2-torsion, derived locally ===");
  nf = nfinit('w^3 - 4);
  fa = nffactor(nf, s2);
  degs = vecsort(vector(#fa[,1], i, poldegree(fa[i,1])));
  printf("  factor degrees over K: %s\n", degs);
  if(degs != [2,2,2]~ && degs != [2,2,2],
     print("  *** FAIL: expected three irreducible quadratics"); nfail++);
  print("  three Galois orbits of size 2 on the Weierstrass points, every union");
  print("  of orbits of even cardinality, 2^3/2 = 4 classes:");
  print("        dim_F2 J(K)[2] = 2      <== so the rank bound is dim Sel^2 - 2");
  print("");

  print("=== 3. the block to evaluate remotely (the only Magma-only step) ===");
  print("  R<x> := PolynomialRing(Rationals());");
  print("  K<w> := NumberField(x^3-4);");
  print("  Kx<X> := PolynomialRing(K);");
  printf("  %s\n", magmablock(s2));
  print("  J := Jacobian(HyperellipticCurve(f));");
  print("  TwoSelmerGroup(J);");
  print("");
  printf("  failures: %d\n", nfail);
  return(nfail);
};

run();
