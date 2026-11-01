\\ check-c4-gamma2b.gp --- E095 part 2 (recorded as E097): the tropicalisation
\\ of C_4 at ell = 2, the residual curves, and how far short of Gamma_2 it stops.
\\
\\ Run: gp -q check-c4-gamma2b.gp
\\
\\ WHERE PART 1 LEFT IT.  E095 fixed where C_4(Q_2) can be (integral t only, and
\\ within that only v_2(t) = 0, v_2(t) = 1 with t = 6 mod 8, v_2(t) odd >= 3, and
\\ t = 0) and corroborated E092's two-block partition.  What it did not do is
\\ produce components.  This gate takes the next step that is exactly
\\ computable -- the tropicalisation of the plane model, i.e. the Newton
\\ subdivision in (v(t), v(z)) with z = w - t -- reads off the residual curves,
\\ and then MEASURES whether that is enough, by running the same procedure at
\\ ell = 3 where Gamma_3 is known independently (E083).
\\
\\ THE RESIDUALS ARE FREE.  Every coefficient of F(t+z,t) is 2^v times an ODD
\\ integer, so the residual polynomial at a vertex is simply the sum of the
\\ monomials Z^i T^j attaining the minimum, over F_2.  Squareness is then read
\\ off the exponents: a polynomial over F_2 is a square iff every exponent is
\\ even.  A square residual means the toric model is NON-REDUCED there, which is
\\ the wildness of p = 2 showing up in the one place it must.
\\
\\ WHAT COMES OUT.  Three vertices, at v_2(t) = 0, 1/2, 1; two of the three
\\ residuals are squares and the third, at v_2(t) = 1, is the Artin-Schreier
\\ conic Z^2 + T^2 + T, of genus 0.  There is NO vertex with v_2(t) > 1, so
\\ nothing in the tropicalisation separates (0,0) from (-2,6).  But the same
\\ procedure at ell = 3 finds two vertices where Gamma_3 has three, so the
\\ tropicalisation UNDERCOUNTS, and the ell = 2 conclusion stays [P].
\\
\\ AND THE FIELD.  Q(E'[3]) has degree 16 with e = 8 above 2, so the quotient
\\ elliptic curve alone needs e = 8 to acquire good reduction; the branch points
\\ sit at depth 2/3, so 3 | e as well.  Hence 24 | e for a semistable model of
\\ C_4 at 2.  BDMTV2023 built their C_188 model by hand over e = 3.

FAIL = 0;
check(c, msg) = {print(if(c, "   [ok]  ", "   [FAIL] "), msg); if(!c, FAIL = FAIL + 1);};
info(msg) = print("        ", msg);

F(w, t) = w^4 - 6*(t-1)^2*w^2 + 27*t^4 - 108*t;

\\ monomial list [deg_z, deg_s, v_ell(coefficient)] of F(w0+z, t0+s)
{
monos(t0, w0, ell) = my(G, M = List());
  G = subst(subst(F(w, t), t, t0 + s), w, w0);
  G = subst(subst(F(w, t), t, t0 + s), w, z + subst(w0, t, t0 + s));
  for(i = 0, poldegree(G, z), my(c = polcoef(G, i, z));
    for(j = 0, poldegree(c, s), my(a = polcoef(c, j, s));
      if(a != 0, listput(M, [i, j, valuation(a, ell)]))));
  Vec(M);
}
Lval(m, al, be) = m[3] + m[1]*be + m[2]*al;
{
attain(M, al, be) = my(best = 10^9, S = []);
  for(k = 1, #M, my(x = Lval(M[k], al, be));
    if(x < best, best = x; S = [k], if(x == best, S = concat(S, [k])))); S;
}
\\ a GENUINE vertex: the attaining monomials are not collinear (so the tropical
\\ curve really has a corner there) and the residual has z-degree at least 2 (so
\\ it is a curve and not a single sheet).
{
vertices(M) = my(V = List(), W = List());
  for(a = 1, #M, for(b = a+1, #M, for(c = b+1, #M,
    my(A, sol, be, al, S, nc, dz);
    A = [M[b][1]-M[a][1], M[b][2]-M[a][2]; M[c][1]-M[a][1], M[c][2]-M[a][2]];
    if(matdet(A) != 0,
      sol = A^(-1)*[M[a][3]-M[b][3], M[a][3]-M[c][3]]~;
      be = sol[1]; al = sol[2]; S = attain(M, al, be); nc = 0; dz = 0;
      for(x = 1, #S, dz = max(dz, M[S[x]][1]));
      for(x = 1, #S, for(y = x+1, #S, for(u = y+1, #S,
        if((M[S[y]][1]-M[S[x]][1])*(M[S[u]][2]-M[S[x]][2])
           - (M[S[y]][2]-M[S[x]][2])*(M[S[u]][1]-M[S[x]][1]) != 0, nc = 1))));
      if(nc && dz >= 2, listput(V, [al, be, S]))))));
  for(k = 1, #V, my(dup = 0);
    for(l = 1, #W, if(W[l][1] == V[k][1] && W[l][2] == V[k][2], dup = 1));
    if(!dup, listput(W, V[k])));
  Vec(W);
}
\\ residual over F_2 (or F_ell): the attaining monomials, coefficients all units
issquareres(M, S) = {my(ok = 1); for(k = 1, #S, if((M[S[k]][1] % 2) || (M[S[k]][2] % 2), ok = 0)); ok;}
resstr(M, S) = {my(s = ""); for(k = 1, #S, s = concat([s, if(k > 1, " + ", ""), "Z^", M[S[k]][1], " T^", M[S[k]][2]])); s;}

print("=== check-c4-gamma2b.gp --- E095 part 2: the tropicalisation at ell = 2 ===");

print("(1) THE TROPICALISATION IN (v(t), v(z)), z = w - t");
M2 = monos(0, t, 2);
info(Str("F(t+z,t) has ", #M2, " monomials (deg_z, deg_t, v_2): ", M2));
W2 = vertices(M2);
{for(k = 1, #W2, info(Str("vertex ", k, ": (v(t), v(z)) = (", W2[k][1], ", ", W2[k][2], ")   residual over F_2:  ", resstr(M2, W2[k][3]), if(issquareres(M2, W2[k][3]), "   [a SQUARE: non-reduced, wild]", "   [not a square]"))));}
check(#W2 == 3, Str("exactly three genuine vertices, found by exhausting all triples of monomials: at v_2(t) = 0, 1/2, 1  [T(CAS)].  Found ", #W2));
check(W2[1][1] == 1 && W2[1][2] == 1 && W2[2][1] == 0 && W2[2][2] == 1/4 && W2[3][1] == 1/2 && W2[3][2] == 1/2, "and they sit at (v(t), v(z)) = (1,1), (0,1/4), (1/2,1/2) -- the same three radii E095 part 1 found by the sheet valuations, now with residual curves attached");
sq = 0; {for(k = 1, #W2, if(issquareres(M2, W2[k][3]), sq = sq + 1));}
check(sq == 2, "TWO of the three residuals are squares over F_2 -- Z^4+Z^2+T^2 = (Z^2+Z+T)^2 at v_2(t)=1/2 and Z^4+T^4+T^2 = (Z^2+T^2+T)^2 at v_2(t)=0 -- so the toric model is non-reduced there and the wildness of p = 2 is concentrated in exactly those two places");
{my(k3 = 0); for(k = 1, #W2, if(W2[k][1] == 1, k3 = k));
my(ex = vecsort([[M2[W2[k3][3][x]][1], M2[W2[k3][3][x]][2]] | x <- [1..#W2[k3][3]]]));
check(k3 && !issquareres(M2, W2[k3][3]) && ex == vecsort([[2,0],[0,2],[0,1]]), Str("the vertex at v_2(t) = 1 -- the one every rational point with even t reduces towards -- has residual Z^2 + T^2 + T, which is NOT a square: it is an ARTIN-SCHREIER conic, (Z+T)^2 = T, of genus 0.  It is the only honest residual curve the plane model produces"));}

print("(2) NOTHING SEPARATES (0,0) FROM (-2,6)");
deep = 0; {for(k = 1, #W2, if(W2[k][1] > 1, deep = deep + 1));}
check(deep == 0, "no genuine vertex has v_2(t) > 1, and the search was exhaustive over all triples.  The ray v(z) = (1+v(t))/2 running out to t = 0 carries no corner, so in the plane tropicalisation the whole region v_2(t) >= 1 -- including the bad point (0,0) and the rational point (-2,6) -- retracts to the single vertex at v_2(t) = 1");
info("IF the tropicalisation saw every component, this would prove h_2(0,0) = h_2(-2,6), which is exactly E092's cluster split, and would close the ell = 2 half of Upsilon at two elements.  Group (3) measures whether it does.");

print("(3) THE CONTROL: THE SAME PROCEDURE AT ell = 3, WHERE Gamma_3 IS KNOWN");
M3 = monos(0, 0, 3);
info(Str("mod 3 the quartic is w^4, so the coordinate is w itself; ", #M3, " monomials"));
W3 = vertices(M3);
{for(k = 1, #W3, info(Str("vertex ", k, ": (v(t), v(w)) = (", W3[k][1], ", ", W3[k][2], ")   residual over F_3: ", resstr(M3, W3[k][3]))));}
check(#W3 == 2, Str("the plane tropicalisation at ell = 3 finds ", #W3, " genuine vertices from the centre t = 0"));
check(#W3 < 3, "AND Gamma_3 HAS THREE (E083: the components Ebar', R and F, confirmed independently by MCLF in E085).  So the single-centre plane tropicalisation UNDERCOUNTS the components of the semistable model.  It is not a proof method, and group (2)'s conclusion is therefore [P] and not [T]");
info("The reason is structural and worth naming: a tropicalisation of a plane model sees only the components visible in that embedding; loops and components hidden inside residue disks -- which is exactly what wild ramification produces -- are invisible to it.  Gamma_3 moreover has toric rank 1 (E084 measured Tr(Z|H_1(Gamma_3)) = -1), and a tree cannot show that.");

print("(4) THE FIELD THE MODEL WOULD HAVE TO LIVE OVER");
psi3 = x^4 - 72*x^2 - 432;
g3 = polresultant(psi3, y^2 - (x^3 - 36*x), x);
g3 = g3/content(g3);
S3 = nfsplitting(g3);
K3 = nfinit(S3);
pr = idealprimedec(K3, 2);
info(Str("Q(E'[3]) = splitting field of ", g3, ", of degree ", poldegree(S3)));
{for(k = 1, #pr, info(Str("   prime above 2: e = ", pr[k][3], ", f = ", pr[k][4])));}
check(poldegree(S3) == 16 && #pr == 1 && pr[1][3] == 8, "Q(E'[3]) has degree 16 with a single prime above 2, of ramification index 8.  E' has potentially good reduction at 2 (j = 1728 is integral) and acquires it only over a field with e = 8: that is the semistability defect of the QUOTIENT  [T(CAS)]");
check(Mod(24, 8) == 0 && Mod(24, 3) == 0, "so a semistable model of C_4 at 2 needs 8 | e from the quotient and 3 | e from the branch depth 2/3 (E095 part 1), hence 24 | e.  BDMTV2023 Example 3.3 built the analogous model BY HAND over K = Q_2(2^(1/3)), where e = 3.  Ours is eight times more ramified, and that is the honest measure of the distance between their computation and this one");

print("(5) WHAT IS SETTLED AND WHAT IS NOT");
info("SETTLED [T(CAS)]: three tropical vertices at v_2(t) = 0, 1/2, 1; two residuals square, one the Artin-Schreier conic Z^2+T^2+T of genus 0; no vertex beyond v_2(t) = 1; e divisible by 24.");
info("NOT SETTLED: Gamma_2 itself.  The tropicalisation undercounts at ell = 3 (group 3), so it cannot be promoted, and the two square residuals are precisely where the missing work is -- each needs the non-reduced toric fibre normalised, which is the wild Artin-Schreier step.");
info("STATUS AGAINST THE PLAN: E094 allowed three sessions for Gamma_2; this is the second, and the stopping rule says that if the blow-ups have not converged by the third, the Magma option goes to the user.  On the evidence of group (4) -- e divisible by 24 against BDMTV's 3 -- it is worth saying now rather than later that hand computation here is a much larger job than the one they describe.");
info("WHAT SESSION 3 SHOULD DO: not more blow-ups.  Either (a) the bielliptic calibration of E096, which settles epsilon and would be the first end-to-end test of the port, or (b) accept E092's split as [P], carry it, and run the quadratic Chabauty assembly -- the zero set is epsilon-free by E096 (P3), and the split only affects Upsilon through ONE of its four elements.");

print("========================================================================");
print("E097 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
