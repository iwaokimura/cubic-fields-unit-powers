\\ check-c4-gamma2.gp --- E095 (part 1): the 2-adic geometry of C_4, by Newton
\\ polygons, before the regular model.
\\
\\ Run: gp -q check-c4-gamma2.gp
\\
\\ WHY.  E094 makes Gamma_2 the critical path: the ell = 2 half of Upsilon
\\ and the ell-local terms of any Coleman-Gross height both wait on it, and
\\ E092's cluster rule -- which is what lets E093 write ONE unknown c_2 instead
\\ of two -- is [P].  BDMTV2023 Example 3.3 built the analogous model for C_188
\\ at 2 BY HAND, by a sequence of blow-ups, after Magma's RegularModel and MCLF
\\ both failed; E085 measured that MCLF fails for us too (degree 4, p = 2,
\\ wild).  This gate does the step that comes BEFORE the blow-ups and that
\\ constrains their outcome: the Newton polygon of C_4 over every point of the
\\ t-line, which says where the sheets are and, in particular, where C_4(Q_2)
\\ can and cannot be.
\\
\\ THE COORDINATE.  Mod 2 the plane quartic is the quadruple line (w+t)^4, so
\\ the right coordinate is z := w - t everywhere on the affine patch, and
\\
\\   F(t+z, t) = z^4 + 4t z^3 + (12t-6) z^2 + (-8t^3+24t^2-12t) z
\\               + (22t^4+12t^3-6t^2-108t).
\\
\\ For t of valuation alpha the Newton polygon of this in z gives the
\\ valuations of the four sheets, hence which of them can carry a Q_2-point
\\ (only those of INTEGER valuation can) and where the geometry changes.
\\
\\ WHAT COMES OUT.  Three facts, all exact:
\\   (a) v_2(t) < 0  =>  all four sheets have v(z) = v_2(t) + 1/4.  No point of
\\       C_4(Q_2) lies over a non-integral t AT ALL.
\\   (b) v_2(t) = alpha >= 1  =>  the sheets are {(1+alpha)/2 twice, 1/2
\\       twice}, so there is no Q_2-point over t when alpha is EVEN.
\\   (c) TWO of the four sheets have v(z) = 1/2 for every t: at most two points
\\       of C_4(Q_2) lie over any t.
\\ The shape of the polygon changes only at alpha = 1/2, and no t in Q_2 has
\\ valuation 1/2.  The branch points sit at alpha = 2/3 (E085).  Both numbers
\\ lie strictly between 0 and 1, so the partition of C_4(Q_2) they induce is
\\ exactly "t odd" against "t even or zero" -- which is E092's cluster rule
\\ v_2(t^3-4) > 0.  That is an independent corroboration of the PARTITION; it
\\ is NOT a computation of j_{Gamma_2}, and this gate does not claim one.
\\
\\ WHAT IS STILL MISSING: the components themselves, their intersection matrix,
\\ mu_F, and hence j_{Gamma_2}.  See group (6).

FAIL = 0;
check(c, msg) = {
  print(if(c, "   [ok]  ", "   [FAIL] "), msg);
  if(!c, FAIL = FAIL + 1);
};
info(msg) = print("        ", msg);

F(w, t) = w^4 - 6*(t-1)^2*w^2 + 27*t^4 - 108*t;

\\ valuations of the roots of a one-variable polynomial over Q_ell, with
\\ multiplicity, read off its factorisation over Q_ell.
rootvals(f, ell, acc = 60) = {
  my(g = f/content(f), fa, out = []);
  fa = factorpadic(g, ell, acc);
  for(i = 1, matsize(fa)[1],
    my(h = fa[i,1], e = fa[i,2], d = poldegree(h), v);
    v = (valuation(truncate(polcoef(h, 0)), ell) - valuation(truncate(pollead(h)), ell))/d;
    for(k = 1, e, out = concat(out, vector(d, j, v))));
  vecsort(out);
};

zvals(t0, ell) = rootvals(subst(subst(F(t0 + z, t0), z, x), t, t0), ell);

\\ the Newton polygon of F(t+z,t) in z for a GENERIC t of valuation alpha:
\\ v(c_i) = min_j (v_ell(a_ij) + j*alpha), then the lower convex hull.
Gz = subst(F(t + z, t), z, x);
genval(i, alpha, ell) = {
  my(c = polcoef(Gz, i, x), best = 10^9);
  for(j = 0, poldegree(c, t),
    my(a = polcoef(c, j, t));
    if(a != 0, best = min(best, valuation(a, ell) + j*alpha)));
  best;
};
hullslopes(pts) = {
  my(n = #pts, hull = [pts[1]], cur = 1, out = []);
  while(cur < n,
    my(bs = 10^9, nx = cur);
    for(k = cur+1, n,
      my(s = (pts[k][2] - pts[cur][2])/(pts[k][1] - pts[cur][1]));
      if(s < bs, bs = s; nx = k));
    hull = concat(hull, [pts[nx]]); cur = nx);
  for(k = 1, #hull - 1,
    my(d = hull[k+1][1] - hull[k][1]);
    my(s = (hull[k][2] - hull[k+1][2])/d);
    out = concat(out, vector(d, j, s)));
  vecsort(out);
};
genvals(alpha, ell) = hullslopes(vector(5, i, [i-1, genval(i-1, alpha, ell)]));

print("=== check-c4-gamma2.gp --- E095 (part 1): the 2-adic geometry of C_4 ===");

print("(1) THE BRANCH LOCUS, EXACTLY");
D = poldisc(subst(F(w, t), t, T), w);
Q4 = 2*T^4 + 4*T^3 - 6*T^2 - 8*T - 1;
info(Str("disc_w F = ", D));
check(D == 2^8*3^7*T*(T^3-4)*Q4^2, "disc_w F = 2^8 3^7 t (t^3-4) q(t)^2 with q = 2t^4+4t^3-6t^2-8t-1, so the only primes where the degree-4 map to the t-line degenerates are 2 and 3 -- E093's [T] good reduction away from {2,3}, seen a second way");
check(rootvals(Q4, 2) == [-1/4, -1/4, -1/4, -1/4], "the four roots of q have v_2 = -1/4 and so are not rational: the extra ramification of C_4 -> P^1_t is invisible to Q_2-points");
check(rootvals(T^3 - 4, 2) == [2/3, 2/3, 2/3], "the three branch points t^3 = 4 have v_2 = 2/3, the same as their mutual distances and their distance to the fourth branch point t = 0: all four collide in ONE cluster of depth 2/3, which is what E085 measured p-adically");
check(rootvals(T^3 - 4, 3) == [0, 0, 0] && valuation(poldisc(T^3 - 4), 3) == 3, "at ell = 3 the same three points are units and t = 0 is at distance 0 from them; disc(t^3-4) = -432 = -2^4 3^3 puts their mutual distances at 1/2, a cluster of depth 1/2 NOT containing t = 0.  The two primes see different pictures, which is why h_2 and h_3 had to be separated in the first place");

print("(2) THE NEWTON POLYGON OF F(t+z,t) IN z, OVER EVERY t");
info(Str("F(t+z,t) = ", Gz));
\\ exactval: the minimum defining v(c_i) for generic t of valuation alpha,
\\ together with a flag saying whether it is attained by a SINGLE monomial --
\\ in which case the value is exact for EVERY t of that valuation, not just a
\\ generic one, and the conclusion drawn from it is [T(CAS)] and not [E].
{exactval(i, alpha, ell) = my(c = polcoef(Gz, i, x), best = 10^9, hits = 0);
  for(j = 0, poldegree(c, t), my(a = polcoef(c, j, t));
    if(a != 0, my(v = valuation(a, ell) + j*alpha);
       if(v < best, best = v; hits = 1, if(v == best, hits = hits + 1))));
  [best, hits];}

ok = 1; uniq = 1; above = 1;
{for(k = 1, 12, my(al = -k/2, v0 = exactval(0, al, 2));
  if(genvals(al, 2) != vector(4, j, al + 1/4), ok = 0);
  if(v0[2] != 1 || exactval(4, al, 2) != [0, 1], uniq = 0);
  for(i = 1, 3, if(exactval(i, al, 2)[1] <= v0[1]*(4-i)/4, above = 0)));}
check(ok && uniq && above, "v_2(t) = alpha < 0  =>  all four sheets have v(z) = alpha + 1/4.  This is EXACT and not generic: v(c_0) = 1+4 alpha is attained by the single monomial 22t^4 and v(c_4) = 0 by 1, so the segment joining them is what it is for EVERY such t, while c_1, c_2, c_3 can only rise above their generic values, which already lie strictly above that segment.  NO POINT OF C_4(Q_2) LIES OVER A NON-INTEGRAL t  [T(CAS)]");
ok = 1; uniq = 1;
{for(al = 2, 12, if(genvals(al, 2) != vecsort([1/2, 1/2, (1+al)/2, (1+al)/2]), ok = 0);
  for(i = 0, 4, if(exactval(i, al, 2)[2] != 1, uniq = 0)));}
check(ok && uniq, "v_2(t) = alpha >= 2  =>  the sheets are {1/2, 1/2, (1+alpha)/2, (1+alpha)/2}, and here EVERY coefficient valuation is attained by a single monomial (c_0 by -108t, c_1 by -12t, c_2 by -6, c_3 by 4t), so the polygon is exact for every such t.  For alpha EVEN none of these is an integer: THERE IS NO Q_2-POINT OVER ANY t WITH v_2(t) EVEN AND AT LEAST 2, and for alpha ODD there are exactly two candidate sheets  [T(CAS)]");
check(exactval(0, 1, 2) == [3, 2] && exactval(1, 1, 2) == [3, 1] && exactval(2, 1, 2) == [1, 1] && exactval(4, 1, 2) == [0, 1], "alpha = 1 is the ONE stratum where a minimum is attained twice: v(c_0) = 3 comes from -6t^2 AND -108t together, so it depends on t beyond its valuation.  Everything else there is exact, in particular c_2 = 6(2t-1) at 1 and c_4 = 1 at 0, so the two sheets at v(z) = 1/2 survive whatever the cancellation does");
tw = List(); ts = List();
{forstep(u = -15, 15, 2, my(t0 = 2*u, zv = zvals(t0, 2));
  listput(tw, [t0, t0 % 8, zv]);
  listput(ts, [t0 % 8, denominator(zv[3]) == 1]));}
{for(i = 1, #tw, info(Str("t = ", tw[i][1], "   t mod 8 = ", tw[i][2], "   sheets ", tw[i][3])));}
ok = 1;
{for(i = 1, #ts, if(ts[i][2] != (ts[i][1] == 6), ok = 0));}
check(ok, "and the cancellation is governed by t mod 8: for t = 2 mod 8 the two deep sheets sit at 3/2 and carry NO Q_2-point, for t = 6 mod 8 they are integers and do.  The one rational point with v_2(t) = 1 is t = -2, which is 6 mod 8, with sheets {1/2, 1/2, 2, 3} against the generic {1/2, 1/2, 1, 1}");
ok = 1;
{for(k = 1, 11, my(al = k/12, gv = genvals(al, 2));
  if(al < 1/2 && gv != vector(4, j, (1+2*al)/4), ok = 0);
  if(al > 1/2 && gv != vecsort([1/2, 1/2, al, al]), ok = 0));}
check(ok, "and on the annulus 0 < v_2(t) < 1 the polygon has exactly two shapes, meeting at alpha = 1/2: all four sheets at (1+2 alpha)/4 for alpha < 1/2, and {1/2, 1/2, alpha, alpha} for alpha > 1/2.  THE SHAPE CHANGES AT alpha = 1/2 AND NOWHERE ELSE IN 0 < alpha < 1");
check(genvals(1/2, 2) == [1/2, 1/2, 1/2, 1/2], "at alpha = 1/2 itself the polygon is a single segment of slope -1/2: that is the annulus where a component of the special fibre has to appear, and no t in Q_2 reaches it");
info("the branch points sit at alpha = 2/3 and the polygon breaks at alpha = 1/2, both strictly inside (0,1): every t in Q_2 is on one side or the other, never on the transition");

print("(3) t A UNIT: THE STRATIFICATION MOD 8");
psi2(t0) = 11*t0^4 + 6*t0^3 - 3*t0^2 - 54*t0;
ok = 1;
{forstep(t0 = -15, 15, 2,
  my(v = valuation(psi2(t0), 2), zv = zvals(t0, 2));
  info(Str("t = ", t0, "   t mod 8 = ", t0 % 8, "   v_2(psi) = ", v, "   sheets ", zv));
  if(zv != vecsort([1/2, 1/2, 1, v - 1]), ok = 0));}
check(ok, "for every odd t the four sheets are {1/2, 1/2, 1, v_2(psi(t)) - 1} with psi = 11t^4+6t^3-3t^2-54t: TWO sheets of half-integer valuation, always, and two of integer valuation.  So at most two points of C_4(Q_2) lie over any t -- which is exactly what the nine rational points show, two w for each of the four t-values");
ok = 1;
{forstep(t0 = -31, 31, 2,
  my(v = valuation(psi2(t0), 2), r = t0 % 8);
  if((r == 1 || r == 7) && v != 3, ok = 0);
  if((r == 3 || r == 5) && v < 4, ok = 0));}
check(ok, "and v_2(psi) is 3 exactly when t = +-1 mod 8, at least 4 when t = +-3 mod 8: the deepest sheet moves with t mod 8, so the unit disk is NOT one residue class for the model and the blow-up there will need at least three steps");

print("(4) THE NINE RATIONAL POINTS, AND E092'S CLUSTER RULE AT ell = 2");
TS = [1, -1, -2, -1/11, 0];
ok = 1;
{for(i = 1, #TS,
  my(t0 = TS[i], vt, cl, zv);
  vt = if(t0 == 0, "oo", valuation(t0, 2));
  cl = if(t0 == 0, 1, valuation(t0^3 - 4, 2) > 0);
  zv = if(t0 == 0, "(the bad disk)", Str(zvals(t0, 2)));
  info(Str("t = ", t0, "   v_2(t) = ", vt, "   v_2(t^3-4) = ", if(t0 == 0, 2, valuation(t0^3-4, 2)), "   in cluster: ", cl, "   sheets ", zv));
  if(cl != if(t0 == 0, 1, valuation(t0, 2) >= 1), ok = 0));}
check(ok, "on the nine rational points E092's cluster rule v_2(t^3-4) > 0 says exactly the same thing as v_2(t) >= 1: t = -2 and t = 0 inside, t = 1, -1, -1/11 outside.  Group (2) puts the change of shape at v_2(t) = 1/2 and the branch points at 2/3, both between 0 and 1, so the two-block partition the cluster rule predicts is the one the geometry forces on Q_2-points; and no third block can contain one, because non-integral t carries none");
info("this corroborates the PARTITION behind E092's h_2(0,0) = h_2(-2,6).  It does NOT compute j_{Gamma_2}: in BDMTV2023 Example 3.3 the analogous graph had THREE vertices with j = 0, kappa, 2 kappa, and the third one carried exactly the non-integral x that group (2) has just shown is empty for us");

print("(5) THE SAME PROCEDURE AT ell = 3, AS A REGRESSION ON E083/E084");
{for(i = 1, #TS,
  my(t0 = TS[i]);
  info(Str("t = ", t0, "   v_3(t) = ", if(t0 == 0, "oo", valuation(t0, 3)), "   v_3(t^3-4) = ", if(t0 == 0, 0, valuation(t0^3-4, 3)), "   sheets ", if(t0 == 0, "(the bad disk)", Str(zvals(t0, 3))))));}
J3 = [0, 1, 0, 0, 1];      \\ E084's j_Gamma at t = 1, -1, -2, -1/11, 0
J2 = [0, 0, 1, 0, 1];      \\ E093's j_2 at the same five, under E092's rule
\\ j_Gamma is normalised by j(red b) = 0 with b = (1,3), i.e. t = 1.  So the
\\ prediction is not "in the cluster" but "in the OTHER block from t = 1".
clus(t0, ell) = if(t0 == 0, valuation(4, ell) > 0, valuation(t0^3 - 4, ell) > 0);
ok = 1;
{for(i = 1, #TS, my(t0 = TS[i]);
  if((clus(t0, 3) != clus(1, 3)) != J3[i], ok = 0));}
check(ok, "at ell = 3 the cluster rule -- read as 'j = 0 on the block of the base point t = 1, j = 1 on the other' -- reproduces E084's j_Gamma on all five orbits: t = 1, -2, -1/11 are in the cluster with the base point and get 0, t = -1 and t = 0 are outside it and get 1.  Gamma_3 is KNOWN there from an independent semistable model (E083, confirmed by MCLF in E085), so the rule is VERIFIED where it can be verified");
ok = 1;
{for(i = 1, #TS, my(t0 = TS[i]);
  if((clus(t0, 2) != clus(1, 2)) != J2[i], ok = 0));}
check(ok, "and at ell = 2 the SAME reading gives E093's j_2: there t = 1 is OUTSIDE the cluster, so the block that gets 1 is the inside one, {-2, 0}.  The apparent reversal between the two primes is nothing but the base-point normalisation j(red b) = 0, and noticing that is what makes one rule out of what looked like two");
check(zvals(-1, 3) == [0, 0, 0, 0] && zvals(1, 3) == [0, 0, 0, 0], "and at ell = 3 the sheets are all units at t = +-1: the 3-adic degeneration is not visible in this coordinate, which is the honest reason the Newton polygon argument of group (2) is a 2-adic argument and not a general one");

print("(6) WHAT REMAINS");
info("Gamma_2 itself: the components of the special fibre of a regular semistable model over a ramified K/Q_2, their intersection matrix, the edge lengths, mu_F, and j_{Gamma_2} normalised by j(red b) = 0.");
info("What group (2) contributes: K must contain sqrt(2) -- two sheets sit at v(z) = 1/2 for every t, exactly -- and 2^(1/3), the branch depth, so e >= 6.  BDMTV2023 needed K = Q_2(2^(1/3)) for C_188; we need one quadratic step more, because C_4 -> E is itself a WILD double cover at 2.");
info("What groups (2)-(4) contribute to Upsilon: C_4(Q_2) is confined to t = 0, to v_2(t) = 0, to v_2(t) = 1 with t = 6 mod 8, and to v_2(t) odd and at least 3.  Non-integral t and even v_2(t) >= 2 are EMPTY.  So the vertex of Gamma_2 that BDMTV2023's C_188 reached through non-integral x -- the third value of its j -- has no analogue here that a rational point could see.");
info("What is NOT in hand: the components, hence j_{Gamma_2}, hence the split of E092's c_2 into h_2(0,0) and h_2(-2,6).  E093's c_2 = -(3/4)D is INDEPENDENT of that split; only the split is [P].  The next step is the blow-up itself, over K, starting from the two exact strata of group (2) and the mod-8 stratification of groups (2) and (3).");
print("========================================================================");
print("E095 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
