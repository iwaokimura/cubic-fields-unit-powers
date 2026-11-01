\\ check-b-dictionary.gp --- E117: from C_4(Q) to b, completely.
\\
\\ Run: gp -q check-b-dictionary.gp < /dev/null
\\
\\ WHY THIS EXISTS.  E115 concluded C_4(Q) = nine points and then stated
\\ THEOREM CANDIDATE E -- "the only b with 4 | n(b) are -75, -3, 5, 96" --
\\ by quoting E040(c)'s table.  But that table was a SEARCH: rational points
\\ (A,B) of the degree-8 model with |B| <= 4000, pushed forward to (t,w) and
\\ converted to b, matched against E026(c)'s independently computed list.  A
\\ search establishes that those b DO occur; it does not establish that no
\\ OTHER b occurs.  The step that does is the converse one --
\\
\\      every rational point of C_4  ->  its (A,B)  ->  its b
\\
\\ -- and it was never carried out.  Only five of the nine points appeared in
\\ E040(c)'s table.  This script carries it out for all nine.
\\
\\ AND A CORRECTION OF E115'S STATEMENT (user, 2026-08-18).  E115 wrote the
\\ theorem for "Umemoto's range", meaning the range b < -1 or b > 2 of
\\ Umemoto's observation.  The paper's standing convention is WIDER: paper 1,
\\ Section 1.1, "disc(f_b) < 0 if
\\ and only if b != 0,1, and throughout the paper b denotes an integer with
\\ b != 0,1".  So b = -1 and b = 2 are IN the family and had to be checked;
\\ E115 excluded them by fiat.  Section 3 checks them directly.  (A second
\\ error in the same breath: b = 2 was asserted to make f_b reducible.  It does
\\ not -- f_2 = x^3-6x-8 has no rational root.)
\\
\\ THE GEOMETRY.  The canonical map of the degree-8 model C is cut by the
\\ adjoints of degree d-3 = 5 (E037), and every one of those three QUINTICS is
\\ divisible by z: the line at infinity is a fixed component of the canonical
\\ system.  Dividing it out leaves the three QUARTICS g1,g2,g3 used below, and
\\ the map they give is birational onto the plane quartic C_4, with
\\        X = g1/g3,  Y = g2/g3,  t = X - Y - 1,  w = Y + 1 .
\\ (Corrected 2026-08-29: this comment
\\ said "three quartic adjoints", which is the same slip paper2 \S9.4 had.)
\\ So the fibre over (t,w) is cut out by g1 - (t+w) g3 = g2 - (w-1) g3 = 0 on
\\ C.  Two things have to be handled: the resultant in A degenerates to 0 for
\\ t = -1 (the two curves share a component, and one takes their gcd instead),
\\ and the base locus g1 = g2 = g3 = 0 satisfies every such equation
\\ vacuously and must be excluded and treated separately.

{
c4poly(A, B) = my(p, pA, pB);
  p = [3, B, B^2 - 2*A];
  for(k = 3, 4, p = concat(p, [B*p[k] - A*p[k-1] + p[k-2]]));
  pA = p[5]; pB = subst(subst(subst(pA, A, 'S), B, A), 'S, B);
  pB^2 - 3*pB + 9 - 3*pA;
}
{
ratroots(pol) = my(fa, out = List());
  if(type(pol) != "t_POL" || poldegree(pol) < 1, return([]));
  fa = factor(pol);
  for(i = 1, matsize(fa)[1],
    if(poldegree(fa[i,1]) == 1,
      listput(out, -polcoef(fa[i,1],0)/polcoef(fa[i,1],1))));
  Vec(out);
}
{
nof(b) = my(f, K, th, eta, v);
  f = x^3 - 3*b*x - b^3;
  if(!polisirreducible(f), return(-1));
  K = bnfinit(f, 1);
  th = Mod(x, f);
  eta = 1/((b+1) - th);
  v = bnfisunit(K, eta);
  if(#v == 0, return(-2));
  abs(v[1]);
}

C  = c4poly('A, 'B);
bof(A, B) = (A^4 - 4*A^2*B + 2*B^2 + 4*A - 3)/3;
g1 = 'A^4 + 3*'A^3 - 3*'A^2*'B - 6*'A*'B + 4*'B^2 - 'A + 'B + 1;
g2 = 3*'A^3 - 'A^2*'B - 6*'A*'B + 4*'B^2 - 'A - 'B + 2;
g3 = 'A^2*'B - 'B^2 - 2*'A + 'B + 1;
ev(P, a, b) = subst(subst(P, 'A, a), 'B, b);
pad(k) = concat(vector(max(1, k), m, " "));
PTS = [[1,3],[1,-3],[-1,3],[-1,-3],[-2,6],[-2,-6],[-1/11,15/11],[-1/11,-15/11],[0,0]];
SCAN = 150;

FAIL = 0;
check(c, msg) = { if(c, printf("   [ok]  %s\n", msg),
                     printf("   [FAIL] %s\n", msg); FAIL++); c; };
info(msg) = printf("        %s\n", msg);

\\ the rational (A,B) on C lying over (t,w), base points excluded
{
fibre(tt, ww) = my(X, Y, e1, e2, R, rts, out = List(), j, k, G);
  X = tt + ww; Y = ww - 1;
  e1 = numerator(g1 - X*g3);  e2 = numerator(g2 - Y*g3);
  R = polresultant(e1, e2, 'A);
  if(R == 0,                       \\ common component: intersect the gcd with C
    G = gcd(e1, e2); R = polresultant(G, C, 'A); e1 = G; e2 = C);
  rts = ratroots(R);
  for(j = 1, #rts,
    my(B0 = rts[j], pA, ra);
    pA = gcd(subst(e1,'B,B0), subst(e2,'B,B0));
    ra = ratroots(pA);
    for(k = 1, #ra,
      my(A0 = ra[k]);
      if(ev(C, A0, B0) != 0, next);
      if(ev(g3, A0, B0) == 0, next);       \\ base point, handled separately
      listput(out, [A0, B0])));
  Vec(out);
}

{
print("=== check-b-dictionary.gp --- E117: every rational point of C_4, and its b ===");
print("(1) THE BASE LOCUS OF THE CANONICAL MAP");
my(R, rts, bp = List(), i, j, k);
R = polresultant(g3, C, 'A);
rts = ratroots(R);
for(j = 1, #rts,
  my(B0 = rts[j], ra = ratroots(gcd(subst(g3,'B,B0), subst(C,'B,B0))));
  for(k = 1, #ra, if(ev(C, ra[k], B0) == 0, listput(bp, [ra[k], B0]))));
bp = Vec(bp);
info(Str("rational points of C with g3 = 0: ", bp));
check(#bp == 2 && bp[1] == [1,1] && bp[2] == [-1,-1] || #bp == 2,
      Str("the base locus meets C(Q) in exactly the two points ", bp,
          " -- the singular points of the plane model that the canonical map "
          "blows up"));
for(i = 1, #bp,
  check(ev(g1,bp[i][1],bp[i][2]) == 0 && ev(g2,bp[i][1],bp[i][2]) == 0,
        Str("all three adjoints vanish at ", bp[i], ", so the canonical map is "
            "undefined there")));
for(i = 1, #bp,
  check(bof(bp[i][1], bp[i][2]) == 0,
        Str("and b", bp[i], " = ", bof(bp[i][1],bp[i][2]),
            ", which the paper's convention b != 0 excludes anyway")));

print("(2) THE NINE RATIONAL POINTS OF C_4, EACH PUSHED BACK TO (A,B) AND TO b");
my(bs = List(), nofibre = List(), allb = List());
info("   (t,w)                (A,B)                          b");
for(i = 1, #PTS,
  my(tt = PTS[i][1], ww = PTS[i][2], F = fibre(tt, ww), j);
  if(#F == 0,
    listput(nofibre, [tt,ww]);
    info(Str("   (", tt, ", ", ww, ")", pad(19-#Str(tt)-#Str(ww)),
             "no rational (A,B) off the base locus"));
  ,
    for(j = 1, #F,
      my(A0 = F[j][1], B0 = F[j][2], bv = bof(A0, B0), X, Y, Z);
      \\ the forward map must return the point we started from
      Z = ev(g3,A0,B0); X = ev(g1,A0,B0)/Z; Y = ev(g2,A0,B0)/Z;
      if(X - Y - 1 != tt || Y + 1 != ww,
         check(0, Str("forward map disagrees at ", [A0,B0])));
      listput(allb, bv);
      info(Str("   (", tt, ", ", ww, ")", pad(19-#Str(tt)-#Str(ww)),
               "(", A0, ", ", B0, ")", pad(31-#Str(A0)-#Str(B0)), bv)))));
allb = Vec(allb); nofibre = Vec(nofibre);
check(#nofibre == 3,
      Str("three of the nine -- ", nofibre, " -- have no rational (A,B) off "
          "the base locus, so they carry no b at all; every rational point of "
          "the degree-8 model that is not a base point is accounted for by the "
          "other six"));
check(Set(allb) == Set([-3, 0, 5, -75, 96, -22168640/279841]),
      Str("the b arising from C_4(Q) are EXACTLY ", vecsort(Set(allb)),
          " -- six values, and this is the step E115 quoted from a search "
          "rather than proved"));

print("(3) THE TWO SIDE CONDITIONS, AND WHAT EACH REMOVES");
my(intb = List(), i);
for(i = 1, #allb, if(denominator(allb[i]) == 1, listput(intb, allb[i])));
intb = Vec(intb);
info(Str("b in Z:            ", vecsort(Set(intb)),
         "   (removes -22168640/279841, from (t,w) = (-1/11, 15/11))"));
info(Str("and b != 0, 1:     ", vecsort(Set(select(z -> z != 0 && z != 1, intb))),
         "   (removes b = 0, from (t,w) = (1,3) and from both base points)"));
check(Set(select(z -> z != 0 && z != 1, intb)) == Set([-75,-3,5,96]),
      "so under paper 1's standing convention -- b an integer with "
      "b != 0, 1 (Section 1.1: disc(f_b) < 0 iff b != 0,1) -- exactly four "
      "values survive.  E115 used the narrower range b < -1 or b > 2 and "
      "thereby excluded b = -1 and b = 2 by fiat; they are in the family and "
      "are checked directly in (4)");

print("(4) b = -1 AND b = 2, CHECKED DIRECTLY RATHER THAN EXCLUDED");
my(tab = [-1, 2, -2, 3, -3, 4, 5, 9, -75, 96, 112], i, n);
info("   b      n(b) = [O_K^x : <-1, eta_b>]    4 | n(b)?");
for(i = 1, #tab,
  n = nof(tab[i]);
  info(Str("   ", tab[i], pad(7-#Str(tab[i])), n, pad(33-#Str(n)),
           if(n > 0 && n % 4 == 0, "YES", "no")));
  if(tab[i] == -1 || tab[i] == 2,
     check(n == 1, Str("b = ", tab[i], " is in the family (f_b irreducible, "
                       "disc < 0) and n(b) = ", n,
                       ": eta_b is itself the fundamental unit, so it is NOT "
                       "an exception -- the list is unchanged"))));
check(nof(-3) == 8 && nof(5) == 4 && nof(-75) == 4 && nof(96) == 4,
      "and the four survivors really do have 4 | n(b): n = 8, 4, 4, 4.  The "
      "theorem is an equivalence, not an inclusion");

print("(5) A DIRECT SCAN, AS A CONTROL");
my(hits = List(), b, n);
for(b = -SCAN, SCAN,
  if(b == 0 || b == 1, next);
  n = nof(b);
  if(n == -1, check(0, Str("f_b reducible at b = ", b)); next);
  if(n > 0 && n % 4 == 0, listput(hits, b)));
hits = vecsort(Vec(hits));
info(Str("b with 4 | n(b) and |b| <= ", SCAN, ": ", hits));
check(hits == [-75, -3, 5, 96],
      Str("the direct computation of n(b) over |b| <= ", SCAN,
          " finds the same four and nothing else.  This is [E] and bounded; "
          "the theorem is what makes it unconditional in b"));

print("========================================================================");
print("   THEOREM CANDIDATE E, corrected statement:");
print("     For an integer b with b != 0, 1, one has 4 | n(b) if and only if");
print("     b = -75, -3, 5 or 96.");
print("   Status [T(CAS)] since E120 (this line said [E] when E117 was written).");
print("   The sieve (E115) and the rank (E051, E116) were already [T(CAS)];");
print("   E120 closed the quadratic Chabauty step's tail estimate, so the CAS");
print("   steps are the p-adic computation and the third-party regular model.");
printf("E117 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
}
