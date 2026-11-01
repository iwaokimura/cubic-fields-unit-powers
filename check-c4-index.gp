\\ check-c4-index.gp --- E106: the indexing convention, calibrated at ell = 2
\\ and applied at ell = 3.
\\
\\ Run: gp -q check-c4-index.gp
\\
\\ THE CONTRADICTION, RESOLVED.  E103, E104 and E105 all reported the same
\\ oddity: PointOnRegularModel puts Q-rational points on components that
\\ Multiplicities calls multiplicity 2, which is impossible (a section of a
\\ regular proper model meets a multiplicity-1 component).  One probe of the
\\ model's internals settles it.  The record M`abstract_fibres carries a
\\ multiplicity field, and
\\
\\     ell = 2 :  Multiplicities  = [1, 1, 1, 2, 2, 4]        (SORTED)
\\                abstract_fibres = [4, 1, 1, 2, 1, 2]        (INTERNAL)
\\     ell = 3 :  Multiplicities  = [1,1,1,1,1,1,1,2,2,2]     (SORTED)
\\                abstract_fibres = [2,1,1,1,2,1,1,1,1,2]     (INTERNAL)
\\
\\ So Multiplicities -- and with it IntersectionMatrix, since M m = 0 holds in
\\ that order -- is SORTED by multiplicity, while component_indices indexes the
\\ INTERNAL list.  Read internally, every reported component has multiplicity 1,
\\ and the contradiction disappears.
\\
\\ THE DICTIONARY.  Assuming Magma's sort is stable -- equal multiplicities keep
\\ their internal order -- the translation is determined, and it is CHECKED at
\\ ell = 2 against E104's forced identification, which was obtained without any
\\ reference to Magma's labels at all.
\\
\\ WHAT IT BUYS.  At ell = 3 the translation lands on one of E105's five
\\ admissible triples, so THE ell = 3 LOCAL PAIRING IS DETERMINED.

FAIL = 0;
check(c, msg) = {print(if(c, "   [ok]  ", "   [FAIL] "), msg); if(!c, FAIL = FAIL + 1);};
info(msg) = print("        ", msg);

\\ stable sort of the internal list by multiplicity: internal index -> sorted
{dict(int) = my(n = #int, out = vector(n), pos = 0);
  for(v = 1, vecmax(int),
    for(i = 1, n, if(int[i] == v, pos = pos + 1; out[i] = pos)));
  out;}

print("=== check-c4-index.gp --- E106: the indexing, calibrated ===");

print("(1) ell = 2: THE DICTIONARY, AND E104 REPRODUCED");
M2 = [-3,1,0,1,0,0; 1,-3,0,1,0,0; 0,0,-4,0,2,0; 1,1,0,-3,0,1; 0,0,2,0,-3,1; 0,0,0,1,1,-1];
m2 = [1,1,1,2,2,4]~;
i2 = [4,1,1,2,1,2];
d2 = dict(i2);
info(Str("internal multiplicities ", i2, " -> sorted ", m2~));
info(Str("dictionary internal -> sorted: ", d2));
{check(vector(6, k, i2[k]) == vector(6, k, m2[d2[k]]),
      "the stable sort is consistent: the internal multiplicity of every component equals the sorted multiplicity at its image  [T(CAS)]");}
rep2 = [2, 3, 5];      \\ the components Magma reported for the nine points
{check(vecmin(vector(3, k, i2[rep2[k]])) == 1 && vecmax(vector(3, k, i2[rep2[k]])) == 1,
      Str("READ INTERNALLY, the three reported components ", rep2, " all have multiplicity 1, as a Q_2-point requires.  E103's flagged contradiction was an ordering artefact and nothing more"));}
tr2 = vector(3, k, d2[rep2[k]]);
info(Str("translated: ", rep2, " -> ", tr2, "  (sigma swaps the first two, fixes the third)"));
{check(vecsort([tr2[1], tr2[2]]) == [1, 2] && tr2[3] == 3,
      "and the translation gives exactly E104's forced answer: the sigma-swapped pair is {1,2} and the sigma-fixed component is 3.  E104 got that from the section argument and the automorphisms of (M,m), with NO reference to Magma's labels; the dictionary reproduces it  [T(CAS)]");}

print("(2) ell = 3: THE PAIRING, DETERMINED");
M3 = [-1,0,1,0,0,0,0,0,0,0; 0,-1,1,0,0,0,0,0,0,0; 1,1,-6,0,0,0,0,0,2,0; 0,0,0,-2,0,0,0,0,1,0; 0,0,0,0,-2,0,0,0,1,0; 0,0,0,0,0,-2,0,0,1,0; 0,0,0,0,0,0,-2,0,1,0; 0,0,0,0,0,0,0,-1,0,1; 0,0,2,1,1,1,1,0,-4,1; 0,0,0,0,0,0,0,1,1,-2];
m3 = [1,1,1,1,1,1,1,2,2,2]~;
i3 = [2,1,1,1,2,1,1,1,1,2];
d3 = dict(i3);
info(Str("internal multiplicities ", i3));
info(Str("dictionary internal -> sorted: ", d3));
{check(vector(10, k, i3[k]) == vector(10, k, m3[d3[k]]),
      "the same stable sort is consistent at ell = 3  [T(CAS)]");}
rep3 = [7, 9, 4];      \\ A, B, C as E105 reported them
{check(vecmin(vector(3, k, i3[rep3[k]])) == 1 && vecmax(vector(3, k, i3[rep3[k]])) == 1,
      Str("again the three reported components ", rep3, " have internal multiplicity 1"));}
tr3 = vector(3, k, d3[rep3[k]]);
info(Str("translated: A, B, C = ", rep3, " -> ", tr3));
{check(m3[tr3[1]] == 1 && m3[tr3[2]] == 1 && m3[tr3[3]] == 1,
      "and all three are multiplicity-1 components of M_3 in the sorted ordering");}

e(n, i) = my(v = vectorv(n)); v[i] = 1; v;
{sol3(c, A) = if(c == A, vectorv(10),
   matsolve(matconcat([M3; mattranspose(m3)]), concat(-(e(10,c)-e(10,A)), [0]~)));}
{L3 = matrix(3, 3, a, b, my(s = 0, v = sol3(tr3[a], tr3[1]), w = e(10,tr3[b])-e(10,tr3[1]));
   for(t = 1, 10, s += v[t]*w[t]); s);}
info("Lambda_3 (base on A), in units of -chi_3(3):");
{for(a = 1, 3, info(Str("   ", L3[a,])));}
{check(L3 == mattranspose(L3) && L3[1,] == [0,0,0] && L3[2,2] == 1 && L3[2,3] == 1/2 && L3[3,3] == 3/4,
      "Lambda_3 = [[0,0,0],[0,1,1/2],[0,1/2,3/4]] -- ONE of E105's five admissible values, and now the one.  THE ell = 3 LOCAL PAIRING IS DETERMINED  [T(CAS)]");}

print("(3) THE PAIR OF PAIRINGS");
M2s = M2; m2s = m2;
{sol2(c) = if(c == 1, vectorv(6),
   matsolve(matconcat([M2s; mattranspose(m2s)]), concat(-(e(6,c)-e(6,1)), [0]~)));}
{L2 = matrix(3, 3, a, b, my(s = 0, v = sol2(a), w = e(6,b)-e(6,1));
   for(t = 1, 6, s += v[t]*w[t]); s);}
info("Lambda_2 = [[0,0,0],[0,1/2,1/4],[0,1/4,7/8]]  (E104, unchanged)");
info(Str("Lambda_3 = ", L3[1,], " ", L3[2,], " ", L3[3,]));
{check(L2[2,2] == 1/2 && L2[2,3] == 1/4 && L2[3,3] == 7/8,
      "E104's Lambda_2 recomputed here and unchanged: the two local pairings b needs away from p are now both in hand");}

print("(4) WHAT IS AND IS NOT SETTLED");
info("SETTLED: the ordering convention (Multiplicities and IntersectionMatrix sorted, component_indices internal), the contradiction that flagged it, and the ell = 3 pairing.");
info("ASSUMED: that Magma's sort is STABLE.  It is not documented here; what is checked is that the stable reading is CONSISTENT (every internal multiplicity matches its image) at both primes, and that at ell = 2 it reproduces an identification obtained independently.  Two primes and one independent cross-check.");
info("STILL OPEN: the base field at ell = 3.  That model is over O_K with K = Q(i), residue degree 2, not over Z_3, and the relation between h_p over K and h_3 over Q must be settled before Lambda_3 enters Gross's formula.  No such question at ell = 2, where E103's model is over Z_2 itself.");
info("AND: the p-local Coleman-Gross term at p = 13, which is now the only part of b that has not been started.");

print("========================================================================");
print("E106 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
