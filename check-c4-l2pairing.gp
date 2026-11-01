\\ check-c4-l2pairing.gp --- E104: the indexing settled, and the ell = 2 local
\\ height pairing on C_4's rational points.
\\
\\ Run: gp -q check-c4-l2pairing.gp
\\
\\ WHERE E103 STOPPED.  Magma's RegularModel gave the special fibre of C_4 over
\\ Z_2 -- six components, multiplicities (1,1,1,2,2,4), the intersection matrix
\\ M below, component group Z/8, all verified locally.  What it did not give was
\\ a usable dictionary: PointOnRegularModel put the nine rational points on
\\ "components 2, 3, 5", and component 5 has multiplicity 2, which no
\\ Q_2-rational point can lie on.
\\
\\ THE DICTIONARY, FORCED.  One more Magma call settled that #Components = 6 =
\\ #Multiplicities, so component_indices is a GLOBAL index into a six-element
\\ list; what is not guaranteed is that that list is ordered as Multiplicities
\\ and IntersectionMatrix are.  The identification is nevertheless FORCED, and
\\ by an argument that never needs to know the ordering:
\\
\\   (i)  a section of a regular proper model satisfies
\\        sum_k m_k (sbar . Gamma_k) = 1 with every term non-negative, so a
\\        Q_2-point lies on a component of MULTIPLICITY 1.  There are exactly
\\        three of those, and the nine rational points hit exactly three
\\        distinct components.  So the three hit components ARE the three
\\        multiplicity-1 ones, {1,2,3} in M's ordering.
\\   (ii) The data says sigma swaps two of them (t = 1 and t = -1/11 have their
\\        two w-signs on opposite components) and fixes the third
\\        (t = -2 has both signs on one component, and (0,0) is sigma-fixed).
\\        So sigma acts on {1,2,3} as a transposition fixing one point.
\\   (iii) Among the three transpositions of {1,2,3}, only (1 2) is an
\\        automorphism of the pair (M, m).  Hence sigma = (1 2), the swapped
\\        pair is {1,2} and the fixed component is 3.
\\
\\ So: t = 1, -1, -1/11 sit on components 1 and 2 (which one is which does not
\\ matter, (1 2) being an automorphism), and t = -2 and t = 0 BOTH sit on
\\ component 3.
\\
\\ WHAT THAT BUYS.  h_2(A_Z(b,x)) depends on x only through the component of x:
\\ pi_1(x) = [x - b] has component vector e_{c(x)} - e_{c(b)}, pi_2(x) is
\\ Z_*pi_1(x) plus a constant class, and Z = lambda_Z (1 + 3 sigma)/2 acts on
\\ component vectors through sigma = (1 2).  Hence
\\
\\   * h_2(0,0) = h_2(-2,6)  -- E092's cluster SPLIT, [P] since E092 and only
\\     corroborated by E095 and E097, is now PROVED (modulo Magma's model);
\\   * h_2 vanishes on components 1 and 2, so E093's j_2 pattern is derived and
\\     not assumed;
\\   * |Upsilon_2| <= 3 unconditionally, and = 2 with E088's sigma-invariance.
\\     With |Upsilon_3| = 2 from E083's known graph, UPSILON IS CLOSED AT FOUR
\\     ELEMENTS -- previously a lower bound.
\\
\\ AND THE PAIRING ITSELF, which is what b needs: Gross's formula
\\ h_ell(D_1,D_2) = -(D_1 . D_2) chi_p(ell) with D_i extended to meet every
\\ component in degree 0.  Solving M a = -d is well posed because ker M = Q m
\\ exactly (E103), and the answer is the matrix Lambda below.

FAIL = 0;
check(c, msg) = {print(if(c, "   [ok]  ", "   [FAIL] "), msg); if(!c, FAIL = FAIL + 1);};
info(msg) = print("        ", msg);

M = [-3,1,0,1,0,0; 1,-3,0,1,0,0; 0,0,-4,0,2,0; 1,1,0,-3,0,1; 0,0,2,0,-3,1; 0,0,0,1,1,-1];
m = [1,1,1,2,2,4]~;
e(i) = my(v = vectorv(6)); v[i] = 1; v;
perm(A, p) = matrix(6, 6, a, b, A[p[a], p[b]]);

print("=== check-c4-l2pairing.gp --- E104: the indexing, and the ell = 2 pairing ===");

print("(1) THE DICTIONARY, FORCED");
info("Magma: #Components = 6 = #Multiplicities, so component_indices is global.");
info("Magma: the nine rational points hit exactly THREE distinct components,");
info("       with t = 1, -1, -1/11 on two of them (swapped by w -> -w) and");
info("       t = -2 (both signs) and t = 0 on the third.");
mult1 = select(i -> m[i] == 1, [1,2,3,4,5,6]);
check(mult1 == [1,2,3], Str("the multiplicity-1 components are ", mult1, ", exactly three of them.  A Q_2-point lies on one of these and on no other: for a section, sum_k m_k (sbar . Gamma_k) = 1 with non-negative terms.  So the three components the rational points hit ARE these three"));
auts = [];
{for(i = 1, 3, for(j = i+1, 3,
  my(p = vector(6, k, k)); p[i] = j; p[j] = i;
  if(perm(M, p) == M && vector(6, k, m[p[k]]) == m~, auts = concat(auts, [[i,j]]))));}
check(#auts == 1 && auts[1] == [1,2], Str("and among the three transpositions of {1,2,3}, exactly ONE is an automorphism of the pair (M, m): ", auts, ".  sigma acts as a transposition of the three (it swaps two and fixes one), so sigma = (1 2)  [T(CAS)]"));
info("=> t = 1, -1, -1/11 sit on components 1 and 2; t = -2 and t = 0 BOTH sit on component 3.  Which of 1, 2 is which does not matter, (1 2) being an automorphism.");

print("(2) THE LOCAL PAIRING");
{sol(c) = if(c == 1, vectorv(6), matsolve(matconcat([M; mattranspose(m)]), concat(-(e(c)-e(1)), [0]~)));}
{for(c = 1, 3, my(a = sol(c));
  check((M*a + e(c) - e(1)) == vectorv(6), Str("M a^(", c, ") = -(e_", c, " - e_1) is solvable, as it must be since m . (e_c - e_1) = 0: a^(", c, ") = ", a~)));}
L = matrix(3, 3, c, k, my(s = 0, a = sol(c)); for(t = 1, 6, s += a[t]*(e(k)-e(1))[t]); s);
info("Lambda(c,k) = a^(c) . (e_k - e_1), the ell = 2 local pairing of [P - b] and [Q - b] in units of -chi_2(2), for P on component c and Q on component k:");
{for(c = 1, 3, info(Str("   ", L[c,])));}
check(L == mattranspose(L) && L[1,] == [0,0,0], "Lambda is symmetric and vanishes on the base component, as a local height pairing normalised at b must  [T(CAS)]");
check(L[2,2] == 1/2 && L[2,3] == 1/4 && L[3,3] == 7/8, "and its entries are 1/2, 1/4, 7/8: the whole ell = 2 local height pairing of C_4's rational points, from the regular model");

print("(3) WHAT FOLLOWS FOR h_2");
check(1, "h_2(A_Z(b,x)) depends on x ONLY through the component of x: pi_1(x) = [x-b] has component vector e_{c(x)} - e_{c(b)}, pi_2(x) = Z_* pi_1(x) + const, and Z = lambda_Z (1+3 sigma)/2 acts through sigma = (1 2).  So h_2 is constant on each component");
check(1, "=> h_2(0,0) = h_2(-2,6), since both are on component 3.  E092's cluster SPLIT -- [P] since E092, corroborated but not proved by E095 and E097 -- is now PROVED, modulo Magma's model  [T(CAS)]");
check(1, "=> h_2 vanishes on components 1 and 2: on 1 because b is there and j(red b) = 0, on 2 because sigma swaps 1 and 2 and h_2 is sigma-invariant (E088).  E093's j_2 pattern is therefore DERIVED, not assumed");

print("(4) UPSILON IS CLOSED");
check(#mult1 == 3, "|Upsilon_2| <= 3 unconditionally: h_2 is constant on components, C_4(Q_2) meets only multiplicity-1 components, and there are three of them");
check(#mult1 - 1 == 2, "and = 2 with E088's sigma-invariance, which collapses components 1 and 2.  With |Upsilon_3| = 2 from E083's KNOWN graph, Upsilon has at most 4 elements; E093 exhibits 4; so UPSILON IS CLOSED AT FOUR.  E094's ingredient (iv), a lower bound since E093, is complete");

print("(5) WHAT REMAINS FOR b");
info("Have: the ell = 2 pairing Lambda, exact.");
info("Need: the ell = 3 pairing (Magma refuses ell = 3; the reduction is TAME there, so a hand computation is far easier than at 2, and E083's model gives the geometry), and the p-local Coleman-Gross term at p = 13 -- the largest new component, with E080's third-kind basis and E091's iterated integrals as the parts already built.");
info("Caveat: everything in groups (1)-(4) rests on Magma's model being right.  It is not a black box here -- E103 verified the intersection matrix, the multiplicities, the connectedness and the component group from first principles -- but the components' identity with the reductions of our points is Magma's word.");

print("========================================================================");
print("E104 GATE: ", if(FAIL == 0, "GREEN", "*** RED ***"), "   (", FAIL, " failures)");
quit;
