\\ check-tuitman-diamond.gp --- E048 Phase 1, risk 2: does the C_4 model
\\ satisfy Tuitman's hypotheses (the plan's "(diamond)")?
\\
\\ THE HYPOTHESES, from the source (Tuitman I, arXiv:1402.6758v2, Section 2;
\\ Math. Comp. 85 (2016), 961-981).  Read, not recalled.  With
\\ x : X -> P^1 finite separable of degree d_x, y generating the function field,
\\ Q in F_q[x,y] irreducible and monic in y of degree d_x, d_y = deg_x Q, and
\\ script-Q in Z_q[x,y] a lift with the same support, still monic in y:
\\
\\   Definition 2.2.  Delta(x) = disc_y(script-Q),  r = Delta/gcd(Delta, dDelta/dx).
\\
\\   Assumption 1.  (1) There exists a smooth proper curve script-X over Z_q and a
\\     smooth relative divisor D_X on it with U = script-X \ D_X.  (2) There
\\     exists a smooth relative divisor D_{P^1} on P^1_{Z_q} with V = P^1 \ D_{P^1}.
\\
\\   Remark 2.3 makes this checkable: a relative divisor over Z_q is smooth iff it
\\     reduces mod p to a REDUCED divisor.  "Hence by Assumption 1, all branch
\\     points of the map x restricted to X, and all points on X lying over these
\\     branch points, are distinct modulo p."
\\
\\   Assumption 2.  The zero locus of script-Q(x,y) in A^2_{Q_q} is smooth.
\\
\\   Assumption 3.  A matrix W^inf in GL_{d_x}(Z_q[x,x^{-1}]) is known such that
\\     the b_j^inf form an integral basis for Q_q(x,y) over Q_q[x^{-1}].
\\
\\ Assumption 3 is a computation (Phase 1's `auxpolys`), not a restriction on the
\\ model, so it is not tested here.  What must be tested before any code is
\\ written is Assumption 2 and, for each p, Assumption 1 via Remark 2.3.  Note
\\ that U also excludes the fibre over x = infinity, so the points over infinity
\\ must be distinct mod p as well.
\\
\\ THE MODEL (E037/E040).  C_4 : w^4 - 6(t-1)^2 w^2 + 27t(t^3-4) = 0, already
\\ monic in w of degree 4 = deg of the map t, with deg_t = 4.  So the natural
\\ Tuitman input is x = t (base), y = w (fibre).
\\
\\ *** VARIABLE NAMES.  PARI enforces variable priority: to factor / gcd over a
\\ residue ring k[base]/(s), the BASE variable must have the LOWER priority.
\\ Since 'x has higher priority than 'y in GP, this script uses
\\        x = the FIBRE coordinate (Tuitman's y, our w),
\\        y = the BASE  coordinate (Tuitman's x, our t).
\\ Every printed formula says which is which. ***

default(parisize, "512M");

\\ Q with x = fibre (w), y = base (t)
QQ() = {
  return(x^4 - 6*(y-1)^2*x^2 + 27*y^4 - 108*y);
};

\\ Delta and r as polynomials in the BASE variable y
delta() = {
  return(polresultant(QQ(), deriv(QQ(), x), x));
};

rad(D) = {
  return(D / gcd(D, deriv(D, y)));
};

\\ Assumption 2: no point with Q = Q_x = Q_y = 0.  Eliminating the fibre
\\ variable, a singular point forces a common root of the two resultants; if
\\ their gcd is a nonzero constant there is none, over Q AND over F_p for every
\\ p not dividing that constant.
assumption2() = {
  my(Q = QQ(), R1, R2, g);
  R1 = polresultant(Q, deriv(Q, x), x);
  R2 = polresultant(Q, deriv(Q, y), x);
  g = gcd(R1, R2);
  \\ NB: gcd returns a t_POL even when it is constant, and for a t_POL the
  \\ operator % is POLYNOMIAL remainder -- "g % p" is then 0 for every p, which
  \\ silently reported that every prime fails.  Return an integer.
  if(poldegree(g) > 0, return(g), return(simplify(g)));
};

\\ number of distinct points of the curve above the branch locus, in
\\ characteristic 0: for each irreducible factor s of r, work over
\\ K = Q[y]/(s) and count distinct fibre roots as deg Q - deg gcd(Q, dQ/dx).
countchar0(r) = {
  my(Q = QQ(), fa = factor(r), tot = 0, s, Qs, g, d);
  for(i = 1, matsize(fa)[1],
    s = fa[i,1];
    if(poldegree(s) == 0, next);
    Qs = subst(Q, y, Mod(y, s));
    g = gcd(Qs, deriv(Qs, x));
    d = poldegree(Qs, x) - poldegree(g, x);
    tot += poldegree(s) * d);
  return(tot);
};

\\ the same count mod p, over F_p[y]/(sbar) for each irreducible factor sbar
countmodp(r, p) = {
  my(Q = QQ(), fa, tot = 0, s, a, Qa, g, d);
  fa = factor(Mod(1, p) * r);
  for(i = 1, matsize(fa)[1],
    s = fa[i,1];
    if(poldegree(s) == 0, next);
    a = ffgen(s, 'a);
    Qa = subst(Q, y, a);
    g = gcd(Qa, deriv(Qa, x));
    d = poldegree(Qa, x) - poldegree(g, x);
    tot += poldegree(s) * d);
  return(tot);
};

\\ CERTIFICATES.  The prime-by-prime table below is only [E]; these three exact
\\ identities turn it into a statement about every p >= 5.  The fibre polynomial
\\ is even in the fibre variable, x^4 + B x^2 + C with
\\        B = -6(y-1)^2,   C = 27y^4 - 108y = 27y(y^3-4),
\\ and the branch locus is r = 2*y*(y^3-4)*s(y), s = 2y^4+4y^3-6y^2-8y-1.
\\   (i)   over y = 0:        C = 0 and B = -6, so Q = x^2(x^2 - 6);
\\   (ii)  over y^3 = 4:      C = 0 again, so Q = x^2(x^2 - 6(y-1)^2);
\\   (iii) over s = 0:        B^2 - 4C = -36 s(y) EXACTLY, so B^2 = 4C there and
\\         Q = (x^2 + B/2)^2.
\\ Hence the fibre has 3, 3, 2 distinct points respectively, provided only that
\\ B does not vanish, i.e. that 6 and (y-1) are invertible: y = 1 is a root of
\\ y^3-4 only if 3 | p, and s(1) = -9. So for every p >= 5 the counts are the
\\ characteristic-0 ones, and the total is 3 + 3*3 + 2*4 = 20.
certificates() = {
  my(Q = QQ(), B, C, s, i1, i2, i3);
  B = polcoef(Q, 2, x); C = polcoef(Q, 0, x);
  s = 2*y^4 + 4*y^3 - 6*y^2 - 8*y - 1;
  i1 = subst(Q, y, 0) - x^2*(x^2 - 6);
  i2 = (Q - x^2*(x^2 - 6*(y-1)^2)) % (y^3 - 4);
  i3 = (B^2 - 4*C) + 36*s;
  return([B, C, s, i1, i2, i3, subst(s, y, 1), polresultant(y^3-4, y-1)]);
};

\\ the fibre over x = infinity.  The degree-4 part of Q is the leading form; the
\\ points at infinity of the plane model are its roots, and they stay distinct
\\ mod p exactly when p does not divide its discriminant.
atinfinity() = {
  my(Q = QQ(), L = 0, mons);
  \\ leading form: keep the monomials of total degree 4
  for(i = 0, 4, for(j = 0, 4,
    if(i + j == 4, L += polcoef(polcoef(Q, i, x), j, y) * x^i * y^j)));
  return(L);
};

\\ Is the projective plane closure smooth at infinity?  If so the four points of
\\ the leading form really are four points of X, and "distinct mod p" is a
\\ statement about X rather than about a plane model that might be singular
\\ there.  With z the homogenising variable, a singular point at z=0 needs the
\\ leading form and all three partials to vanish.
infsmooth() = {
  my(Q = QQ(), H, dx, dy, dz, L);
  H = x^4 - 6*(y - z)^2*x^2 + 27*y^4 - 108*y*z^3;
  dx = subst(deriv(H, x), z, 0);
  dy = subst(deriv(H, y), z, 0);
  dz = subst(deriv(H, z), z, 0);
  L = subst(H, z, 0);
  \\ dz = 12 y x^2 forces y = 0 or x = 0, and L = x^4 - 6y^2x^2 + 27y^4 then
  \\ forces the other to vanish too -- no point of P^2.  Return the three so the
  \\ reader can check that reasoning rather than take it.
  return([L, dx, dy, dz]);
};

run() = {
  my(Q, D, r, g2, c0, cp, L, Linf, dL, cert, inf, res = List());
  print("=== check-tuitman-diamond.gp --- Tuitman's Assumptions for the C_4 model ===");
  print("    x = FIBRE coordinate (our w), y = BASE coordinate (our t)");
  print("");
  Q = QQ();
  printf("  Q = %s\n", Q);
  printf("  monic in the fibre variable, d_x = %d, d_y = %d, irreducible: %d\n",
         poldegree(Q, x), poldegree(Q, y), polisirreducible(Q));
  print("");

  print("=== 1. Assumption 2 (affine smoothness) ===");
  g2 = assumption2();
  printf("  gcd(Res(Q,Q_fib), Res(Q,Q_base)) = %s\n", g2);
  if(poldegree(g2) > 0,
    print("  *** NOT a constant: the elimination is inconclusive, examine directly ***"),
    printf("  a nonzero constant = %s\n", factor(g2));
    print("  ==> no point with Q = Q_x = Q_y = 0 over Qbar: ASSUMPTION 2 HOLDS,"));
  print("      unconditionally, and the affine curve stays smooth mod every p");
  print("      not dividing that constant.");
  print("");

  print("=== 2. Definition 2.2: Delta and r ===");
  D = delta();
  r = rad(D);
  printf("  Delta = disc_fib(Q), degree %d\n", poldegree(D));
  printf("  Delta factors as %s\n", factor(D));
  printf("  r = %s\n", r);
  printf("  r factors as %s\n", factor(r));
  printf("  deg r = %d, lc(r) = %s\n", poldegree(r), pollead(r));
  printf("  disc(r) = %s = %s\n", poldisc(r), factor(poldisc(r)));
  print("  ==> the branch points are distinct mod p for every p dividing none of");
  print("      lc(r) and disc(r).");
  print("");

  print("=== 3. Remark 2.3, part 2: the points over the branch locus ===");
  c0 = countchar0(r);
  printf("  distinct points above the branch locus in characteristic 0: %d\n", c0);
  print("");

  print("=== 3'. the same count, certified for EVERY p >= 5 ===");
  cert = certificates();
  printf("  fibre polynomial: x^4 + B x^2 + C with B = %s, C = %s\n", cert[1], cert[2]);
  printf("  s(y) = %s\n", cert[3]);
  printf("  (i)   Q|_{y=0} - x^2(x^2-6) = %s\n", cert[4]);
  printf("  (ii)  Q - x^2(x^2-6(y-1)^2) mod (y^3-4) = %s\n", cert[5]);
  printf("  (iii) (B^2 - 4C) + 36 s(y) = %s\n", cert[6]);
  printf("  s(1) = %s, Res(y^3-4, y-1) = %s  (so y=1 meets the branch locus only at p=3)\n",
         cert[7], cert[8]);
  if(cert[4] == 0 && cert[5] == 0 && cert[6] == 0,
    print("  ==> all three identities hold exactly, so for every p >= 5 the fibres");
    print("      over the branch locus have 3, 3, 2 distinct points and the total is");
    print("      3 + 3*3 + 2*4 = 20, the characteristic-0 count.  [T(CAS)]"),
    print("  *** an identity FAILED: the argument below is void ***"));
  print("");

  print("=== 4. the fibre over x = infinity ===");
  L = atinfinity();
  Linf = subst(L, y, 1);
  dL = poldisc(Linf);
  printf("  leading form = %s\n", L);
  printf("  dehomogenised = %s, disc = %s = %s\n", Linf, dL, factor(dL));
  printf("  squarefree: %d, so %d distinct points at infinity in char 0\n",
         poldegree(gcd(Linf, deriv(Linf, x))) == 0, poldegree(Linf));
  inf = infsmooth();
  printf("  projective closure at z=0: L = %s\n", inf[1]);
  printf("    dH/dx|_{z=0} = %s\n", inf[2]);
  printf("    dH/dy|_{z=0} = %s\n", inf[3]);
  printf("    dH/dz|_{z=0} = %s\n", inf[4]);
  print("    dH/dz = 12*y*x^2 forces y=0 or x=0, and then L forces the other to");
  print("    vanish as well, which is no point of P^2 ==> the closure is SMOOTH at");
  print("    infinity, so these four are genuine points of X, not of a bad model.");
  print("");

  print("=== 5. the verdict, prime by prime ===");
  print("  A2 = affine smoothness survives; br = branch points distinct;");
  print("  fib = points over the branch locus (char 0 count reproduced);");
  print("  inf = points over infinity distinct.  All four are needed.");
  print("");
  print("       p    A2    br   fib(count)    inf    (diamond)");
  forprime(p = 5, 60,
    my(a2, br, fib, inf, ok);
    a2 = (g2 % p != 0);
    br = (pollead(r) % p != 0) && (poldisc(r) % p != 0);
    cp = if(br, countmodp(r, p), -1);
    fib = (cp == c0);
    inf = (dL % p != 0);
    ok = a2 && br && fib && inf;
    printf("   %5d   %3s   %3s   %3s (%2d)     %3s    %s\n", p,
           if(a2, "ok", "NO"), if(br, "ok", "NO"), if(fib, "ok", "NO"), cp,
           if(inf, "ok", "NO"), if(ok, "HOLDS", "*** FAILS ***"));
    if(ok, listput(res, p)));
  print("");
  printf("  (diamond) holds for: %s\n", Vec(res));
  print("");
  print("=== 6. the primes Phase 0 Gate 2 actually used ===");
  print("  E048 Gate 2 ran Sage's genus-2 Coleman integration at p = 11, 23, 29,");
  print("  and its census had 21 usable primes below 200.  Those are the primes");
  print("  Phase 3 gate (v) needs, so they are the ones that matter here.");
  foreach([11, 23, 29], p,
    my(a2, br, fib, inf);
    a2 = (g2 % p != 0);
    br = (pollead(r) % p != 0) && (poldisc(r) % p != 0);
    cp = countmodp(r, p);
    fib = (cp == c0);
    inf = (dL % p != 0);
    printf("   p = %2d: A2 %s, br %s, fib %d vs %d, inf %s ==> %s\n", p,
           if(a2, "ok", "NO"), if(br, "ok", "NO"), cp, c0, if(inf, "ok", "NO"),
           if(a2 && br && fib && inf, "HOLDS", "FAILS")));
  print("");
  print("=== END ===");
};

run();
