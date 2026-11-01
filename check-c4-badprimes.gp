\\ check-c4-badprimes.gp --- E037(d) addendum: the canonical quartic of C_4 is
\\ smooth over every field of characteristic other than 2 and 3.
\\
\\ E037(d) read good reduction off Q mod p for p = 5,...,31, which settles those
\\ primes and no others.  paper 2, Section 9, needs the statement for ALL p,
\\ because the count |Upsilon| = 4 there is one factor 2 per prime of bad
\\ reduction.  This script backs the closed proof recorded in E037's addendum.
\\
\\ In the coordinates of E037(e), T = X-Y-Z and W = Y+Z, the canonical model is
\\       Q = 27 T (T^3 - 4 Z^3) + W^4 - 6 (T-Z)^2 W^2 .
\\ Write u = T-Z and s = W^2 - 3u^2.  The three partials factor:
\\       Q_T = 12 u (9(T^2+TZ+Z^2) - W^2),
\\       Q_W = 4 W s,
\\       Q_Z = -324 T Z^2 + 12 W^2 u ,
\\ and modulo s they simplify further,
\\       Q_T = 36 u (2T+Z)(T+2Z) - 12 u s,
\\       Q_Z = 36 (u^3 - 9 T Z^2) + 12 u s .
\\ Over a field of characteristic p, p not 2 or 3, a singular point is a common
\\ zero of the three partials (Euler, since p does not divide deg Q = 4), and
\\ Q_W = 4Ws = 0 splits into two cases:
\\
\\   W = 0.  Then Q_T = 108(T^3 - Z^3) and Q_Z = -324 T Z^2.  From Q_Z either
\\           T = 0, whence Z^3 = 0 and Z = 0; or Z = 0, whence T^3 = 0.
\\   s = 0, i.e. W^2 = 3u^2.  Then Q_T = 36 u (2T+Z)(T+2Z) and
\\           Q_Z = 36 (u^3 - 9 T Z^2).  The three factors of Q_T:
\\             u = 0 : T = Z, so W^2 = 0 and Q_Z = -324 Z^3, giving Z = 0;
\\             T = -2Z : u^3 - 9TZ^2 = -9 Z^3, giving Z = 0, then T = 0, W = 0;
\\             Z = -2T : u^3 - 9TZ^2 = -9 T^3, giving T = 0, then Z = 0, W = 0.
\\
\\ Every branch ends at (T,W,Z) = (0,0,0), which is not a point of P^2.  Hence Q
\\ is smooth in every characteristic other than 2 and 3, and C_4 has good
\\ reduction outside {2,3}.  [T] --- the argument is finite and written out; the
\\ only inputs are the polynomial identities checked in group 1 below, each of
\\ which is a one-line hand expansion.
\\
\\ Groups 2 and 3 are independent controls and are not part of the deduction:
\\ group 2 enumerates P^2(F_p) and looks for a singular point directly, group 3
\\ confirms that 2 and 3 really are bad.
\\
\\ Run with:  gp -q check-c4-badprimes.gp < /dev/null      Runtime: 0.3 s.

default(parisize, 200000000);

\\ --- E119 gate harness (see E119) ---
FAILN = 0;
check(c, msg) =
{
  if(!c, printf("   [FAIL] %s\n", msg); FAILN++);
  return(c);
}
gate(tag) =
{
  printf("\n%s GATE: %s   (%d failures)\n", tag, if(FAILN, "*** RED ***", "GREEN"), FAILN);
  return(FAILN);
}

quartic() =
{
  return(27*T*(T^3 - 4*Z^3) + W^4 - 6*(T-Z)^2*W^2);
}

\\ ---------------------------------------------------------------- group 1
\\ The polynomial identities the proof rests on.  All are exact identities in
\\ Z[T,W,Z]; each is verified as "difference is the zero polynomial".
identities() =
{
  my(Q, QT, QW, QZ, u, s);
  Q = quartic();
  QT = deriv(Q, T);
  QW = deriv(Q, W);
  QZ = deriv(Q, Z);
  u = T - Z;
  s = W^2 - 3*u^2;
  print("### 1. the identities behind the proof ###");
  print("  Q  = ", Q);
  check(Q == 27*T^4 - 108*T*Z^3 - 6*W^2*T^2 + 12*W^2*Z*T - 6*W^2*Z^2 + W^4,
        "E037(d'): Q expands as recorded in E037(e)");
  check(QT - 12*u*(9*(T^2 + T*Z + Z^2) - W^2) == 0,
        "E037(d'): Q_T = 12 u (9(T^2+TZ+Z^2) - W^2)");
  check(QW - 4*W*s == 0,
        "E037(d'): Q_W = 4 W (W^2 - 3u^2)");
  check(QZ - (-324*T*Z^2 + 12*W^2*u) == 0,
        "E037(d'): Q_Z = -324 T Z^2 + 12 W^2 u");
  check(QT - 36*u*(2*T + Z)*(T + 2*Z) + 12*u*s == 0,
        "E037(d'): Q_T = 36 u (2T+Z)(T+2Z) - 12 u s");
  check(QZ - 36*(u^3 - 9*T*Z^2) - 12*u*s == 0,
        "E037(d'): Q_Z = 36 (u^3 - 9 T Z^2) + 12 u s");
  print("");
  print("  the branch W = 0:");
  check(subst(QT, W, 0) - 108*(T^3 - Z^3) == 0,
        "E037(d'): Q_T = 108 (T^3 - Z^3) when W = 0");
  check(subst(QZ, W, 0) + 324*T*Z^2 == 0,
        "E037(d'): Q_Z = -324 T Z^2 when W = 0");
  print("  the branch s = 0, the three factors of Q_T:");
  check(subst(u^3 - 9*T*Z^2, T, Z) + 9*Z^3 == 0,
        "E037(d'): u^3 - 9TZ^2 = -9 Z^3 on u = 0");
  check(subst(u^3 - 9*T*Z^2, T, -2*Z) + 9*Z^3 == 0,
        "E037(d'): u^3 - 9TZ^2 = -9 Z^3 on T = -2Z");
  check(subst(u^3 - 9*T*Z^2, Z, -2*T) + 9*T^3 == 0,
        "E037(d'): u^3 - 9TZ^2 = -9 T^3 on Z = -2T");
  print("");
  print("  every branch forces (T,W,Z) = (0,0,0), which is not a point of P^2,");
  print("  provided 2 and 3 are invertible -- the only divisions used are by");
  print("  the coefficients 4, 9, 12, 36, 108 and 324, all of the form 2^a 3^b.");
  return(1);
}

\\ ---------------------------------------------------------------- group 2
\\ Independent control: enumerate P^2(F_p) and look for a singular point.
\\ This repeats E037(d) for p = 5,...,97 by a different route (E037(d) used a
\\ Sage smoothness test on the reduced curve).
singular_count(p) =
{
  my(Q, QT, QW, QZ, cnt, t, w, z);
  Q = quartic();
  QT = deriv(Q, T);
  QW = deriv(Q, W);
  QZ = deriv(Q, Z);
  cnt = 0;
  \\ the three standard charts of P^2, without double counting:
  \\ [t:w:1], then [t:1:0], then [1:0:0].
  for(a = 0, p-1, for(b = 0, p-1,
    t = Mod(a, p); w = Mod(b, p); z = Mod(1, p);
    if(substvec(QT, [T,W,Z], [t,w,z]) == 0
       && substvec(QW, [T,W,Z], [t,w,z]) == 0
       && substvec(QZ, [T,W,Z], [t,w,z]) == 0, cnt++)));
  for(a = 0, p-1,
    t = Mod(a, p); w = Mod(1, p); z = Mod(0, p);
    if(substvec(QT, [T,W,Z], [t,w,z]) == 0
       && substvec(QW, [T,W,Z], [t,w,z]) == 0
       && substvec(QZ, [T,W,Z], [t,w,z]) == 0, cnt++));
  t = Mod(1, p); w = Mod(0, p); z = Mod(0, p);
  if(substvec(QT, [T,W,Z], [t,w,z]) == 0
     && substvec(QW, [T,W,Z], [t,w,z]) == 0
     && substvec(QZ, [T,W,Z], [t,w,z]) == 0, cnt++);
  return(cnt);
}

sweep() =
{
  my(c);
  print("");
  print("### 2. control: singular points of Q over F_p, by enumeration ###");
  printf("  %5s %10s\n", "p", "#sing");
  forprime(p = 5, 97,
    c = singular_count(p);
    printf("  %5d %10d\n", p, c);
    check(c == 0, Str("E037(d'): Q mod p is smooth at p = ", p)));
  return(1);
}

\\ ---------------------------------------------------------------- group 3
\\ The converse half: 2 and 3 ARE bad, so "outside {2,3}" is sharp.
badones() =
{
  my(c);
  print("");
  print("### 3. control: 2 and 3 are genuinely bad ###");
  foreach([2, 3], p,
    c = singular_count(p);
    printf("  p = %d : %d singular point(s) in P^2(F_p)\n", p, c);
    check(c > 0, Str("E037(d'): Q mod p is singular at p = ", p)));
  print("");
  print("  (over F_2 and F_3 the argument above breaks at its first step:");
  print("   Q_W = 4Ws vanishes identically mod 2, and mod 3 the factor 9 in");
  print("   Q_T and the 9 in u^3 - 9TZ^2 both disappear.)");
  return(1);
}

run() =
{
  identities();
  sweep();
  badones();
  gate("E037");
  return(1);
}
run();
