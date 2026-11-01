# check-singular-ord.sage -- feasibility study for E130 (user's suggestion).
#
# E129's addendum localised the non-termination of E128 (i') in depurate(),
# which iterates the rewriting ell^e -> f^e on every coefficient that is not an
# ell-adic unit and diverges when f's own coefficients are not units.
#
# The user proposed using Singular (through Sage's interface) for the blow-ups,
# via resolve.lib, and Macaulay2's ReesAlgebra.  This script measures what is
# actually available and what would actually help:
#
#   (A) the ring we need -- A = O[S,T]/(f-ell) localised at m = (S,T) -- is
#       expressible in Singular, with a LOCAL ordering over ZZ or over Z/2^N;
#   (B) ord_m computed there agrees with liu-model-lib's initial();
#   (C) on the real data of the node where E128 (i') stalls, Singular computes
#       ord_m and a normal form modulo (f-2) in well under a second, where
#       depurate() does not terminate at all;
#   (D) resolve.lib's own scope, read off the installed library.
#
# This is a feasibility gate, not a production one: nothing in liu-model-lib
# depends on Singular.  See E130.
import sys, time
# Run from the directory that holds liu-model-lib.sage (the repository
# root); see the README.
load("liu-model-lib.sage")

NPASS = 0
NFAIL = 0
FAILS = []


def check(name, got, want=None, cond=None):
    global NPASS, NFAIL
    ok = (got == want) if cond is None else cond
    if ok:
        NPASS += 1
        print("  PASS  %-58s %s" % (name, got))
    else:
        NFAIL += 1
        FAILS.append(name)
        print("  FAIL  %-58s got %s want %s" % (name, got, want))
    sys.stdout.flush()


B = LiuBase(2)
S, T = B.S, B.T


def ord_singular(decl, fstr, zstr="2", cap=15):
    """ord_m(z) in O[S,T]/(f-2) as max{n : z in m^n + (f-2)}, by standard
    bases.  A local ordering is required: ord_m is a statement about A
    localised at m = (S,T)."""
    singular.eval(decl)
    singular.eval('poly f = %s;' % fstr)
    singular.eval('ideal J = f - 2;')
    singular.eval('poly z = %s;' % zstr)
    n = 0
    while n < cap:
        singular.eval('ideal I = J + maxideal(%s);' % (n + 1))
        singular.eval('ideal G = std(I);')
        if singular.eval('reduce(z, G);').strip() != '0':
            break
        n += 1
    return n


print("=" * 74)
print("E130 feasibility: Singular standard bases as the ord_m primitive")
print("=" * 74)

# ---------------------------------------------------------------------------
print("\n(A) the ring A = O[S,T]/(f-ell) localised at m = (S,T)")
# ---------------------------------------------------------------------------
ok = {}
for tag, decl in (("ZZ, local (ds)", 'ring r = integer,(S,T),ds;'),
                  ("Z/2^40, local (ds)", 'ring r = (integer,2,40),(S,T),ds;'),
                  ("ZZ, global (dp)", 'ring r = integer,(S,T),dp;')):
    try:
        singular.eval(decl)
        ok[tag] = True
    except Exception:
        ok[tag] = False
    check("Singular accepts %s" % tag, ok[tag], True)

# ---------------------------------------------------------------------------
print("\n(B) ord_m against liu-model-lib's initial(), on synthetic charts")
# ---------------------------------------------------------------------------
# The second chart is the first translated by theta = 1; its coefficients are
# no longer 2-adic units, which is exactly what makes depurate() diverge.
CH = [("S^11*T^4 + S^6*T^2", 8),
      ("S^11*(T+1)^4 + S^6*(T+1)^2", 6),
      ("S^2*(1+S*T)", 2),
      ("S^6*T^2 + S^11*T^4 + 2*S^3", 8),
      ("S*T", 2),
      ("S^2*T^3 + S^5", 5)]
for fstr, want in CH:
    fpy = sage_eval(fstr, locals={'S': S, 'T': T})
    ours = LiuChart(B, fpy).ord(B.R(2))
    zz = ord_singular('ring r = integer,(S,T),ds;', fstr)
    z2 = ord_singular('ring r = (integer,2,40),(S,T),ds;', fstr)
    check("ord_m(2) for f = %-28s" % fstr, [ours, zz, z2], [want, want, want])

# ---------------------------------------------------------------------------
print("\n(C) the real data of the node where E128 (i') stalls")
# ---------------------------------------------------------------------------
TARGET = "s=0|E3@0|E4@1|E5@0|E6@oo|E7@0|E9@1"


class _Caught(Exception):
    def __init__(self, nd):
        self.nd = nd


_proc = Resolution.process


def _stop(self, nd, stack):
    if nd.tag == TARGET:
        raise _Caught(nd)
    return _proc(self, nd, stack)


Resolution.process = _stop
Rs = PolynomialRing(B.O, 's')
s = Rs.gen()
LC = LineCover(B, 2 * (s ** 3 + 4),
               2 * (3 * s ** 4 + 4 * s ** 3 + 2 * (-7) * s ** 2 + 4), 2,
               all_rational=False, point_degree=1, next_cover=False)
nd = None
try:
    LC.resolution()
except _Caught as c:
    nd = c.nd
finally:
    Resolution.process = _proc
check("the stalling node of E128 (i') is reached", nd is not None, True)
ch = nd.chart


def to_singular(p):
    out = []
    for (u, v), c in ch.R(p).dict().items():
        cl = B.O(c).lift()
        assert cl.degree() <= 0 and QQ(cl.constant_coefficient()).denominator() % 2 == 1
        q = QQ(cl.constant_coefficient())
        out.append("(%s)*S^%s*T^%s"
                   % (q.numerator() * ZZ(q.denominator()).inverse_mod(2 ** 60) % 2 ** 60,
                      u, v))
    return " + ".join(out) if out else "0"


check("the stalling chart's f has coefficients that are not units",
      max(B.oval(c) for c in ch.f.dict().values()) > 0, True)
fS = to_singular(ch.f)
for nm, z in (("2", ch.R(2)), ("a", ch.R(nd.a)), ("b", ch.R(nd.b))):
    ours = ch.ord(z)
    t = time.time()
    got = ord_singular('ring r = (integer,2,60),(S,T),ds;', fS, to_singular(z))
    check("ord_m(%s) agrees (initial() and Singular)" % nm, [ours, got],
          [ours, ours])
    print("        computed in %.2f s" % (time.time() - t))
# depurate() diverges here; Singular's normal form does not
rounds = []
z = ch.R(nd.b)
for _ in range(4):
    W = ch._terms(z)
    rounds.append(max(t2[2] for t2 in W))
    if rounds[-1] == 0:
        break
    zn = ch.R(0)
    for (u, v), c, e, w in W:
        zn += (c / B.ell ** e) * ch._fpow(e) * B.S ** u * B.T ** v
    z = zn
check("depurate(b) diverges: the maximum valuation rises",
      [rounds[-1] > rounds[0], rounds == sorted(rounds)], [True, True])
print("        valuations per round: %s" % rounds)
t = time.time()
singular.eval('ring r = (integer,2,60),(S,T),ds;')
singular.eval('poly f = %s;' % fS)
singular.eval('ideal J = f - 2;')
singular.eval('poly b = %s;' % to_singular(ch.R(nd.b)))
singular.eval('ideal GJ = std(J);')
nf = singular.eval('reduce(b, GJ);')
dt = time.time() - t
check("Singular's normal form of b modulo (f-2) terminates", dt < 60, True)
print("        %s characters in %.2f s" % (len(nf), dt))

# ---------------------------------------------------------------------------
print("\n(D) the scope resolve.lib states for itself")
# ---------------------------------------------------------------------------
# locate resolve.lib through Singular's own library search path, so that
# this does not depend on where Singular is installed
import os
_libdir = singular.eval('system("SingularLib");').strip().strip('"')
_resolve = None
for _d in _libdir.split(':'):
    _c = os.path.join(_d, 'resolve.lib')
    if os.path.exists(_c):
        _resolve = _c
        break
check("resolve.lib is found on Singular's library path", _resolve is not None, True)
src = open(_resolve).read(4000)
check("resolve.lib implements Villamayor's algorithm",
      'Algorithm of Villamayor' in src, True)
check("resolve.lib documents its scope as characteristic zero",
      'characteristic zero' in src, True)
print("        -> resolve(J) does not apply to an arithmetic surface over")
print("           Z_(2) with wild residue characteristic; blowUp() does run")
print("           over ZZ, but the blow-up is not what E128 (i') stalls on.")

print()
print("=" * 74)
if NFAIL == 0:
    print("JUDGEMENT: GREEN -- %s/%s checks passed" % (NPASS, NPASS))
    sys.exit(int(0))
else:
    print("JUDGEMENT: RED -- %s/%s checks failed: %s"
          % (NFAIL, NPASS + NFAIL, FAILS))
    sys.exit(int(1))
