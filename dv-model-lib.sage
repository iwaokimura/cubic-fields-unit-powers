## dv-model-lib.sage --- shared library for check-c4-dv3.sage and
## check-dv-paper-examples.sage.  NOT a gated script: it defines and checks
## nothing on its own, and the verification runner should skip it (hence the
## name, which does not start with "check-").
##
## An implementation of
##     T. Dokchitser, Models of curves over discrete valuation rings,
##     Duke Math. J. 170 (2021), no. 11, 2519-2574,
## from arXiv:1807.00025v2 (the published version was not consulted; see
## E125 8.1).  All numbering in the comments is v2's.
## The statements implemented are listed in E125.
import sys
## --- E119 gate harness ---
import sys as _sys
FAIL = []
NCHECK = [0]
def check(c, msg):
    NCHECK[0] += 1
    if not c:
        print("   [FAIL] %s" % msg)
        FAIL.append(msg)
    _sys.stdout.flush()
    return c
def gate(tag):
    print("")
    print("%s GATE: %s   (%d checks, %d failures)"
          % (tag, "*** RED ***" if FAIL else "GREEN", NCHECK[0], len(FAIL)))
    for m in FAIL:
        print("   FAILED: %s" % m)
    _sys.stdout.flush()
## --- end gate harness ---

R = PolynomialRing(QQ, ['x', 'y']); x, y = R.gens()
F0 = y^4 - 6*(x-1)^2*y^2 + 27*x*(x^3-4)          # paper2 (14)
PTS = [(1,3), (1,-3), (-1,3), (-1,-3), (-2,6), (-2,-6),
       (QQ(-1)/11, QQ(15)/11), (QQ(-1)/11, QQ(-15)/11), (0,0)]   # paper2 (20)
E105 = {(1,3): 'A', (-2,-6): 'A', (QQ(-1)/11, QQ(15)/11): 'A',
        (1,-3): 'B', (-2,6): 'B', (QQ(-1)/11, QQ(-15)/11): 'B',
        (-1,3): 'C', (-1,-3): 'C', (0,0): 'C'}
LL = 3

def clear_den(h):
    return h * lcm([c.denominator() for c in h.coefficients()])

def smooth_torus(red, l, nvars):
    if red is None: return False
    g = red['poly']
    if g.is_constant(): return False
    if nvars == 1:
        u = g.parent().gen(0)
        while g % u == 0: g //= u
        return g.degree() < 1 or gcd(g, g.derivative()).degree() == 0
    A = PolynomialRing(GF(l), ['U', 'V', 'W']); U, V, W = A.gens()
    gg = A(str(g).replace('u', 'U').replace('v', 'V'))
    return A.ideal([gg, gg.derivative(U), gg.derivative(V), U*V*W-1]).dimension() == -1

class Model:
    """Delta_v and the r.n.c. model of Thm 3.13, for f over Z_(l)."""
    def __init__(self, f, l):
        self.f = f; self.l = l
        self.mons = {(m.exponents()[0][0], m.exponents()[0][1]): c
                     for c, m in zip(f.coefficients(), f.monomials())}
        self.val = {P: ZZ(c).valuation(l) for P, c in self.mons.items()}
        self.P3 = Polyhedron(vertices=[(P[0], P[1], self.val[P]) for P in self.mons],
                             rays=[(0,0,1)], base_ring=QQ)
        self.Delta = Polyhedron(vertices=[(P[0], P[1]) for P in self.mons])
        self._faces(); self._edges()

    def _restrict(self, S, vf, nvars):            # Def 3.4 + Def 3.5
        S = sorted(S); P0 = S[0]
        Mt = matrix(ZZ, [[t[0]-P0[0], t[1]-P0[1]] for t in S[1:]])
        B = Mt.row_module().basis_matrix()
        if B.nrows() != nvars: return None
        surv = []
        for t in S:
            if t not in self.mons or self.val[t] != vf(*t): continue
            e = B.solve_left(vector(QQ, [t[0]-P0[0], t[1]-P0[1]]))
            if not all(c in ZZ for c in e): return None
            surv.append((vector(ZZ, e), QQ(self.mons[t])/self.l^vf(*t)))
        if not surv: return None
        lo = vector(ZZ, [min(e[i] for e, _ in surv) for i in range(nvars)])
        Rk = PolynomialRing(GF(self.l), ['u', 'v'][:nvars])
        g = sum(GF(self.l)(c)*prod(Rk.gen(i)^ZZ((e-lo)[i]) for i in range(nvars))
                for e, c in surv)
        return dict(poly=g, P0=P0, basis=B)

    def _faces(self):
        self.faces = []
        for F in self.P3.faces(2):
            H = F.ambient_Hrepresentation()
            if len(H) != 1: continue
            a, b, c = H[0].A(); d = -H[0].b()
            if c <= 0: continue                            # not on the lower hull
            Fp = Polyhedron(vertices=[(v[0], v[1]) for v in F.vertices()])
            if Fp.dim() != 2: continue
            vF = lambda i, j, a=a, b=b, c=c, d=d: (d - a*i - b*j)/c
            ip = [tuple(p) for p in Fp.integral_points()]
            dF = lcm([QQ(vF(*p)).denominator() for p in ip])
            Bl = matrix(ZZ, [[p[0]-ip[0][0], p[1]-ip[0][1]]
                             for p in ip if vF(*p) in ZZ][1:]).row_module().basis_matrix()
            interior = [p for p in ip if Fp.interior_contains(vector(QQ, p))]
            self.faces.append(dict(
                poly=Fp, vF=vF, delta=dF, ipts=ip, latidx=abs(Bl.det()) if Bl.nrows()==2 else 0,
                verts=frozenset((v[0], v[1]) for v in F.vertices()),
                interior=[p for p in interior if vF(*p) in ZZ],
                genus=len([p for p in interior if vF(*p) in ZZ]),
                red=self._restrict([p for p in ip if vF(*p) in ZZ], vF, 2)))

    def _edges(self):
        self.edges = []
        for E in self.P3.faces(1):
            if len(E.rays()) or len(E.lines()) or len(E.vertices()) != 2: continue
            p, q = [(v[0], v[1], v[2]) for v in E.vertices()]
            Ep = Polyhedron(vertices=[(p[0], p[1]), (q[0], q[1])])
            if Ep.dim() != 1: continue
            def vL(i, j, p=p, q=q):
                t = QQ(i-p[0])/(q[0]-p[0]) if q[0] != p[0] else QQ(j-p[1])/(q[1]-p[1])
                return p[2] + t*(q[2]-p[2])
            ip = [tuple(t) for t in Ep.integral_points()]
            dL = lcm([QQ(vL(*t)).denominator() for t in ip])
            SZ = sorted([t for t in ip if vL(*t) in ZZ])
            adj = [n for n, F in enumerate(self.faces)
                   if all(F['poly'].contains(vector(QQ, t)) for t in (p[:2], q[:2]))]
            onbd = any(all(H.eval(vector(QQ, t)) == 0 for t in ip)
                       for H in self.Delta.Hrepresentation())
            self.edges.append(dict(
                p=p[:2], q=q[:2], vL=vL, delta=dL, SZ=SZ, ipts=ip, adj=adj, onbd=onbd,
                red=self._restrict(SZ, vL, 1) if len(SZ) >= 2 else None))

    def is_regular(self):                                   # Def 3.9
        for F in self.faces:
            if not smooth_torus(F['red'], self.l, 2):
                return False, ('face', sorted(F['verts']))
        for E in self.edges:
            if E['red'] is None: continue
            if smooth_torus(E['red'], self.l, 1): continue
            if (E['onbd'] and len(E['adj']) == 1
                    and self.faces[E['adj'][0]]['delta'] == E['delta']):
                continue                                    # the Def 3.9 exception
            return False, ('edge', E['p'], E['q'])
        return True, None

# ---------------- Def 3.12: slopes at a v-edge ----------------
def slope_data(M, E):
    p, q = vector(ZZ, E['p']), vector(ZZ, E['q'])
    d = q - p; d = d/gcd(d[0], d[1])
    nrm = vector(ZZ, [-d[1], d[0]])                    # primitive normal to L
    F1 = M.faces[E['adj'][0]]
    ref = sum(vector(QQ, t) for t in F1['ipts'])/len(F1['ipts'])
    if nrm.dot_product(ref - vector(QQ, p)) < 0: nrm = -nrm      # L* >= 0 on F1
    _, c0, c1 = xgcd(ZZ(nrm[0]), ZZ(nrm[1]))
    P0 = p; P1 = p + vector(ZZ, [c0, c1])              # L*(P0)=0, L*(P1)=1
    assert nrm.dot_product(P1 - P0) == 1
    inner = len(E['adj']) == 2
    s1 = E['delta']*(F1['vF'](*P1) - F1['vF'](*P0))
    s2 = (E['delta']*(M.faces[E['adj'][1]]['vF'](*P1) - M.faces[E['adj'][1]]['vF'](*P0))
          if inner else floor(s1 - 1))
    return dict(P0=P0, P1=P1, s1=s1, s2=s2, inner=inner,
                F1=E['adj'][0], F2=E['adj'][1] if inner else None)

# ---------------- Rem 3.15: the minimal unimodular sequence ----------------
def hj_chain(s1, s2):
    assert s1 > s2
    sh = -floor(s2); a, b = s1 + sh, s2 + sh
    D = max(QQ(a).denominator(), QQ(b).denominator())
    cand = set()
    for q in range(1, D+1):
        for n in range(ceil(b*q), floor(a*q)+1):
            r = QQ(n)/q
            if b <= r <= a: cand.add(r)
    seq = sorted(cand, reverse=True)
    changed = True
    while changed:                        # blow down the mediants (Rem 3.15)
        changed = False
        for i in range(1, len(seq)-1):
            A, B, C = seq[i-1], seq[i], seq[i+1]
            if (B.numerator() == A.numerator()+C.numerator()
                    and B.denominator() == A.denominator()+C.denominator()):
                seq.pop(i); changed = True; break
    for i in range(len(seq)-1):           # the determinant condition of 3.13(2)
        A, C = seq[i], seq[i+1]
        assert A.numerator()*C.denominator() - C.numerator()*A.denominator() == 1
    return [QQ(r) - sh for r in seq]

def edge_roots(M, E):
    """the points of X_L(kbar): the distinct roots of f|L in kbar^*"""
    g = E['red']['poly']; u = g.parent().gen(0)
    while g % u == 0: g //= u
    e = lcm([h.degree() for h, _ in g.factor()])
    K = GF(M.l^e, 'w') if e > 1 else GF(M.l)
    return sorted(g.change_ring(K).roots(multiplicities=False)), K

# ---------------- Thm 3.13 + 3.14: the special fibre ----------------
def fibre(M):
    comp = []; inc = []; fidx = {}; edata = {}
    for n, F in enumerate(M.faces):
        fidx[n] = len(comp); comp.append([F['delta'], ('F', n)])
    for n, E in enumerate(M.edges):
        sd = slope_data(M, E); ch = hj_chain(sd['s1'], sd['s2']); r = len(ch) - 2
        rts, K = edge_roots(M, E)
        edata[n] = dict(sd=sd, ch=ch, r=r, roots=rts, K=K, idx={})
        for c, rt in enumerate(rts):
            prev = fidx[sd['F1']]
            for i in range(1, r+1):
                k = len(comp)
                comp.append([E['delta']*ch[i].denominator(), ('L', n, c, i)])
                edata[n]['idx'][(c, i)] = k
                inc.append((prev, k)); prev = k
            if sd['inner']:
                inc.append((prev, fidx[sd['F2']]))
    return comp, inc, fidx, edata

def imatrix(comp, inc):
    n = len(comp); m = vector(ZZ, [c[0] for c in comp])
    M = matrix(QQ, n, n)
    for (i, j) in inc:
        M[i, j] += 1; M[j, i] += 1
    for i in range(n):
        M[i, i] = -sum(m[j]*M[i, j] for j in range(n) if j != i)/m[i]
    return M, m

# ---------------- Rem 3.19: reduction of a rational point ----------------
def reduce_point(M, comp, fidx, edata, px, py):
    vx, vy = QQ(px).valuation(M.l), QQ(py).valuation(M.l)
    vs = [(v[0], v[1], v[2]) for v in M.P3.vertices()]
    best = min(vx*v[0] + vy*v[1] + v[2] for v in vs)
    S = frozenset((v[0], v[1]) for v in vs if vx*v[0] + vy*v[1] + v[2] == best)
    for n, F in enumerate(M.faces):                       # case (2)
        if S == F['verts']:
            return fidx[n], ('face', n, F['delta'])
    if len(S) != 2:
        return None, ('minimised on a %d-point set' % len(S),)
    for n, E in enumerate(M.edges):
        if S != frozenset([E['p'], E['q']]): continue
        d = edata[n]; sd = d['sd']
        if d['r'] == 0:
            # Thm 3.14: outer with delta_L = delta_F -- the point sits on X_F-bar
            if (not sd['inner']) and E['delta'] == M.faces[sd['F1']]['delta']:
                return fidx[sd['F1']], ('face via outer edge', sd['F1'],
                                        M.faces[sd['F1']]['delta'])
            return None, ('edge with r = 0 but not the outer delta_L = delta_F case',)
        # which chain: the root r of f|L that the point reduces to
        P0 = E['red']['P0']; w = E['red']['basis'].row(0)
        dv = E['vL'](*(vector(ZZ, P0) + w)) - E['vL'](*P0)
        ut = M.l^dv * QQ(px)^ZZ(w[0]) * QQ(py)^ZZ(w[1])
        if QQ(ut).valuation(M.l) != 0:
            return None, ('the edge coordinate is not a unit',)
        rt = d['K'](GF(M.l)(ut))
        if rt not in d['roots']:
            return None, ('reduction %s is not a root of f|L' % rt,)
        c = d['roots'].index(rt)
        # which component of the chain: s(v) = -delta_L * (v_x,v_y).(P1-P0)
        s = -E['delta']*(vx*(sd['P1']-sd['P0'])[0] + vy*(sd['P1']-sd['P0'])[1])
        # the fan ray carrying (v_x,v_y).  For an outer edge the chain is
        # truncated at s_2 = floor(s_1 - 1) and everything beyond it lies at the
        # free end of Gamma^r -- which is where the points of C \ C_0 over the
        # roots of f|L sit (Rem 3.19(a)), so points of C_0 near them reduce there.
        hit = [i for i in range(1, d['r']+1) if d['ch'][i] == s]
        clamped = False
        if not hit and not sd['inner'] and s <= d['ch'][d['r']]:
            hit = [d['r']]; clamped = True
        if len(hit) != 1:
            return None, ('slope %s is not carried by the chain %s' % (s, d['ch']),)
        i = hit[0]
        k = d['idx'][(c, i)]
        return k, ('chain-end' if clamped else 'chain', n, rt, s, comp[k][0])
    return None, ('no v-edge matches the minimising set',)

