"""T15 (g): the prefix of route beta (n < 16 test) at any machine installing TMIroot."""
import os, sys, json, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *
import num
import lin
lin.FASTPATH = True
from lin import linarith

G1 = '( 1st ` ( 1st ` T ) )'
L_ = '( 2nd ` ( 1st ` T ) )'
S_ = '( TM2Stmt ` T )'
DG = 'dom %s' % G1
STK = '( TM2Stk ` T )'
CTX = '( ( T e. V /\\ M : %s --> %s ) /\\ ( %s = TMGam /\\ ( 2nd ` T ) = TMSt ) )' % (L_, S_, G1)
X0 = '( encNatGam ` N )'
Z = '( # ` ( encodeNat ` N ) )'


def INIT(k, X, v='k'):
    return '( %s e. %s |-> if ( %s = %s , %s , (/) ) )' % (v, DG, v, k, X)


def UPD(D, K, Y):
    return '( ( %s |` ( %s \\ { %s } ) ) u. { <. %s , %s >. } )' % (D, DG, K, K, Y)


def CL(A, D, H='( 2nd ` T )'):
    return '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (A, H, D)


def TRI(C, D, N):
    return '%s ( T TM2Hoare M ) <. %s , %s >.' % (C, D, N)


class Pre:
    def __init__(self, w, ph):
        self.w, self.ph = w, ph
        self.memo = {}
        self.w.memo = {}

    def s(self, h, r, f):
        return self.w.s(h, r, '( %s -> %s )' % (self.ph, f))

    def c(self, f, ref, hyps=()):
        if f in self.memo: return self.memo[f]
        st = self.w.s(list(hyps), ref, f); self.memo[f] = st; return st

    def d(self, st, f):
        key = ('d', f)
        if key in self.memo: return self.memo[key]
        r = self.w.s([st], 'a1i', '( %s -> %s )' % (self.ph, f)); self.memo[key] = r; return r

    def neq(self, i, k):
        f = '-. %s = %s' % (i, k)
        if f in self.memo: return self.memo[f]
        w = self.w
        i_, k_ = int(i), int(k)
        lo, hi = min(i_, k_), max(i_, k_)
        lt = num.le_nat(w, lo, hi, strict=True)
        r1 = num.re_nat(w, lo)
        ne = self.c('%d =/= %d' % (lo, hi), 'ltneii', [r1, lt])
        if i_ == lo:
            st = self.c(f, 'neii', [ne])
        else:
            ne2 = self.c('%d =/= %d' % (hi, lo), 'necomi', [ne])
            st = self.c(f, 'neii', [ne2])
        return st

    def ned(self, i, k):
        """( ph -> i =/= k )"""
        f = '%s =/= %s' % (i, k)
        key = ('ned', f)
        if key in self.memo: return self.memo[key]
        n = self.neq(i, k)
        st = self.c(f, 'df-ne' if False else 'neir', [n]) if False else None
        w = self.w
        i_, k_ = int(i), int(k)
        lo, hi = min(i_, k_), max(i_, k_)
        ne = self.c('%d =/= %d' % (lo, hi), 'ltneii', [num.re_nat(w, lo), num.le_nat(w, lo, hi, strict=True)])
        if i_ != lo:
            ne = self.c('%d =/= %d' % (hi, lo), 'necomi', [ne])
        r = self.d(ne, f)
        self.memo[key] = r
        return r

    def stk8(self, k):
        """( ph -> k e. ( 0 ..^ 8 ) )"""
        key = ('stk8', k)
        if key in self.memo: return self.memo[key]
        w = self.w
        n = int(k)
        a = num.nn0(w, n); b = self.c('8 e. NN', '8nn'); c = num.le_nat(w, n, 8, strict=True)
        e = self.c('( %s e. ( 0 ..^ 8 ) <-> ( %s e. NN0 /\\ 8 e. NN /\\ %s < 8 ) )' % (k, k, k), 'elfzo0')
        f = self.c('%s e. ( 0 ..^ 8 )' % k, 'mpbir3an', [a, b, c, e])
        r = self.d(f, '%s e. ( 0 ..^ 8 )' % k)
        self.memo[key] = r
        return r

    def kdom(self, k):
        key = ('kdom', k)
        if key in self.memo: return self.memo[key]
        w = self.w
        j = self.s([self.tg, self.stk8(k)], 'jca', '( %s = TMGam /\\ %s e. ( 0 ..^ 8 ) )' % (G1, k))
        r = self.s([j, w.inst('t15kdom')], 'syl', "( %s e. %s /\\ ( %s ` %s ) = Gamma' )" % (k, DG, G1, k))
        a = self.s([r], 'simpld', '%s e. %s' % (k, DG))
        b = self.s([r], 'simprd', "( %s ` %s ) = Gamma'" % (G1, k))
        self.memo[key] = (a, b)
        return a, b

    def ctx(self, cstep):
        """cstep : ( ph -> CTX )"""
        self.cx = cstep
        self.tvm = self.s([cstep], 'simpld', '( T e. V /\\ M : %s --> %s )' % (L_, S_))
        self.tv = self.s([self.tvm], 'simpld', 'T e. V')
        self.gs = self.s([cstep], 'simprd', '( %s = TMGam /\\ ( 2nd ` T ) = TMSt )' % G1)
        self.tg = self.s([self.gs], 'simpld', '%s = TMGam' % G1)
        self.ts = self.s([self.gs], 'simprd', '( 2nd ` T ) = TMSt')

    # ------------------------------------------------ stacks
    def initstk(self, k, X, xgam):
        """INIT(k, X) e. Stk (bound k); xgam : ( ph -> X e. Word Gamma' )"""
        w = self.w
        kd, kg = self.kdom(k)
        wq = self.s([kg, w.inst('wrdeq')], 'syl', "Word ( %s ` %s ) = Word Gamma'" % (G1, k))
        xg = self.s([xgam, wq], 'eleqtrrd', '%s e. Word ( %s ` %s )' % (X, G1, k))
        m = self.s([self.tv, kd, xg, w.inst('tm2initstk')], 'syl3anc', '%s e. %s' % (INIT(k, X, 'j'), STK))
        cb1 = w.s([], 'eqeq1', '( k = j -> ( k = %s <-> j = %s ) )' % (k, k))
        cb2 = w.s([cb1], 'ifbid', '( k = j -> if ( k = %s , %s , (/) ) = if ( j = %s , %s , (/) ) )' % (k, X, k, X))
        cb = w.s([cb2], 'cbvmptv', '%s = %s' % (INIT(k, X), INIT(k, X, 'j')))
        return self.s([self.d(cb, '%s = %s' % (INIT(k, X), INIT(k, X, 'j'))), m], 'eqeltrd', '%s e. %s' % (INIT(k, X), STK))

    def wordg(self, X, xgam, k):
        """( ph -> X e. Word ( G ` k ) ) from xgam ( ph -> X e. Word Gamma' )"""
        kd, kg = self.kdom(k)
        wq = self.s([kg, self.w.inst('wrdeq')], 'syl', "Word ( %s ` %s ) = Word Gamma'" % (G1, k))
        return self.s([xgam, wq], 'eleqtrrd', '%s e. Word ( %s ` %s )' % (X, G1, k))

    def updstk(self, D, dstk, K, Y, ygam):
        w = self.w
        kd, kg = self.kdom(K)
        yg = self.wordg(Y, ygam, K)
        j = self.s([kd, yg], 'jca', '( %s e. %s /\\ %s e. Word ( %s ` %s ) )' % (K, DG, Y, G1, K))
        return self.s([self.tv, dstk, j, w.inst('tm2stkupd')], 'syl3anc', '%s e. %s' % (UPD(D, K, Y), STK))

    def initval(self, k, X, j):
        """( ph -> ( INIT(k,X) ` j ) = value )"""
        w = self.w
        kd, _ = self.kdom(j)
        body = 'if ( k = %s , %s , (/) )' % (k, X)
        ex = self.s([], 'ifexd' if False else 'fvexd', '') if False else None
        val = X if j == k else '(/)'
        # substitution hypothesis
        eqi = w.s([], 'id', '( k = %s -> k = %s )' % (j, j))
        st, v2 = cong(w, body, {'k': j}, 'k = %s' % j, {'k': eqi})
        mp = INIT(k, X)
        exv = self.s([], 'fvexd', '%s e. _V' % v2) if False else None
        # value is if ( j = k , X , (/) ): prove it is a set via ifex
        xs = self.s([], 'fvexd', '%s e. _V' % X) if X.startswith('( encNatGam') and False else None
        e1 = self.xset(X)
        e0 = self.d(self.c('(/) e. _V', '0ex'), '(/) e. _V')
        ie = self.s([e1, e0], 'ifcld', '%s e. _V' % v2)
        df = w.s([], 'eqid', '%s = %s' % (mp, mp))
        fm = w.s([st, df], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (j, DG, v2, mp, j, v2))
        a = self.s([kd, ie, fm], 'syl2anc', '( %s ` %s ) = %s' % (mp, j, v2))
        if j == k:
            b = self.s([self.d(self.c('%s = %s' % (j, j), 'eqid'), '%s = %s' % (j, j))], 'iftrued', '%s = %s' % (v2, X))
        else:
            b = self.s([self.d(self.neq(j, k), '-. %s = %s' % (j, k))], 'iffalsed', '%s = (/)' % v2)
        return self.s([a, b], 'eqtrd', '( %s ` %s ) = %s' % (mp, j, val)), val

    def xset(self, X):
        key = ('xset', X)
        if key in self.memo: return self.memo[key]
        w = self.w
        if X == '(/)':
            r = self.d(self.c('(/) e. _V', '0ex'), '(/) e. _V')
        elif X.startswith('( ') and ' ++ ' in X and X.endswith(' )'):
            r = self.s([], 'ovexd', '%s e. _V' % X)
        elif X.startswith('( ') and ' ` ' in X:
            r = self.s([], 'fvexd', '%s e. _V' % X)
        else:
            raise NotImplementedError(X)
        self.memo[key] = r
        return r

    def updval(self, D, dstk, K, Y, j, dval=None):
        """( ph -> ( UPD(D,K,Y) ` j ) = value ); dval(j) gives ( step, value ) for ( D ` j )"""
        w = self.w
        kd, _ = self.kdom(K)
        jd, _ = self.kdom(j)
        ys = self.xset(Y)
        j1 = self.s([self.tv, dstk], 'jca', '( T e. V /\\ %s e. %s )' % (D, STK))
        j2 = self.s([kd, ys], 'jca', '( %s e. %s /\\ %s e. _V )' % (K, DG, Y))
        u = self.s([j1, j2, jd, w.inst('tm2stkupv')], 'syl3anc',
                   '( %s ` %s ) = if ( %s = %s , %s , ( %s ` %s ) )' % (UPD(D, K, Y), j, j, K, Y, D, j))
        if j == K:
            b = self.s([self.d(self.c('%s = %s' % (j, j), 'eqid'), '%s = %s' % (j, j))], 'iftrued',
                       'if ( %s = %s , %s , ( %s ` %s ) ) = %s' % (j, K, Y, D, j, Y))
            return self.s([u, b], 'eqtrd', '( %s ` %s ) = %s' % (UPD(D, K, Y), j, Y)), Y
        b = self.s([self.d(self.neq(j, K), '-. %s = %s' % (j, K))], 'iffalsed',
                   'if ( %s = %s , %s , ( %s ` %s ) ) = ( %s ` %s )' % (j, K, Y, D, j, D, j))
        st = self.s([u, b], 'eqtrd', '( %s ` %s ) = ( %s ` %s )' % (UPD(D, K, Y), j, D, j))
        if dval is None:
            return st, '( %s ` %s )' % (D, j)
        s2, v = dval(j)
        return self.s([st, s2], 'eqtrd', '( %s ` %s ) = %s' % (UPD(D, K, Y), j, v)), v


def parse_tri(f):
    t = f.split()
    k = t.index('TM2Hoare')
    d = 0; st = k - 1
    while True:
        x = t[st]
        if x in CLOSE: d += 1
        elif x in OPEN:
            if d == 0: break
            d -= 1
        st -= 1
    en = grab(t, st)
    C = ' '.join(t[:st])
    rest = t[en:]
    assert rest[0] == '<.' and rest[-1] == '>.'
    inner = rest[1:-1]; d = 0
    for q, x in enumerate(inner):
        if x in OPEN: d += 1
        elif x in CLOSE: d -= 1
        elif d == 0 and x == ',':
            return C, ' '.join(inner[:q]), ' '.join(inner[q + 1:])
    raise ValueError(f)


def seq(X, ta, fa, tb, fb):
    Ca, Da, Na = parse_tri(fa); Cb, Db, Nb = parse_tri(fb)
    assert Da == Cb, (Da, Cb)
    f = TRI(Ca, Db, '( %s + %s )' % (Na, Nb))
    return X.s([X.tvm, ta, tb, X.w.inst('tm2hseq')], 'syl3anc', f), f


def transport(X, t, f, peq, Pn):
    """from ( ph -> C ~~> <. P , N >. ) and ( ph -> P = Pn ) get the triple with Pn"""
    w = X.w
    C, P_, N = parse_tri(f)
    ss = X.s([peq], 'eqimssd', '%s C_ %s' % (P_, Pn))
    fx = X.s([X.tvm], 'simprd', 'M : %s --> %s' % (L_, S_))
    lx = X.s([], 'fvexd', '%s e. _V' % L_)
    mx = X.s([fx, lx, w.inst('fex')], 'syl2anc', 'M e. _V')
    j = X.s([X.s([X.tv, mx], 'jca', '( T e. V /\\ M e. _V )'), t], 'jca', '( ( T e. V /\\ M e. _V ) /\\ %s )' % f)
    ty = X.s([j, w.inst('tm2hrtyp')], 'syl', '( %s C_ ( TM2Cfg ` T ) /\\ %s C_ ( TM2Cfg ` T ) /\\ %s e. NN0 )' % (C, P_, N))
    ty2 = X.s([ty], 'simp2d', '%s C_ ( TM2Cfg ` T )' % P_)
    ty3 = X.s([peq, ty2], 'eqsstrrd', '%s C_ ( TM2Cfg ` T )' % Pn)
    j2 = X.s([X.tvm, t], 'jca', '( ( T e. V /\\ M : %s --> %s ) /\\ %s )' % (L_, S_, f))
    j3 = X.s([ss, ty3], 'jca', '( %s C_ %s /\\ %s C_ ( TM2Cfg ` T ) )' % (P_, Pn, Pn))
    f2 = TRI(C, Pn, N)
    return X.s([j2, j3, w.inst('tm2hssd')], 'syl2anc', f2), f2


def unfold_root(w, ph, rstep):
    """rstep: ( ph -> TMIroot C K T M P E ); returns dict of pieces"""
    rhs = ROOT_RHS
    P = load_preds()
    P['TMIroot'] = (['C', 'K', 'T', 'M', 'P', 'E'], rhs.split(), 'df-tmiroot')
    tr = wff_tree(rhs.split(), P)
    df = w.s([], 'df-tmiroot', '( TMIroot C K T M P E <-> %s )' % rhs)
    top = w.s([rstep, df], 'sylib', '( %s -> %s )' % (ph, rhs))
    out = []

    def text(n):
        if n[0] == 'and': return '( %s )' % ' /\\ '.join(text(k) for k in n[1])
        if n[0] == 'pred':
            vs = P[n[1]][0]
            return '%s %s' % (n[1], ' '.join(' '.join(n[2][v]) for v in vs))
        return '%s %s %s' % (' '.join(n[1]), '=' if n[0] == 'eq' else 'e.', ' '.join(n[2]))

    def walk(n, st):
        if n[0] != 'and':
            out.append((text(n), st)); return
        k = len(n[1])
        refs = ['simpld', 'simprd'] if k == 2 else ['simp1d', 'simp2d', 'simp3d']
        for kid, r in zip(n[1], refs):
            s2 = w.s([st], r, '( %s -> %s )' % (ph, text(kid)))
            walk(kid, s2)
    walk(tr, top)
    return dict(out)


def t15pre1():
    w = W('t15pre1', 'The prefix of route beta, first part: copy the input, duplicate it, push 16 and compare (Lean: the small-input deviation, T13-blueprint 4.2).')
    ph = '( ( %s /\\ TMIroot C K T M P E ) /\\ N e. NN0 )' % CTX
    X = Pre(w, ph)
    cx = X.s([], 'simpll', CTX)
    X.ctx(cx)
    root = X.s([], 'simplr', 'TMIroot C K T M P E')
    nn = X.s([], 'simpr', 'N e. NN0')
    pc = unfold_root(w, ph, root)
    # words
    g4 = X.d(X.c("<\" 4 \"> e. Word Gamma'", 'ax-mp', [X.c("4 e. Gamma'", 'gamma4'), w.inst('s1cl')]), "<\" 4 \"> e. Word Gamma'")
    w0 = X.d(X.c("(/) e. Word Gamma'", 'wrd0'), "(/) e. Word Gamma'")
    x0g = X.s([nn, w.inst('encnatgamcl')], 'syl', "%s e. Word Gamma'" % X0)
    ev = X.s([nn, w.inst('encnatgamval')], 'syl', '%s = ( inclBool o. ( encodeNat ` N ) )' % X0)
    enc = X.s([nn, w.inst('encnatcl')], 'syl', '( encodeNat ` N ) e. Word 2o')
    icl = X.d(X.c('inclBool : 2o --> ( { 1 } X. 2o )', 'tmcinclf'), 'inclBool : 2o --> ( { 1 } X. 2o )')
    ico = X.s([enc, icl, w.inst('wrdco')], 'syl2anc', '( inclBool o. ( encodeNat ` N ) ) e. Word ( { 1 } X. 2o )')
    x0b = X.s([ev, ico], 'eqeltrd', '%s e. Word ( { 1 } X. 2o )' % X0)
    X4 = '( %s ++ <" 4 "> )' % X0
    x4g = X.s([x0g, g4, w.inst('ccatcl')], 'syl2anc', "%s e. Word Gamma'" % X4)
    D0 = INIT('0', X0)
    D1 = INIT('7', X4)
    L = {}
    L[CTX] = cx
    # T1: input copy
    L['TMIinp T M ( P ` 0 ) ( ( P ` 1 ) ` 0 )'] = pc['TMIinp T M ( P ` 0 ) ( ( P ` 1 ) ` 0 )']
    L['N e. NN0'] = nn
    t1, f1 = use(w, ph, 'tmiinp', {'P': '( P ` 0 )', 'E': '( ( P ` 1 ) ` 0 )'}, L)
    # T2: dup 7 6 5
    d1s = X.initstk('7', X4, x4g)
    d17, _ = X.initval('7', X4, '7')
    r4 = X.d(X.c('( <" 4 "> ++ (/) ) = <" 4 ">', 'ax-mp', [X.c("<\" 4 \"> e. Word Gamma'", 'ax-mp', [X.c("4 e. Gamma'", 'gamma4'), w.inst('s1cl')]), w.inst('ccatrid')]), '( <" 4 "> ++ (/) ) = <" 4 ">')
    r4b = X.s([r4], 'oveq2d', '( %s ++ ( <" 4 "> ++ (/) ) ) = %s' % (X0, X4))
    d17b = X.s([d17, r4b], 'eqtr4d', '( %s ` 7 ) = ( %s ++ ( <" 4 "> ++ (/) ) )' % (D1, X0))
    for k in ('7', '6', '5', '4'):
        L['%s e. ( 0 ..^ 8 )' % k] = X.stk8(k)
    for a, b in (('7', '6'), ('7', '5'), ('6', '5'), ('4', '6')):
        L['%s =/= %s' % (a, b)] = X.ned(a, b)
    L['TMIdup 7 6 5 T M ( P ` 1 ) ( ( P ` 2 ) ` 0 )'] = pc['TMIdup 7 6 5 T M ( P ` 1 ) ( ( P ` 2 ) ` 0 )']
    L['%s e. Word ( { 1 } X. 2o )' % X0] = x0b
    L["(/) e. Word Gamma'"] = w0
    L['%s e. %s' % (D1, STK)] = d1s
    L['( %s ` 7 ) = ( %s ++ ( <" 4 "> ++ (/) ) )' % (D1, X0)] = d17b
    t2, f2 = use(w, ph, 'tmidup', {'K': '7', 'J': '6', 'I': '5', 'P': '( P ` 1 )', 'E': '( ( P ` 2 ) ` 0 )',
                                  'W': X0, 'X': '(/)', 'D': D1}, L)
    Y2 = '( %s ++ ( <" 4 "> ++ ( %s ` 6 ) ) )' % (X0, D1)
    D2 = UPD(D1, '6', Y2)
    d16, _ = X.initval('7', X4, '6')
    y2a = X.s([d16, w0], 'eqeltrd' if False else 'eqeltrrd', '') if False else None
    d16g = X.s([d16, w0], 'eqeltrd', "( %s ` 6 ) e. Word Gamma'" % D1)
    y2b = X.s([g4, d16g, w.inst('ccatcl')], 'syl2anc', "( <\" 4 \"> ++ ( %s ` 6 ) ) e. Word Gamma'" % D1)
    y2g = X.s([x0g, y2b, w.inst('ccatcl')], 'syl2anc', "%s e. Word Gamma'" % Y2)
    d2s = X.updstk(D1, d1s, '6', Y2, y2g)
    # T3: pnv 4 16
    L['TMIpnv 4 ; 1 6 T M ( P ` 2 ) ( ( P ` 3 ) ` 0 )'] = pc['TMIpnv 4 ; 1 6 T M ( P ` 2 ) ( ( P ` 3 ) ` 0 )']
    L['; 1 6 e. NN0'] = X.d(num.nn0(w, 16), '; 1 6 e. NN0')
    L['%s e. %s' % (D2, STK)] = d2s
    t3, f3 = use(w, ph, 'tmipnv', {'K': '4', 'N': '; 1 6', 'P': '( P ` 2 )', 'E': '( ( P ` 3 ) ` 0 )', 'D': D2}, L)
    G16 = '( encNatGam ` ; 1 6 )'
    Y3 = '( %s ++ ( <" 4 "> ++ ( %s ` 4 ) ) )' % (G16, D2)
    D3 = UPD(D2, '4', Y3)
    dv1 = lambda j: X.initval('7', X4, j)
    d24, v24 = X.updval(D1, d1s, '6', Y2, '4', dv1)
    g16 = X.s([L['; 1 6 e. NN0'], w.inst('encnatgamcl')], 'syl', "%s e. Word Gamma'" % G16)
    d24g = X.s([d24, w0], 'eqeltrd', "( %s ` 4 ) e. Word Gamma'" % D2)
    y3b = X.s([g4, d24g, w.inst('ccatcl')], 'syl2anc', "( <\" 4 \"> ++ ( %s ` 4 ) ) e. Word Gamma'" % D2)
    y3g = X.s([g16, y3b, w.inst('ccatcl')], 'syl2anc', "%s e. Word Gamma'" % Y3)
    d3s = X.updstk(D2, d2s, '4', Y3, y3g)
    # T4: cmp 4 6
    Lw = '( encodeNat ` ; 1 6 )'
    Lp = '( encodeNat ` N )'
    d34, _ = X.updval(D2, d2s, '4', Y3, '4')
    e16 = X.s([L['; 1 6 e. NN0'], w.inst('encnatgamval')], 'syl', '%s = ( inclBool o. %s )' % (G16, Lw))
    c34 = X.s([d24], 'oveq2d', '( <" 4 "> ++ ( %s ` 4 ) ) = ( <" 4 "> ++ (/) )' % D2)
    c34b = X.s([e16, c34], 'oveq12d', '%s = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ (/) ) )' % (Y3, Lw))
    d34b = X.s([d34, c34b], 'eqtrd', '( %s ` 4 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ (/) ) )' % (D3, Lw))
    d26 = lambda j: X.updval(D1, d1s, '6', Y2, j, dv1)
    d36, _ = X.updval(D2, d2s, '4', Y3, '6')
    d26b, _ = X.updval(D1, d1s, '6', Y2, '6')
    c36 = X.s([d16], 'oveq2d', '( <" 4 "> ++ ( %s ` 6 ) ) = ( <" 4 "> ++ (/) )' % D1)
    c36b = X.s([ev, c36], 'oveq12d', '%s = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ (/) ) )' % (Y2, Lp))
    d36b = X.s([d36, d26b, c36b], '3eqtrd', '( %s ` 6 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ (/) ) )' % (D3, Lp))
    L['TMIcmp 4 6 T M ( P ` 3 ) ( P ` 4 )'] = pc['TMIcmp 4 6 T M ( P ` 3 ) ( P ` 4 )']
    L['%s e. Word 2o' % Lw] = X.s([L['; 1 6 e. NN0'], w.inst('encnatcl')], 'syl', '%s e. Word 2o' % Lw)
    L['%s e. Word 2o' % Lp] = enc
    L['%s e. %s' % (D3, STK)] = d3s
    L['( %s ` 4 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ (/) ) )' % (D3, Lw)] = d34b
    L['( %s ` 6 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ (/) ) )' % (D3, Lp)] = d36b
    t4, f4 = use(w, ph, 'tmicmp', {'K': '4', 'J': '6', 'P': '( P ` 3 )', 'E': '( P ` 4 )', 'L': Lw, "L'": Lp,
                                  'X': '(/)', 'Y': '(/)', 'D': D3}, L)
    # sequence
    t12, f12 = seq(X, t1, f1, t2, f2)
    t123, f123 = seq(X, t12, f12, t3, f3)
    tall, fall = seq(X, t123, f123, t4, f4)
    # post: toNat and D4 = D1
    D4a = UPD(D3, '4', '(/)')
    D4 = UPD(D4a, '6', '(/)')
    d4as = X.updstk(D3, d3s, '4', '(/)', w0)
    d4s = X.updstk(D4a, d4as, '6', '(/)', w0)
    vals = []
    for j in '01234567':
        def dv3(jj):
            def dv2(j2):
                return X.updval(D1, d1s, '6', Y2, j2, dv1)
            return X.updval(D2, d2s, '4', Y3, jj, dv2)
        a, va = X.updval(D4a, d4as, '6', '(/)', j, lambda jj: X.updval(D3, d3s, '4', '(/)', jj, dv3))
        b, vb = dv1(j)
        assert va == vb, (j, va, vb)
        vals.append(X.s([a, b], 'eqtr4d', '( %s ` %s ) = ( %s ` %s )' % (D4, j, D1, j)))
    L['( T e. V /\\ %s = TMGam )' % G1] = X.s([X.tv, X.tg], 'jca', '( T e. V /\\ %s = TMGam )' % G1)
    L['%s e. %s' % (D4, STK)] = d4s
    for j, st in zip('01234567', vals):
        L['( %s ` %s ) = ( %s ` %s )' % (D4, j, D1, j)] = st
    deq, _ = use(w, ph, 't12stkeq', {'A': D4, 'B': D1}, L)
    tn1 = X.s([L['; 1 6 e. NN0'], w.inst('tonatencnat')], 'syl', '( toNat ` %s ) = ; 1 6' % Lw)
    tn2 = X.s([nn, w.inst('tonatencnat')], 'syl', '( toNat ` %s ) = N' % Lp)
    C4, P4, N4 = parse_tri(fall)
    rules = {'( toNat ` %s )' % Lw: ('; 1 6', tn1), '( toNat ` %s )' % Lp: ('N', tn2), D4: (D1, deq)}
    peq, Pn = cong(w, P4, {}, ph, {}, rules=rules)
    H = '{ h e. TMSt | ( TMcmp ` h ) = ( ; 1 6 Ncmp N ) }'
    assert Pn == '( { ( inl ` ( P ` 4 ) ) } X. ( %s X. { %s } ) )' % (H, D1), Pn
    tall2 = transport(X, tall, fall, peq, Pn)
    # bound
    B0 = '( ( 5 x. %s ) + ; 5 0 )' % Z
    X4len = X.s([nn, w.inst('encnatgamlen')], 'syl', '( # ` %s ) = %s' % (X0, Z))
    zn = X.s([enc, w.inst('lencl')], 'syl', '%s e. NN0' % Z)
    zr = X.s([zn], 'nn0red', '%s e. RR' % Z)
    z0 = X.s([zn], 'nn0ge0d', '0 <_ %s' % Z)
    x0r = X.s([X.s([x0g, w.inst('lencl')], 'syl', '( # ` %s ) e. NN0' % X0)], 'nn0red', '( # ` %s ) e. RR' % X0)
    gn = X.s([g16, w.inst('lencl')], 'syl', '( # ` %s ) e. NN0' % G16)
    gr = X.s([gn], 'nn0red', '( # ` %s ) e. RR' % G16)
    ge = X.s([L['; 1 6 e. NN0'], w.inst('t15enl')], 'syl', '( ( # ` %s ) + 1 ) <_ ( ; 1 6 + 1 )' % G16)
    lwn = X.s([L['%s e. Word 2o' % Lw], w.inst('lencl')], 'syl', '( # ` %s ) e. NN0' % Lw)
    lwr = X.s([lwn], 'nn0red', '( # ` %s ) e. RR' % Lw)
    lweq = X.s([L['; 1 6 e. NN0'], w.inst('encnatgamlen')], 'syl', '( # ` %s ) = ( # ` %s )' % (G16, Lw))
    IFT = 'if ( ( # ` %s ) <_ ( # ` %s ) , ( # ` %s ) , ( # ` %s ) )' % (Lw, Lp, Lp, Lw)
    lw0 = X.s([lwn], 'nn0ge0d', '0 <_ ( # ` %s )' % Lw)
    j1 = X.s([lwr, zr], 'jca', '( ( # ` %s ) e. RR /\\ %s e. RR )' % (Lw, Z))
    j2 = X.s([lw0, z0], 'jca', '( 0 <_ ( # ` %s ) /\\ 0 <_ %s )' % (Lw, Z))
    ifl = X.s([j1, j2, w.inst('t15ifle')], 'syl2anc', '%s <_ ( ( # ` %s ) + %s )' % (IFT, Lw, Z))
    ifr = X.s([lwr, zr], 'ifcld' if False else 'ifcld', '%s e. RR' % IFT) if False else None
    ifr = X.s([zr, lwr], 'ifcld', '%s e. RR' % IFT)
    le = linarith(w, ph, [X4len, ge, lweq, ifl, z0], '%s <_ %s' % (N4, B0),
                  leaves={Z: zr, '( # ` %s )' % X0: x0r, '( # ` %s )' % G16: gr, '( # ` %s )' % Lw: lwr, IFT: ifr})
    b0n = X.s([X.s([X.d(num.nn0(w, 5), '5 e. NN0'), zn], 'nn0mulcld', '( 5 x. %s ) e. NN0' % Z), X.d(num.nn0(w, 50), '; 5 0 e. NN0')], 'nn0addcld', '%s e. NN0' % B0)
    fin = hle(X, tall2, parse_tri(tall2[1])[0] if False else None, None) if False else None
    Cf, Pf, Nf = parse_tri(tall2[1])
    j3 = X.s([b0n, le], 'jca', '( %s e. NN0 /\\ %s <_ %s )' % (B0, Nf, B0))
    j4 = X.s([X.tvm, tall2[0]], 'jca', '( ( T e. V /\\ M : %s --> %s ) /\\ %s )' % (L_, S_, tall2[1]))
    w.qed([j4, j3, w.inst('tm2hle')], 'syl2anc', '( %s -> %s )' % (ph, TRI(Cf, Pf, B0)))
    w.t = (t1, f1, t2, f2, t3, f3, t4, f4)
    w.X = X; w.L = L; w.D = (D0, D1, D2, D3); w.misc = dict(nn=nn, x0g=x0g, x0b=x0b, x4g=x4g, d1s=d1s, d2s=d2s, d3s=d3s,
                                                            enc=enc, g16=g16, pc=pc, ev=ev)
    return w



def t15ifle():
    w = W('t15ifle', 'The larger of two nonnegative reals is at most their sum.')
    ph = '( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) )'
    ar = w.s([], 'simpll', '( %s -> A e. RR )' % ph)
    br = w.s([], 'simplr', '( %s -> B e. RR )' % ph)
    a0 = w.s([], 'simprl', '( %s -> 0 <_ A )' % ph)
    b0 = w.s([], 'simprr', '( %s -> 0 <_ B )' % ph)
    I = 'if ( A <_ B , B , A )'
    p1 = '( %s /\\ A <_ B )' % ph
    i1 = w.s([w.s([], 'simpr', '( %s -> A <_ B )' % p1)], 'iftrued', '( %s -> %s = B )' % (p1, I))
    c1 = w.s([w.s([a0], 'adantr', '( %s -> 0 <_ A )' % p1), w.s([br], 'adantr', '( %s -> B e. RR )' % p1), w.s([ar], 'adantr', '( %s -> A e. RR )' % p1)], 'addge02d', '( %s -> ( 0 <_ A <-> B <_ ( A + B ) ) )' % p1) if False else None
    ar1 = w.s([ar], 'adantr', '( %s -> A e. RR )' % p1)
    br1 = w.s([br], 'adantr', '( %s -> B e. RR )' % p1)
    a01 = w.s([a0], 'adantr', '( %s -> 0 <_ A )' % p1)
    c1b = w.s([br1, ar1], 'addge02d', '( %s -> ( 0 <_ A <-> B <_ ( A + B ) ) )' % p1)
    c1 = w.s([a01, c1b], 'mpbid', '( %s -> B <_ ( A + B ) )' % p1)
    e1 = w.s([i1, c1], 'eqbrtrd', '( %s -> %s <_ ( A + B ) )' % (p1, I))
    p2 = '( %s /\\ -. A <_ B )' % ph
    i2 = w.s([w.s([], 'simpr', '( %s -> -. A <_ B )' % p2)], 'iffalsed', '( %s -> %s = A )' % (p2, I))
    ar2 = w.s([ar], 'adantr', '( %s -> A e. RR )' % p2)
    br2 = w.s([br], 'adantr', '( %s -> B e. RR )' % p2)
    b02 = w.s([b0], 'adantr', '( %s -> 0 <_ B )' % p2)
    c2b = w.s([ar2, br2], 'addge01d', '( %s -> ( 0 <_ B <-> A <_ ( A + B ) ) )' % p2)
    c2 = w.s([b02, c2b], 'mpbid', '( %s -> A <_ ( A + B ) )' % p2)
    e2 = w.s([i2, c2], 'eqbrtrd', '( %s -> %s <_ ( A + B ) )' % (p2, I))
    w.qed([e1, e2], 'pm2.61dan', '( %s -> %s <_ ( A + B ) )' % (ph, I))
    return w



def unfold(w, ph, name, argmap, step, dflab=None):
    """step : ( ph -> NAME args ); returns {leaf text: step} of its definition's right side"""
    P = load_preds()
    if name == 'TMIroot':
        P['TMIroot'] = (['C', 'K', 'T', 'M', 'P', 'E'], ROOT_RHS.split(), 'df-tmiroot')
    vs, body, lab = P[name]
    rhs = subst_text(' '.join(body), argmap)
    head = '%s %s' % (name, ' '.join(argmap.get(v, v) for v in vs))
    df = w.s([], lab, '( %s <-> %s )' % (head, rhs))
    top = w.s([step, df], 'sylib', '( %s -> %s )' % (ph, rhs))
    tr = wff_tree(rhs.split(), P)
    out = {}

    def text(n):
        if n[0] == 'and': return '( %s )' % ' /\\ '.join(text(k) for k in n[1])
        if n[0] == 'pred':
            vv = P[n[1]][0]
            return '%s %s' % (n[1], ' '.join(' '.join(n[2][v]) for v in vv))
        return '%s %s %s' % (' '.join(n[1]), '=' if n[0] == 'eq' else 'e.', ' '.join(n[2]))

    def walk(n, st):
        out[text(n)] = st
        if n[0] != 'and':
            return
        k = len(n[1])
        refs = ['simpld', 'simprd'] if k == 2 else ['simp1d', 'simp2d', 'simp3d']
        for kid, r in zip(n[1], refs):
            walk(kid, w.s([st], r, '( %s -> %s )' % (ph, text(kid))))
    walk(tr, top)
    return out


H16 = '{ h e. TMSt | ( TMcmp ` h ) = ( ; 1 6 Ncmp N ) }'
BRF = '( u e. TMSt |-> if ( ( TMcmp ` u ) = 2o , (/) , 1o ) )'


def gotocl(X, lab_step, lab):
    w = X.w
    lx = X.s([], 'fvexd', '%s e. _V' % L_)
    c = X.s([X.s([lx, lab_step], 'jca', '( %s e. _V /\\ %s e. %s )' % (L_, lab, L_)), w.inst('t15cst')], 'syl',
            '( ( 2nd ` T ) X. { %s } ) e. ( %s ^m ( 2nd ` T ) )' % (lab, L_))
    g = X.s([X.tv, c, w.inst('tm2goto')], 'syl2anc', '<. 5 , ( ( 2nd ` T ) X. { %s } ) >. e. %s' % (lab, S_))
    return c, g


def branch(X, pc, D1, d1s, big, labs):
    """the branch at ( P ` 4 ): triple from CL( P4 , D1 , H16 ) to CL( target , D1 , H16 ) in 1"""
    w, ph = X.w, X.ph
    tgt = '( P ` 5 )' if big else '( ( P ` 7 ) ` 0 )'
    G5 = '( ( 2nd ` T ) X. { ( P ` 5 ) } )'
    G7 = '( ( 2nd ` T ) X. { ( ( P ` 7 ) ` 0 ) } )'
    BR = '<. 4 , <. %s , <. <. 5 , %s >. , <. 5 , %s >. >. >. >.' % (BRF, G5, G7)
    Pc = '( %s X. { %s } )' % (H16, D1)
    Dc = '( { ( inl ` %s ) } X. %s )' % (tgt, Pc)
    hsT = X.d(X.c('%s C_ TMSt' % H16, 'ssrab2'), '%s C_ TMSt' % H16)
    hsS = X.s([hsT, X.ts], 'sseqtrrd', '%s C_ ( 2nd ` T )' % H16)
    ds = X.s([d1s], 'snssd', '{ %s } C_ %s' % (D1, STK))
    pcs = X.s([hsS, ds, w.inst('xpss12')], 'syl2anc', '%s C_ ( ( 2nd ` T ) X. %s )' % (Pc, STK))
    dcs = X.s([X.tv, labs[tgt], pcs, w.inst('tm2hcfgss')], 'syl3anc', '%s C_ ( TM2Cfg ` T )' % Dc)
    # handler typing
    pu = '( %s /\\ u e. TMSt )' % ph
    ic = w.s([w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % pu),
              w.s([w.s([], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % pu)], 'ifcld',
             '( %s -> if ( ( TMcmp ` u ) = 2o , (/) , 1o ) e. 2o )' % pu)
    al = X.s([ic], 'ralrimiva', 'A. u e. TMSt if ( ( TMcmp ` u ) = 2o , (/) , 1o ) e. 2o')
    o2 = X.d(X.c('2o e. _V', '2oex'), '2o e. _V')
    fty = X.s([X.ts, o2, al, w.inst('tmcmapty')], 'syl3anc', '%s e. ( 2o ^m ( 2nd ` T ) )' % BRF)
    c5, g5 = gotocl(X, labs['( P ` 5 )'], '( P ` 5 )')
    c7, g7 = gotocl(X, labs['( ( P ` 7 ) ` 0 )'], '( ( P ` 7 ) ` 0 )')
    # the quantified part
    pa = '( %s /\\ a e. %s )' % (ph, Pc)
    sub = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (pa, f))
    am = w.s([], 'simpr', '( %s -> a e. %s )' % (pa, Pc))
    s1 = w.s([am, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` a ) e. %s )' % (pa, H16))
    s2 = w.s([am, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` a ) e. { %s } )' % (pa, D1))
    s2e = w.s([s2, w.inst('elsni')], 'syl', '( %s -> ( 2nd ` a ) = %s )' % (pa, D1))
    ae = w.s([am, w.inst('1st2nd2')], 'syl', '( %s -> a = <. ( 1st ` a ) , ( 2nd ` a ) >. )' % pa)
    s_ = '( 1st ` a )'
    op = w.s([s2e], 'opeq2d', '( %s -> <. %s , ( 2nd ` a ) >. = <. %s , %s >. )' % (pa, s_, s_, D1))
    a2 = w.s([ae, op], 'eqtrd', '( %s -> a = <. %s , %s >. )' % (pa, s_, D1))
    er = w.s([], 'elrab' if False else 'elrab', '') if False else None
    fvh = '( TMcmp ` h ) = ( ; 1 6 Ncmp N )'
    cb = w.s([w.s([], 'fveq2', '( h = %s -> ( TMcmp ` h ) = ( TMcmp ` %s ) )' % (s_, s_))], 'eqeq1d',
             '( h = %s -> ( ( TMcmp ` h ) = ( ; 1 6 Ncmp N ) <-> ( TMcmp ` %s ) = ( ; 1 6 Ncmp N ) ) )' % (s_, s_))
    el = w.s([cb], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ ( TMcmp ` %s ) = ( ; 1 6 Ncmp N ) ) )' % (s_, H16, s_, s_))
    s3 = w.s([s1, el], 'sylib', '( %s -> ( %s e. TMSt /\\ ( TMcmp ` %s ) = ( ; 1 6 Ncmp N ) ) )' % (pa, s_, s_))
    sT = w.s([s3], 'simpld', '( %s -> %s e. TMSt )' % (pa, s_))
    cmv = w.s([s3], 'simprd', '( %s -> ( TMcmp ` %s ) = ( ; 1 6 Ncmp N ) )' % (pa, s_))
    tsa = sub(X.ts, '( 2nd ` T ) = TMSt')
    sS = w.s([sT, tsa], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (pa, s_))
    d1a = sub(d1s, '%s e. %s' % (D1, STK))
    mbr = sub(pc['( M ` ( P ` 4 ) ) = %s' % BR], '( M ` ( P ` 4 ) ) = %s' % BR)
    SA = '( TM2sa ` T )'
    e1 = w.s([mbr, a2], 'oveq12d', '( %s -> ( ( M ` ( P ` 4 ) ) %s a ) = ( %s %s <. %s , %s >. ) )' % (pa, SA, BR, SA, s_, D1))
    tva = sub(X.tv, 'T e. V')
    jb = w.s([sub(fty, '%s e. ( 2o ^m ( 2nd ` T ) )' % BRF), sub(g5, '<. 5 , %s >. e. %s' % (G5, S_)), sub(g7, '<. 5 , %s >. e. %s' % (G7, S_))], '3jca',
             '( %s -> ( %s e. ( 2o ^m ( 2nd ` T ) ) /\\ <. 5 , %s >. e. %s /\\ <. 5 , %s >. e. %s ) )' % (pa, BRF, G5, S_, G7, S_))
    jc = w.s([sS, d1a], 'jca', '( %s -> ( %s e. ( 2nd ` T ) /\\ %s e. %s ) )' % (pa, s_, D1, STK))
    R5 = '( <. 5 , %s >. %s <. %s , %s >. )' % (G5, SA, s_, D1)
    R7 = '( <. 5 , %s >. %s <. %s , %s >. )' % (G7, SA, s_, D1)
    Fs = '( %s ` %s )' % (BRF, s_)
    e2 = w.s([tva, jb, jc, w.inst('tm2sabr')], 'syl3anc', '( %s -> ( %s %s <. %s , %s >. ) = if ( %s = 1o , %s , %s ) )' % (pa, BR, SA, s_, D1, Fs, R5, R7))
    # value of the handler
    fx = w.s([], 'ifexd' if False else 'fvexd', '') if False else None
    ifx = w.s([w.s([], 'ifex', 'if ( ( TMcmp ` %s ) = 2o , (/) , 1o ) e. _V' % s_)], 'a1i', '( %s -> if ( ( TMcmp ` %s ) = 2o , (/) , 1o ) e. _V )' % (pa, s_))
    fv, _ = fvm(w, pa, BRF, None, 'u', 'TMSt', 'if ( ( TMcmp ` u ) = 2o , (/) , 1o )', s_, sT, ifx)
    n16 = sub(X.d(num.nn0(w, 16), '; 1 6 e. NN0'), '; 1 6 e. NN0')
    nna = sub(X.misc_nn, 'N e. NN0')
    gt = w.s([n16, nna, w.inst('ncmpgt')], 'syl2anc', '( %s -> ( ( ; 1 6 Ncmp N ) = 2o <-> N < ; 1 6 ) )' % pa)
    Gl = G5 if big else G7
    if big:
        le = sub(X.misc_le, '; 1 6 <_ N')
        n16r = sub(X.d(num.re_nat(w, 16), '; 1 6 e. RR'), '; 1 6 e. RR')
        nr = w.s([nna], 'nn0red', '( %s -> N e. RR )' % pa)
        nlt = w.s([n16r, nr, le], 'lenltd' if False else 'lenltd', '') if False else None
        lnl = w.s([n16r, nr, w.inst('lenlt')], 'syl2anc', '( %s -> ( ; 1 6 <_ N <-> -. N < ; 1 6 ) )' % pa)
        nlt = w.s([le, lnl], 'mpbid', '( %s -> -. N < ; 1 6 )' % pa)
        ng = w.s([nlt, gt], 'mtbird', '( %s -> -. ( ; 1 6 Ncmp N ) = 2o )' % pa)
        cq = w.s([cmv], 'eqeq1d', '( %s -> ( ( TMcmp ` %s ) = 2o <-> ( ; 1 6 Ncmp N ) = 2o ) )' % (pa, s_))
        ncq = w.s([ng, cq], 'mtbird', '( %s -> -. ( TMcmp ` %s ) = 2o )' % (pa, s_))
        iv = w.s([ncq], 'iffalsed', '( %s -> if ( ( TMcmp ` %s ) = 2o , (/) , 1o ) = 1o )' % (pa, s_))
        f1 = w.s([fv, iv], 'eqtrd', '( %s -> %s = 1o )' % (pa, Fs))
        e3 = w.s([f1], 'iftrued', '( %s -> if ( %s = 1o , %s , %s ) = %s )' % (pa, Fs, R5, R7, R5))
        Rg, cg = R5, sub(c5, '%s e. ( %s ^m ( 2nd ` T ) )' % (G5, L_))
    else:
        lt = sub(X.misc_le, 'N < ; 1 6')
        g2 = w.s([lt, gt], 'mpbird', '( %s -> ( ; 1 6 Ncmp N ) = 2o )' % pa)
        cq = w.s([cmv, g2], 'eqtrd', '( %s -> ( TMcmp ` %s ) = 2o )' % (pa, s_))
        iv = w.s([cq], 'iftrued', '( %s -> if ( ( TMcmp ` %s ) = 2o , (/) , 1o ) = (/) )' % (pa, s_))
        f0 = w.s([fv, iv], 'eqtrd', '( %s -> %s = (/) )' % (pa, Fs))
        n1 = w.s([w.s([], '1n0', '1o =/= (/)')], 'a1i', '( %s -> 1o =/= (/) )' % pa)
        n2 = w.s([n1], 'necomd', '( %s -> (/) =/= 1o )' % pa)
        f1 = w.s([f0, n2], 'eqnetrd', '( %s -> %s =/= 1o )' % (pa, Fs))
        f1n = w.s([f1], 'neneqd', '( %s -> -. %s = 1o )' % (pa, Fs))
        e3 = w.s([f1n], 'iffalsed', '( %s -> if ( %s = 1o , %s , %s ) = %s )' % (pa, Fs, R5, R7, R7))
        Rg, cg = R7, sub(c7, '%s e. ( %s ^m ( 2nd ` T ) )' % (G7, L_))
    e4 = w.s([tva, cg, jc, w.inst('tm2sagoto')], 'syl3anc', '( %s -> %s = <. ( inl ` ( %s ` %s ) ) , <. %s , %s >. >. )' % (pa, Rg, Gl, s_, s_, D1))
    tl = sub(labs[tgt], '%s e. %s' % (tgt, L_))
    e5 = w.s([tl, sS, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (pa, Gl, s_, tgt))
    e6 = w.s([e5], 'fveq2d', '( %s -> ( inl ` ( %s ` %s ) ) = ( inl ` %s ) )' % (pa, Gl, s_, tgt))
    e7 = w.s([e6], 'opeq1d', '( %s -> <. ( inl ` ( %s ` %s ) ) , <. %s , %s >. >. = <. ( inl ` %s ) , <. %s , %s >. >. )' % (pa, Gl, s_, s_, D1, tgt, s_, D1))
    V = '<. ( inl ` %s ) , <. %s , %s >. >.' % (tgt, s_, D1)
    ev = w.s([e1, e2, e3], '3eqtrd', '( %s -> ( ( M ` ( P ` 4 ) ) %s a ) = %s )' % (pa, SA, Rg))
    ev2 = w.s([ev, e4, e7], '3eqtrd', '( %s -> ( ( M ` ( P ` 4 ) ) %s a ) = %s )' % (pa, SA, V))
    i1 = w.s([w.s([], 'fvexd', '( %s -> ( inl ` %s ) e. _V )' % (pa, tgt)), w.inst('snidg')], 'syl', '( %s -> ( inl ` %s ) e. { ( inl ` %s ) } )' % (pa, tgt, tgt))
    i2 = w.s([d1a, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (pa, D1, D1))
    i3 = w.s([s1, i2, w.inst('opelxpi')], 'syl2anc', '( %s -> <. %s , %s >. e. %s )' % (pa, s_, D1, Pc))
    i4 = w.s([i1, i3, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. %s )' % (pa, V, Dc))
    mem = w.s([ev2, i4], 'eqeltrd', '( %s -> ( ( M ` ( P ` 4 ) ) %s a ) e. %s )' % (pa, SA, Dc))
    ra = X.s([mem], 'ralrimiva', 'A. a e. %s ( ( M ` ( P ` 4 ) ) %s a ) e. %s' % (Pc, SA, Dc))
    L = {'( T e. V /\\ M : %s --> %s )' % (L_, S_): X.tvm, '( P ` 4 ) e. %s' % L_: labs['( P ` 4 )'],
         '%s C_ ( ( 2nd ` T ) X. %s )' % (Pc, STK): pcs, '%s C_ ( TM2Cfg ` T )' % Dc: dcs,
         'A. a e. %s ( ( M ` ( P ` 4 ) ) %s a ) e. %s' % (Pc, SA, Dc): ra}
    return use(w, ph, 'tm2hstep', {'A': '( P ` 4 )', 'P': Pc, 'D': Dc}, L)


def grow_s(X, t, f):
    """replace the post class CL( A , D , H16 ) of a triple by CL( A , D ) (state class TMSt)"""
    w = X.w
    C, Pp, N = parse_tri(f)
    Pn = Pp.replace(H16, '( 2nd ` T )')
    t_ = Pp.split()
    # Pp = ( { ( inl ` A ) } X. ( H16 X. { D } ) )
    inner = Pp[len('( { ( inl ` '):]
    A = Pp[len('( { ( inl ` '):Pp.index(' ) } X. ( ')]
    D = Pp[Pp.index(' X. { ', len('( { ( inl ` ') + len(A) + 10) + 6:-6]
    hsT = X.d(X.c('%s C_ TMSt' % H16, 'ssrab2'), '%s C_ TMSt' % H16)
    hsS = X.s([hsT, X.ts], 'sseqtrrd', '%s C_ ( 2nd ` T )' % H16)
    a = X.s([hsS, w.inst('xpss1')], 'syl', '( %s X. { %s } ) C_ ( ( 2nd ` T ) X. { %s } )' % (H16, D, D))
    b = X.s([a, w.inst('xpss2')], 'syl', '%s C_ %s' % (Pp, Pn))
    return a, b, Pn, A, D


def prefix_ctx(w, ph, big):
    X = Pre(w, ph)
    cx = X.s([], 'simplll', CTX)
    X.ctx(cx)
    root = X.s([], 'simpllr', 'TMIroot C K T M P E')
    nn = X.s([], 'simplr', 'N e. NN0')
    X.misc_nn = nn
    X.misc_le = X.s([], 'simpr', '; 1 6 <_ N' if big else 'N < ; 1 6')
    pc = unfold(w, ph, 'TMIroot', {}, root)
    labs = {}
    for l in ('( P ` 4 )', '( P ` 5 )', '( P ` 6 )', '( P ` 9 )'):
        labs[l] = pc['%s e. %s' % (l, L_)]
    fal = unfold(w, ph, 'TMIfal', {'P': '( P ` 7 )', 'E': '( P ` 9 )'}, pc['TMIfal T M ( P ` 7 ) ( P ` 9 )'])
    labs['( ( P ` 7 ) ` 0 )'] = fal['( ( P ` 7 ) ` 0 ) e. %s' % L_]
    pre = X.s([], 'simpl', '( ( %s /\\ TMIroot C K T M P E ) /\\ N e. NN0 )' % CTX)
    t0, f0 = use(w, ph, 't15pre1', {}, {'( ( %s /\\ TMIroot C K T M P E ) /\\ N e. NN0 )' % CTX: pre})
    D1 = INIT('7', '( %s ++ <" 4 "> )' % X0)
    x0g = X.s([nn, w.inst('encnatgamcl')], 'syl', "%s e. Word Gamma'" % X0)
    g4 = X.d(X.c("<\" 4 \"> e. Word Gamma'", 'ax-mp', [X.c("4 e. Gamma'", 'gamma4'), w.inst('s1cl')]), "<\" 4 \"> e. Word Gamma'")
    x4g = X.s([x0g, g4, w.inst('ccatcl')], 'syl2anc', "( %s ++ <\" 4 \"> ) e. Word Gamma'" % X0)
    d1s = X.initstk('7', '( %s ++ <" 4 "> )' % X0, x4g)
    tb, fb = branch(X, pc, D1, d1s, big, labs)
    t01, f01 = seq(X, t0, f0, tb, fb)
    return X, pc, labs, D1, d1s, x0g, g4, x4g, t01, f01


def growt(X, t, f):
    """triple with post CL( A , D , H16 ) -> post CL( A , D )"""
    w = X.w
    a, b, Pn, A, D = grow_s(X, t, f)
    C, Pp, N = parse_tri(f)
    ds = X.s([X.misc_d1s], 'snssd', '{ %s } C_ %s' % (D, STK))
    ss = X.s([X.s([], 'ssidd', '( 2nd ` T ) C_ ( 2nd ` T )'), ds, w.inst('xpss12')], 'syl2anc', '( ( 2nd ` T ) X. { %s } ) C_ ( ( 2nd ` T ) X. %s )' % (D, STK))
    cf = X.s([X.tv, X.labs_[A], ss, w.inst('tm2hcfgss')], 'syl3anc', '%s C_ ( TM2Cfg ` T )' % Pn)
    j2 = X.s([X.tvm, t], 'jca', '( ( T e. V /\\ M : %s --> %s ) /\\ %s )' % (L_, S_, f))
    j3 = X.s([b, cf], 'jca', '( %s C_ %s /\\ %s C_ ( TM2Cfg ` T ) )' % (Pp, Pn, Pn))
    f2 = TRI(C, Pn, N)
    return X.s([j2, j3, w.inst('tm2hssd')], 'syl2anc', f2), f2


def t15preb():
    w = W('t15preb', 'The prefix of route beta for an input n >= 16: the machine reaches the entry of the search with the initial stacks restored.')
    ph = '( ( ( %s /\\ TMIroot C K T M P E ) /\\ N e. NN0 ) /\\ ; 1 6 <_ N )' % CTX
    X, pc, labs, D1, d1s, x0g, g4, x4g, t01, f01 = prefix_ctx(w, ph, True)
    X.misc_d1s = d1s; X.labs_ = labs
    t01g, f01g = growt(X, t01, f01)
    nn = X.misc_nn
    # mv1: 7 -> 2 until the comma
    ev = X.s([nn, w.inst('encnatgamval')], 'syl', '%s = ( inclBool o. ( encodeNat ` N ) )' % X0)
    enc = X.s([nn, w.inst('encnatcl')], 'syl', '( encodeNat ` N ) e. Word 2o')
    icl = X.d(X.c('inclBool : 2o --> ( { 1 } X. 2o )', 'tmcinclf'), 'inclBool : 2o --> ( { 1 } X. 2o )')
    ico = X.s([enc, icl, w.inst('wrdco')], 'syl2anc', '( inclBool o. ( encodeNat ` N ) ) e. Word ( { 1 } X. 2o )')
    x0b = X.s([ev, ico], 'eqeltrd', '%s e. Word ( { 1 } X. 2o )' % X0)
    w0 = X.d(X.c("(/) e. Word Gamma'", 'wrd0'), "(/) e. Word Gamma'")
    X4 = '( %s ++ <" 4 "> )' % X0
    d17, _ = X.initval('7', X4, '7')
    r4 = X.d(X.c('( <" 4 "> ++ (/) ) = <" 4 ">', 'ax-mp', [X.c("<\" 4 \"> e. Word Gamma'", 'ax-mp', [X.c("4 e. Gamma'", 'gamma4'), w.inst('s1cl')]), w.inst('ccatrid')]), '( <" 4 "> ++ (/) ) = <" 4 ">')
    r4b = X.s([r4], 'oveq2d', '( %s ++ ( <" 4 "> ++ (/) ) ) = %s' % (X0, X4))
    d17b = X.s([d17, r4b], 'eqtr4d', '( %s ` 7 ) = ( %s ++ ( <" 4 "> ++ (/) ) )' % (D1, X0))
    MV1 = pc_stmt(pc, '( P ` 5 )')
    MV2 = pc_stmt(pc, '( P ` 6 )')
    L = {'( ( T e. V /\\ M : %s --> %s ) /\\ ( %s = TMGam /\\ ( 2nd ` T ) = TMSt ) )' % (L_, S_, G1): X.cx,
         '( M ` ( P ` 5 ) ) = %s' % MV1: pc['( M ` ( P ` 5 ) ) = %s' % MV1],
         '( M ` ( P ` 6 ) ) = %s' % MV2: pc['( M ` ( P ` 6 ) ) = %s' % MV2],
         '( P ` 5 ) e. %s' % L_: labs['( P ` 5 )'], '( P ` 6 ) e. %s' % L_: labs['( P ` 6 )'],
         '7 e. ( 0 ..^ 8 )': X.stk8('7'), '2 e. ( 0 ..^ 8 )': X.stk8('2'), '0 e. ( 0 ..^ 8 )': X.stk8('0'),
         '7 =/= 2': X.ned('7', '2'), '2 =/= 0': X.ned('2', '0'),
         '%s e. Word ( { 1 } X. 2o )' % X0: x0b, "(/) e. Word Gamma'": w0, '%s e. %s' % (D1, STK): d1s,
         '( %s ` 7 ) = ( %s ++ ( <" 4 "> ++ (/) ) )' % (D1, X0): d17b}
    t2, f2 = use(w, ph, 'tmimvt', {'K': '7', 'J': '2', 'A': '( P ` 5 )', 'E': '( P ` 6 )', 'W': X0, 'X': '(/)', 'D': D1}, L)
    D5a = UPD(D1, '7', '(/)')
    Y5 = '( ( reverse ` %s ) ++ ( %s ` 2 ) )' % (X0, D1)
    D5 = UPD(D5a, '2', Y5)
    d5as = X.updstk(D1, d1s, '7', '(/)', w0)
    rvg = X.s([x0g, w.inst('revcl')], 'syl', "( reverse ` %s ) e. Word Gamma'" % X0)
    d12, _ = X.initval('7', X4, '2')
    d12g = X.s([d12, w0], 'eqeltrd', "( %s ` 2 ) e. Word Gamma'" % D1)
    y5g = X.s([rvg, d12g, w.inst('ccatcl')], 'syl2anc', "%s e. Word Gamma'" % Y5)
    d5s = X.updstk(D5a, d5as, '2', Y5, y5g)
    # mv2: 2 -> 0 until empty
    srch = unfold(w, ph, 'TMIsrch', {'P': '( P ` 8 )', 'E': '( P ` 9 )'}, pc['TMIsrch C K T M ( P ` 8 ) ( P ` 9 )'])
    inpk = [k for k in srch if k.startswith('TMIinp T M ( ( P ` 8 ) ` 4 )')][0]
    inp = unfold(w, ph, 'TMIinp', {'P': '( ( P ` 8 ) ` 4 )', 'E': inpk.split('( ( P ` 8 ) ` 4 ) ', 1)[1]}, srch[inpk])
    EN = '( ( ( P ` 8 ) ` 4 ) ` 0 )'
    L['%s e. %s' % (EN, L_)] = inp['%s e. %s' % (EN, L_)]
    RX = '( reverse ` %s )' % X0
    L['%s e. Word ( { 1 } X. 2o )' % RX] = X.s([x0b, w.inst('revcl')], 'syl', '%s e. Word ( { 1 } X. 2o )' % RX)
    L['%s e. %s' % (D5, STK)] = d5s
    d52, _ = X.updval(D5a, d5as, '2', Y5, '2')
    rr = X.s([d12], 'oveq2d', '%s = ( %s ++ (/) )' % (Y5, RX))
    rz = X.s([rvg, w.inst('ccatrid')], 'syl', '( %s ++ (/) ) = %s' % (RX, RX))
    L['( %s ` 2 ) = %s' % (D5, RX)] = X.s([d52, rr, rz], '3eqtrd', '( %s ` 2 ) = %s' % (D5, RX))
    t3, f3 = use(w, ph, 'tmimvr', {'K': '2', 'J': '0', 'A': '( P ` 6 )', 'E': EN, 'W': RX, 'D': D5}, L)
    Y6 = '( ( reverse ` %s ) ++ ( %s ` 0 ) )' % (RX, D5)
    D6a = UPD(D5, '2', '(/)')
    D6 = UPD(D6a, '0', Y6)
    ta, fa = seq(X, t01g, f01g, t2, f2)
    tb, fb = seq(X, ta, fa, t3, f3)
    # D6 = D0
    D0 = INIT('0', X0)
    d6as = X.updstk(D5, d5s, '2', '(/)', w0)
    d50, _ = X.updval(D5a, d5as, '2', Y5, '0', lambda j: X.updval(D1, d1s, '7', '(/)', j, lambda jj: X.initval('7', X4, jj)))
    rr2 = X.s([X.s([x0g, w.inst('revrev')], 'syl', '( reverse ` %s ) = %s' % (RX, X0)), d50], 'oveq12d', '%s = ( %s ++ (/) )' % (Y6, X0))
    rz2 = X.s([x0g, w.inst('ccatrid')], 'syl', '( %s ++ (/) ) = %s' % (X0, X0))
    y6 = X.s([rr2, rz2], 'eqtrd', '%s = %s' % (Y6, X0))
    y6g = X.s([y6, x0g], 'eqeltrd', "%s e. Word Gamma'" % Y6)
    d6s = X.updstk(D6a, d6as, '0', Y6, y6g)
    vals = []
    for j in '01234567':
        if j == '0':
            a0, _ = X.updval(D6a, d6as, '0', Y6, '0')
            a = X.s([a0, y6], 'eqtrd', '( %s ` 0 ) = %s' % (D6, X0)); va = X0
        else:
            def dv5(jj):
                return X.updval(D5a, d5as, '2', Y5, jj, lambda j2: X.updval(D1, d1s, '7', '(/)', j2, lambda j3: X.initval('7', X4, j3)))
            a, va = X.updval(D6a, d6as, '0', Y6, j, lambda jj: X.updval(D5, d5s, '2', '(/)', jj, dv5))
        b, vb = X.initval('0', X0, j)
        assert va == vb, (j, va, vb)
        vals.append(X.s([a, b], 'eqtr4d', '( %s ` %s ) = ( %s ` %s )' % (D6, j, D0, j)))
    d0s = X.initstk('0', X0, x0g)
    L2 = {'( T e. V /\\ %s = TMGam )' % G1: X.s([X.tv, X.tg], 'jca', '( T e. V /\\ %s = TMGam )' % G1),
          '%s e. %s' % (D6, STK): d6s, '%s e. %s' % (D0, STK): d0s}
    for j, st in zip('01234567', vals):
        L2['( %s ` %s ) = ( %s ` %s )' % (D6, j, D0, j)] = st
    deq, _ = use(w, ph, 't12stkeq', {'A': D6, 'B': D0}, L2)
    C, Pp, N = parse_tri(fb)
    peq, Pn = cong(w, Pp, {}, ph, {}, rules={D6: (D0, deq)})
    tc, fc = transport(X, tb, fb, peq, Pn)
    # bound
    Bb = '( ( 7 x. %s ) + ; 7 0 )' % Z
    C, Pp, N = parse_tri(fc)
    zn = X.s([enc, w.inst('lencl')], 'syl', '%s e. NN0' % Z)
    zr = X.s([zn], 'nn0red', '%s e. RR' % Z)
    z0 = X.s([zn], 'nn0ge0d', '0 <_ %s' % Z)
    xl = X.s([nn, w.inst('encnatgamlen')], 'syl', '( # ` %s ) = %s' % (X0, Z))
    rl = X.s([x0g, w.inst('revlen')], 'syl', '( # ` %s ) = ( # ` %s )' % (RX, X0))
    x0r = X.s([X.s([x0g, w.inst('lencl')], 'syl', '( # ` %s ) e. NN0' % X0)], 'nn0red', '( # ` %s ) e. RR' % X0)
    rxr = X.s([X.s([rvg, w.inst('lencl')], 'syl', '( # ` %s ) e. NN0' % RX)], 'nn0red', '( # ` %s ) e. RR' % RX)
    le = linarith(w, ph, [xl, rl, z0], '%s <_ %s' % (N, Bb), leaves={Z: zr, '( # ` %s )' % X0: x0r, '( # ` %s )' % RX: rxr})
    bn = X.s([X.s([X.d(num.nn0(w, 7), '7 e. NN0'), zn], 'nn0mulcld', '( 7 x. %s ) e. NN0' % Z), X.d(num.nn0(w, 70), '; 7 0 e. NN0')], 'nn0addcld', '%s e. NN0' % Bb)
    j3 = X.s([bn, le], 'jca', '( %s e. NN0 /\\ %s <_ %s )' % (Bb, N, Bb))
    j4 = X.s([X.tvm, tc], 'jca', '( ( T e. V /\\ M : %s --> %s ) /\\ %s )' % (L_, S_, fc))
    w.qed([j4, j3, w.inst('tm2hle')], 'syl2anc', '( %s -> %s )' % (ph, TRI(C, Pp, Bb)))
    return w


def pc_stmt(pc, lab):
    for k in pc:
        if k.startswith('( M ` %s ) = ' % lab):
            return k[len('( M ` %s ) = ' % lab):]
    raise KeyError(lab)


def t15pres():
    w = W('t15pres', 'The prefix of route beta for an input n < 16: the machine answers <. 0 , (/) >. (failAll) and reaches the exit.')
    ph = '( ( ( %s /\\ TMIroot C K T M P E ) /\\ N e. NN0 ) /\\ N < ; 1 6 )' % CTX
    X, pc, labs, D1, d1s, x0g, g4, x4g, t01, f01 = prefix_ctx(w, ph, False)
    X.misc_d1s = d1s; X.labs_ = labs
    t01g, f01g = growt(X, t01, f01)
    nn = X.misc_nn
    L = {CTX: X.cx, 'TMIfal T M ( P ` 7 ) ( P ` 9 )': pc['TMIfal T M ( P ` 7 ) ( P ` 9 )'], '%s e. %s' % (D1, STK): d1s}
    t2, f2 = use(w, ph, 'tmifal', {'P': '( P ` 7 )', 'E': '( P ` 9 )', 'D': D1}, L)
    tb, fb = seq(X, t01g, f01g, t2, f2)
    C, Pp, N = parse_tri(fb)
    Bb = '( ( 7 x. %s ) + ; 7 0 )' % Z
    X4 = '( %s ++ <" 4 "> )' % X0
    enc = X.s([nn, w.inst('encnatcl')], 'syl', '( encodeNat ` N ) e. Word 2o')
    zn = X.s([enc, w.inst('lencl')], 'syl', '%s e. NN0' % Z)
    zr = X.s([zn], 'nn0red', '%s e. RR' % Z)
    z0 = X.s([zn], 'nn0ge0d', '0 <_ %s' % Z)
    hyps = [z0]
    leaves = {Z: zr}
    h0 = X.d(X.c('( # ` (/) ) = 0', 'hash0'), '( # ` (/) ) = 0')
    for j in '01234567':
        v, val = X.initval('7', X4, j)
        a = X.s([v], 'fveq2d', '( # ` ( %s ` %s ) ) = ( # ` %s )' % (D1, j, val))
        if val == '(/)':
            b = X.s([a, h0], 'eqtrd', '( # ` ( %s ` %s ) ) = 0' % (D1, j))
        else:
            l1 = X.s([x0g, w.inst('ccatws1len')], 'syl', '( # ` %s ) = ( ( # ` %s ) + 1 )' % (X4, X0))
            l2 = X.s([nn, w.inst('encnatgamlen')], 'syl', '( # ` %s ) = %s' % (X0, Z))
            l3 = X.s([l2], 'oveq1d', '( ( # ` %s ) + 1 ) = ( %s + 1 )' % (X0, Z))
            b = X.s([a, l1, l3], '3eqtrd', '( # ` ( %s ` %s ) ) = ( %s + 1 )' % (D1, j, Z))
        hyps.append(b)
        dj = X.s([X.tv, d1s, X.kdom(j)[0], w.inst('tm2stkfv')], 'syl3anc', '( %s ` %s ) e. Word ( %s ` %s )' % (D1, j, G1, j))
        ln = X.s([dj, w.inst('lencl')], 'syl', '( # ` ( %s ` %s ) ) e. NN0' % (D1, j))
        leaves['( # ` ( %s ` %s ) )' % (D1, j)] = X.s([ln], 'nn0red', '( # ` ( %s ` %s ) ) e. RR' % (D1, j))
    le = linarith(w, ph, hyps, '%s <_ %s' % (N, Bb), leaves=leaves)
    bn = X.s([X.s([X.d(num.nn0(w, 7), '7 e. NN0'), zn], 'nn0mulcld', '( 7 x. %s ) e. NN0' % Z), X.d(num.nn0(w, 70), '; 7 0 e. NN0')], 'nn0addcld', '%s e. NN0' % Bb)
    j3 = X.s([bn, le], 'jca', '( %s e. NN0 /\\ %s <_ %s )' % (Bb, N, Bb))
    j4 = X.s([X.tvm, tb], 'jca', '( ( T e. V /\\ M : %s --> %s ) /\\ %s )' % (L_, S_, fb))
    w.qed([j4, j3, w.inst('tm2hle')], 'syl2anc', '( %s -> %s )' % (ph, TRI(C, Pp, Bb)))
    return w


S0 = '<. (/) , <. ( inr ` (/) ) , <. ( inr ` (/) ) , <. (/) , <. (/) , <. (/) , (/) >. >. >. >. >. >.'


def t15halt():
    w = W('t15halt', 'The exit of the whole program: load the initial state and halt, in one step.')
    ph = '( ( %s /\\ TMIroot C K T M P E ) /\\ D e. %s )' % (CTX, STK)
    X = Pre(w, ph)
    cx = X.s([], 'simpll', CTX)
    X.ctx(cx)
    root = X.s([], 'simplr', 'TMIroot C K T M P E')
    dd = X.s([], 'simpr', 'D e. %s' % STK)
    pc = unfold(w, ph, 'TMIroot', {}, root)
    FIN = pc_stmt(pc, '( P ` 9 )')
    import t15_e_kind
    k = t15_e_kind.Kind.__new__(t15_e_kind.Kind); k.w = w; k.memo = {}
    s0t = k.closed_st(S0)
    s0s = X.s([X.d(s0t, '%s e. TMSt' % S0), X.ts], 'eleqtrrd', '%s e. ( 2nd ` T )' % S0)
    Pc = '( ( 2nd ` T ) X. { D } )'
    Pd = '( { %s } X. { D } )' % S0
    Dc = '( { ( inr ` (/) ) } X. %s )' % Pd
    ds = X.s([dd], 'snssd', '{ D } C_ %s' % STK)
    pcs = X.s([X.s([], 'ssidd', '( 2nd ` T ) C_ ( 2nd ` T )'), ds, w.inst('xpss12')], 'syl2anc', '%s C_ ( ( 2nd ` T ) X. %s )' % (Pc, STK))
    pds = X.s([X.s([s0s], 'snssd', '{ %s } C_ ( 2nd ` T )' % S0), ds, w.inst('xpss12')], 'syl2anc', '%s C_ ( ( 2nd ` T ) X. %s )' % (Pd, STK))
    dcs = X.s([X.tv, pds, w.inst('tm2hcfgsr')], 'syl2anc', '%s C_ ( TM2Cfg ` T )' % Dc)
    FF = '( ( 2nd ` T ) X. { %s } )' % S0
    sx = X.s([], 'fvexd', '( 2nd ` T ) e. _V')
    fty = X.s([X.s([sx, s0s], 'jca', '( ( 2nd ` T ) e. _V /\\ %s e. ( 2nd ` T ) )' % S0), w.inst('t15cst')], 'syl', '%s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) )' % FF)
    hq = X.s([X.tv, w.inst('tm2halt')], 'syl', '<. 6 , (/) >. e. %s' % S_)
    pa = '( %s /\\ a e. %s )' % (ph, Pc)
    sub = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (pa, f))
    am = w.s([], 'simpr', '( %s -> a e. %s )' % (pa, Pc))
    s1 = w.s([am, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` a ) e. ( 2nd ` T ) )' % pa)
    s2 = w.s([w.s([am, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` a ) e. { D } )' % pa), w.inst('elsni')], 'syl', '( %s -> ( 2nd ` a ) = D )' % pa)
    ae = w.s([am, w.inst('1st2nd2')], 'syl', '( %s -> a = <. ( 1st ` a ) , ( 2nd ` a ) >. )' % pa)
    a2 = w.s([ae, w.s([s2], 'opeq2d', '( %s -> <. ( 1st ` a ) , ( 2nd ` a ) >. = <. ( 1st ` a ) , D >. )' % pa)], 'eqtrd', '( %s -> a = <. ( 1st ` a ) , D >. )' % pa)
    SA = '( TM2sa ` T )'
    mf = sub(pc['( M ` ( P ` 9 ) ) = %s' % FIN], '( M ` ( P ` 9 ) ) = %s' % FIN)
    e1 = w.s([mf, a2], 'oveq12d', '( %s -> ( ( M ` ( P ` 9 ) ) %s a ) = ( %s %s <. ( 1st ` a ) , D >. ) )' % (pa, SA, FIN, SA))
    tva = sub(X.tv, 'T e. V')
    j1 = w.s([sub(fty, '%s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) )' % FF), sub(hq, '<. 6 , (/) >. e. %s' % S_)], 'jca', '( %s -> ( %s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) /\\ <. 6 , (/) >. e. %s ) )' % (pa, FF, S_))
    j2 = w.s([s1, sub(dd, 'D e. %s' % STK)], 'jca', '( %s -> ( ( 1st ` a ) e. ( 2nd ` T ) /\\ D e. %s ) )' % (pa, STK))
    e2 = w.s([tva, j1, j2, w.inst('tm2saload')], 'syl3anc', '( %s -> ( %s %s <. ( 1st ` a ) , D >. ) = ( <. 6 , (/) >. %s <. ( %s ` ( 1st ` a ) ) , D >. ) )' % (pa, FIN, SA, SA, FF))
    e3 = w.s([w.s([w.s([], 'opex', '%s e. _V' % S0)], 'a1i', '( %s -> %s e. _V )' % (pa, S0)), s1, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` ( 1st ` a ) ) = %s )' % (pa, FF, S0))
    e4 = w.s([e3], 'opeq1d', '( %s -> <. ( %s ` ( 1st ` a ) ) , D >. = <. %s , D >. )' % (pa, FF, S0))
    e5 = w.s([e4], 'oveq2d', '( %s -> ( <. 6 , (/) >. %s <. ( %s ` ( 1st ` a ) ) , D >. ) = ( <. 6 , (/) >. %s <. %s , D >. ) )' % (pa, SA, FF, SA, S0))
    j3 = w.s([sub(s0s, '%s e. ( 2nd ` T )' % S0), sub(dd, 'D e. %s' % STK)], 'jca', '( %s -> ( %s e. ( 2nd ` T ) /\\ D e. %s ) )' % (pa, S0, STK))
    e6 = w.s([tva, j3, w.inst('tm2sahalt')], 'syl2anc', '( %s -> ( <. 6 , (/) >. %s <. %s , D >. ) = <. ( inr ` (/) ) , <. %s , D >. >. )' % (pa, SA, S0, S0))
    V = '<. ( inr ` (/) ) , <. %s , D >. >.' % S0
    ev = w.s([e1, e2, e5], '3eqtrd', '( %s -> ( ( M ` ( P ` 9 ) ) %s a ) = ( <. 6 , (/) >. %s <. %s , D >. ) )' % (pa, SA, SA, S0))
    ev2 = w.s([ev, e6], 'eqtrd', '( %s -> ( ( M ` ( P ` 9 ) ) %s a ) = %s )' % (pa, SA, V))
    i1 = w.s([w.s([], 'fvexd', '( %s -> ( inr ` (/) ) e. _V )' % pa), w.inst('snidg')], 'syl', '( %s -> ( inr ` (/) ) e. { ( inr ` (/) ) } )' % pa)
    i2 = w.s([w.s([w.s([], 'opex', '%s e. _V' % S0)], 'a1i', '( %s -> %s e. _V )' % (pa, S0)), w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (pa, S0, S0))
    i3 = w.s([sub(dd, 'D e. %s' % STK), w.inst('snidg')], 'syl', '( %s -> D e. { D } )' % pa)
    i4 = w.s([i2, i3, w.inst('opelxpi')], 'syl2anc', '( %s -> <. %s , D >. e. %s )' % (pa, S0, Pd))
    i5 = w.s([i1, i4, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. %s )' % (pa, V, Dc))
    mem = w.s([ev2, i5], 'eqeltrd', '( %s -> ( ( M ` ( P ` 9 ) ) %s a ) e. %s )' % (pa, SA, Dc))
    ra = X.s([mem], 'ralrimiva', 'A. a e. %s ( ( M ` ( P ` 9 ) ) %s a ) e. %s' % (Pc, SA, Dc))
    L = {'( T e. V /\\ M : %s --> %s )' % (L_, S_): X.tvm, '( P ` 9 ) e. %s' % L_: pc['( P ` 9 ) e. %s' % L_],
         '%s C_ ( ( 2nd ` T ) X. %s )' % (Pc, STK): pcs, '%s C_ ( TM2Cfg ` T )' % Dc: dcs,
         'A. a e. %s ( ( M ` ( P ` 9 ) ) %s a ) e. %s' % (Pc, SA, Dc): ra}
    st, f = use(w, ph, 'tm2hstep', {'A': '( P ` 9 )', 'P': Pc, 'D': Dc}, L)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w

if __name__ == '__main__':
    import sys as _s
    for lab in _s.argv[1:]:
        globals()[lab]().run()
