"""Sortie C6b, part 2: the frame bound (bddun, bddseg, holfrmbd)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *


def BD(X, m, u='u'):
    return 'A. %s e. %s ( abs ` ( F ` %s ) ) <_ %s' % (u, X, u, m)


def bdut(w, X, m, u='u', t='t'):
    """( BD(X,m,u) <-> BD(X,m,t) )"""
    s = w.s([w.s([w.s([], 'fveq2', '( %s = %s -> ( F ` %s ) = ( F ` %s ) )' % (u, t, u, t))], 'fveq2d', '( %s = %s -> ( abs ` ( F ` %s ) ) = ( abs ` ( F ` %s ) ) )' % (u, t, u, t))], 'breq1d',
             '( %s = %s -> ( ( abs ` ( F ` %s ) ) <_ %s <-> ( abs ` ( F ` %s ) ) <_ %s ) )' % (u, t, u, m, t, m))
    return w.s([s], 'cbvralvw', '( %s <-> %s )' % (BD(X, m, u), BD(X, m, t)))


def bdrename(w, X, a, b):
    """( E. a e. RR BD(X,a,u) <-> E. b e. RR BD(X,b,t) )"""
    r1 = w.s([bdut(w, X, a)], 'rexbii', '( E. %s e. RR %s <-> E. %s e. RR %s )' % (a, BD(X, a), a, BD(X, a, 't')))
    s = w.s([w.s([], 'breq2', '( %s = %s -> ( ( abs ` ( F ` t ) ) <_ %s <-> ( abs ` ( F ` t ) ) <_ %s ) )' % (a, b, a, b))], 'ralbidv',
             '( %s = %s -> ( %s <-> %s ) )' % (a, b, BD(X, a, 't'), BD(X, b, 't')))
    r2 = w.s([s], 'cbvrexvw', '( E. %s e. RR %s <-> E. %s e. RR %s )' % (a, BD(X, a, 't'), b, BD(X, b, 't')))
    return w.s([r1, r2], 'bitri', '( E. %s e. RR %s <-> E. %s e. RR %s )' % (a, BD(X, a), b, BD(X, b, 't')))


if __name__ == '__main__':
    # ---- bddun --------------------------------------------------------------------
    w = W('bddun', 'A function bounded on two subsets of its domain is bounded on their union.')
    TY = '( F : D --> CC /\\ X C_ D /\\ Y C_ D )'
    A0 = '( %s /\\ ( E. m e. RR %s /\\ E. m e. RR %s ) )' % (TY, BD('X', 'm'), BD('Y', 'm'))
    ty = w.s([], 'simpl', '( %s -> %s )' % (A0, TY))
    ex2 = w.s([], 'simpr', '( %s -> ( E. m e. RR %s /\\ E. m e. RR %s ) )' % (A0, BD('X', 'm'), BD('Y', 'm')))
    ra = bdrename(w, 'X', 'm', 'a'); rb = bdrename(w, 'Y', 'm', 'b')
    BXA = BD('X', 'a', 't'); BYB = BD('Y', 'b', 't')
    exab = w.s([ex2, w.s([ra, rb], 'anbi12i', '( ( E. m e. RR %s /\\ E. m e. RR %s ) <-> ( E. a e. RR %s /\\ E. b e. RR %s ) )' % (BD('X', 'm'), BD('Y', 'm'), BXA, BYB))], 'sylib',
              '( %s -> ( E. a e. RR %s /\\ E. b e. RR %s ) )' % (A0, BXA, BYB))
    ree = w.s([exab, w.s([], 'reeanv', '( E. a e. RR E. b e. RR ( %s /\\ %s ) <-> ( E. a e. RR %s /\\ E. b e. RR %s ) )' % (BXA, BYB, BXA, BYB))], 'sylibr',
             '( %s -> E. a e. RR E. b e. RR ( %s /\\ %s ) )' % (A0, BXA, BYB))
    A1 = '( %s /\\ ( a e. RR /\\ b e. RR ) )' % TY
    A2 = '( %s /\\ ( %s /\\ %s ) )' % (A1, BXA, BYB)
    MX = 'if ( a <_ b , b , a )'
    ar = w.s([w.s([], 'simprl', '( %s -> a e. RR )' % A1)], 'adantr', '( %s -> a e. RR )' % A2)
    br = w.s([w.s([], 'simprr', '( %s -> b e. RR )' % A1)], 'adantr', '( %s -> b e. RR )' % A2)
    mxr = w.s([br, ar], 'ifcld', '( %s -> %s e. RR )' % (A2, MX))
    amx = w.s([ar, br, w.inst('max1')], 'syl2anc', '( %s -> a <_ %s )' % (A2, MX))
    bmx = w.s([ar, br, w.inst('max2')], 'syl2anc', '( %s -> b <_ %s )' % (A2, MX))
    ff = w.s([w.s([w.s([], 'simp1', '( %s -> F : D --> CC )' % TY)], 'adantr', '( %s -> F : D --> CC )' % A1)], 'adantr', '( %s -> F : D --> CC )' % A2)
    xd = w.s([w.s([w.s([], 'simp2', '( %s -> X C_ D )' % TY)], 'adantr', '( %s -> X C_ D )' % A1)], 'adantr', '( %s -> X C_ D )' % A2)
    yd = w.s([w.s([w.s([], 'simp3', '( %s -> Y C_ D )' % TY)], 'adantr', '( %s -> Y C_ D )' % A1)], 'adantr', '( %s -> Y C_ D )' % A2)
    bx = w.s([w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (A2, BXA, BYB)), w.inst('simpl')], 'syl', '( %s -> %s )' % (A2, BXA))
    by = w.s([w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (A2, BXA, BYB)), w.inst('simpr')], 'syl', '( %s -> %s )' % (A2, BYB))
    def lift(S, sd, bd, c, cmx):
        A3 = '( %s /\\ u e. %s )' % (A2, S)
        us = w.s([], 'simpr', '( %s -> u e. %s )' % (A3, S))
        ud = w.s([w.s([sd], 'adantr', '( %s -> %s C_ D )' % (A3, S)), us], 'sseldd', '( %s -> u e. D )' % A3)
        fu = w.s([w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A3), ud], 'ffvelcdmd', '( %s -> ( F ` u ) e. CC )' % A3)], 'abscld', '( %s -> ( abs ` ( F ` u ) ) e. RR )' % A3)
        tsub = w.s([w.s([w.s([], 'fveq2', '( t = u -> ( F ` t ) = ( F ` u ) )')], 'fveq2d', '( t = u -> ( abs ` ( F ` t ) ) = ( abs ` ( F ` u ) ) )')], 'breq1d', '( t = u -> ( ( abs ` ( F ` t ) ) <_ %s <-> ( abs ` ( F ` u ) ) <_ %s ) )' % (c, c))
        le1 = w.s([tsub, w.s([bd], 'adantr', '( %s -> %s )' % (A3, BD(S, c, 't'))), us], 'rspcdva', '( %s -> ( abs ` ( F ` u ) ) <_ %s )' % (A3, c))
        cr = w.s([ar if c == 'a' else br], 'adantr', '( %s -> %s e. RR )' % (A3, c))
        mx3 = w.s([mxr], 'adantr', '( %s -> %s e. RR )' % (A3, MX))
        le2 = w.s([fu, cr, mx3, le1, w.s([cmx], 'adantr', '( %s -> %s <_ %s )' % (A3, c, MX))], 'letrd', '( %s -> ( abs ` ( F ` u ) ) <_ %s )' % (A3, MX))
        return w.s([le2], 'ralrimiva', '( %s -> %s )' % (A2, BD(S, MX)))
    lx = lift('X', xd, bx, 'a', amx)
    ly = lift('Y', yd, by, 'b', bmx)
    un = w.s([lx, ly, w.s([], 'ralunb', '( %s <-> ( %s /\\ %s ) )' % (BD('( X u. Y )', MX), BD('X', MX), BD('Y', MX)))], 'sylanbrc', '( %s -> %s )' % (A2, BD('( X u. Y )', MX)))
    sub = w.s([w.s([], 'breq2', '( m = %s -> ( ( abs ` ( F ` u ) ) <_ m <-> ( abs ` ( F ` u ) ) <_ %s ) )' % (MX, MX))], 'ralbidv', '( m = %s -> ( %s <-> %s ) )' % (MX, BD('( X u. Y )', 'm'), BD('( X u. Y )', MX)))
    exm = w.s([mxr, un, w.s([sub], 'rspcev', '( ( %s e. RR /\\ %s ) -> E. m e. RR %s )' % (MX, BD('( X u. Y )', MX), BD('( X u. Y )', 'm')))], 'syl2anc', '( %s -> E. m e. RR %s )' % (A2, BD('( X u. Y )', 'm')))
    rl = w.s([w.s([exm], 'ex', '( %s -> ( ( %s /\\ %s ) -> E. m e. RR %s ) )' % (A1, BXA, BYB, BD('( X u. Y )', 'm')))], 'rexlimdvva',
             '( %s -> ( E. a e. RR E. b e. RR ( %s /\\ %s ) -> E. m e. RR %s ) )' % (TY, BXA, BYB, BD('( X u. Y )', 'm')))
    w.qed([ree, w.s([ty, rl], 'syl', '( %s -> ( E. a e. RR E. b e. RR ( %s /\\ %s ) -> E. m e. RR %s ) )' % (A0, BXA, BYB, BD('( X u. Y )', 'm')))], 'mpd',
          '( %s -> E. m e. RR %s )' % (A0, BD('( X u. Y )', 'm')))
    run1(w)

    # ---- bddseg -------------------------------------------------------------------
    w = W('bddseg', 'A continuous function is bounded on a segment inside its domain.')
    SG = '( S cseg T )'
    A0 = '( ( S e. CC /\\ T e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % SG
    U01 = '( 0 [,] 1 )'
    LN = '( S + ( v x. ( T - S ) ) )'
    G = '( v e. %s |-> ( F ` %s ) )' % (U01, LN)
    st = w.s([], 'simpl', '( %s -> ( S e. CC /\\ T e. CC ) )' % A0)
    fs = w.s([], 'simpr', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, SG))
    sc = w.s([st, w.inst('simpl')], 'syl', '( %s -> S e. CC )' % A0)
    tc = w.s([st, w.inst('simpr')], 'syl', '( %s -> T e. CC )' % A0)
    fcn = w.s([fs, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    sd = w.s([fs, w.inst('simpr')], 'syl', '( %s -> %s C_ D )' % (A0, SG))
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    gcn = w.s([st, fs, closed(w, A0, 'ssid', '%s C_ %s' % (U01, U01)), w.inst('cseglincnf')], 'syl3anc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, G, U01))
    bd = w.s([closed(w, A0, '0re', '0 e. RR'), closed(w, A0, '1re', '1 e. RR'), gcn, w.inst('cniccbdd')], 'syl3anc', '( %s -> E. m e. RR A. s e. %s ( abs ` ( %s ` s ) ) <_ m )' % (A0, U01, G))
    A1 = '( %s /\\ ( m e. RR /\\ A. s e. %s ( abs ` ( %s ` s ) ) <_ m ) )' % (A0, U01, G)
    A2 = '( %s /\\ u e. %s )' % (A1, SG)
    A3 = '( %s /\\ ( t e. %s /\\ u = ( S + ( t x. ( T - S ) ) ) ) )' % (A2, U01)
    LT = '( S + ( t x. ( T - S ) ) )'
    ue = w.s([], 'simpr', '( %s -> u e. %s )' % (A2, SG))
    csl = w.s([w.s([st], 'adantr', '( %s -> ( S e. CC /\\ T e. CC ) )' % A1), w.inst('csegel')], 'syl', '( %s -> ( u e. %s <-> E. t e. %s u = %s ) )' % (A1, SG, U01, LT))
    ext = w.s([ue, w.s([csl], 'adantr', '( %s -> ( u e. %s <-> E. t e. %s u = %s ) )' % (A2, SG, U01, LT))], 'mpbid', '( %s -> E. t e. %s u = %s )' % (A2, U01, LT))
    cnd = w.s([], 'simpr', '( %s -> ( t e. %s /\\ u = %s ) )' % (A3, U01, LT))
    t01 = w.s([cnd, w.inst('simpl')], 'syl', '( %s -> t e. %s )' % (A3, U01))
    ueq = w.s([cnd, w.inst('simpr')], 'syl', '( %s -> u = %s )' % (A3, LT))
    sub = w.s([w.s([w.s([], 'oveq1', '( v = t -> ( v x. ( T - S ) ) = ( t x. ( T - S ) ) )')], 'oveq2d', '( v = t -> %s = %s )' % (LN, LT))], 'fveq2d', '( v = t -> ( F ` %s ) = ( F ` %s ) )' % (LN, LT))
    fvx = w.s([w.s([], 'fvex', '( F ` %s ) e. _V' % LT)], 'a1i', '( %s -> ( F ` %s ) e. _V )' % (A3, LT))
    gt = w.s([t01, fvx, w.s([sub, w.s([], 'eqid', '%s = %s' % (G, G))], 'fvmptg', '( ( t e. %s /\\ ( F ` %s ) e. _V ) -> ( %s ` t ) = ( F ` %s ) )' % (U01, LT, G, LT))], 'syl2anc', '( %s -> ( %s ` t ) = ( F ` %s ) )' % (A3, G, LT))
    gtu = w.s([gt, w.s([w.s([ueq], 'eqcomd', '( %s -> %s = u )' % (A3, LT))], 'fveq2d', '( %s -> ( F ` %s ) = ( F ` u ) )' % (A3, LT))], 'eqtrd', '( %s -> ( %s ` t ) = ( F ` u ) )' % (A3, G))
    all_ = w.s([w.s([w.s([], 'simprr', '( %s -> A. s e. %s ( abs ` ( %s ` s ) ) <_ m )' % (A1, U01, G))], 'adantr', '( %s -> A. s e. %s ( abs ` ( %s ` s ) ) <_ m )' % (A2, U01, G))], 'adantr',
               '( %s -> A. s e. %s ( abs ` ( %s ` s ) ) <_ m )' % (A3, U01, G))
    ssub = w.s([w.s([w.s([], 'fveq2', '( s = t -> ( %s ` s ) = ( %s ` t ) )' % (G, G))], 'fveq2d', '( s = t -> ( abs ` ( %s ` s ) ) = ( abs ` ( %s ` t ) ) )' % (G, G))], 'breq1d',
               '( s = t -> ( ( abs ` ( %s ` s ) ) <_ m <-> ( abs ` ( %s ` t ) ) <_ m ) )' % (G, G))
    bt = w.s([ssub, all_, t01], 'rspcdva', '( %s -> ( abs ` ( %s ` t ) ) <_ m )' % (A3, G))
    bu = w.s([w.s([gtu], 'fveq2d', '( %s -> ( abs ` ( %s ` t ) ) = ( abs ` ( F ` u ) ) )' % (A3, G)), bt], 'eqbrtrrd', '( %s -> ( abs ` ( F ` u ) ) <_ m )' % A3)
    im = w.s([w.s([bu], 'ex', '( %s -> ( ( t e. %s /\\ u = %s ) -> ( abs ` ( F ` u ) ) <_ m ) )' % (A2, U01, LT))], 'expd', '( %s -> ( t e. %s -> ( u = %s -> ( abs ` ( F ` u ) ) <_ m ) ) )' % (A2, U01, LT))
    rl = w.s([im], 'rexlimdv', '( %s -> ( E. t e. %s u = %s -> ( abs ` ( F ` u ) ) <_ m ) )' % (A2, U01, LT))
    bu2 = w.s([ext, rl], 'mpd', '( %s -> ( abs ` ( F ` u ) ) <_ m )' % A2)
    ral = w.s([bu2], 'ralrimiva', '( %s -> A. u e. %s ( abs ` ( F ` u ) ) <_ m )' % (A1, SG))
    mr = w.s([], 'simprl', '( %s -> m e. RR )' % A1)
    exm = w.s([mr, ral], 'jca', '( %s -> ( m e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ m ) )' % (A1, SG))
    rex = w.s([w.s([w.s([exm], 'ex', '( %s -> ( ( m e. RR /\\ A. s e. %s ( abs ` ( %s ` s ) ) <_ m ) -> ( m e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ m ) ) )' % (A0, U01, G, SG))], 'expdimp', '( ( %s /\\ m e. RR ) -> ( A. s e. %s ( abs ` ( %s ` s ) ) <_ m -> ( m e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ m ) ) )' % (A0, U01, G, SG))], 'reximdva',
              '( %s -> ( E. m e. RR A. s e. %s ( abs ` ( %s ` s ) ) <_ m -> E. m e. RR ( m e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ m ) ) )' % (A0, U01, G, SG))
    ex3 = w.s([bd, rex], 'mpd', '( %s -> E. m e. RR ( m e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ m ) )' % (A0, SG))
    strip = w.s([w.s([], 'simpr', '( ( m e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ m ) -> A. u e. %s ( abs ` ( F ` u ) ) <_ m )' % (SG, SG))], 'reximi',
                '( E. m e. RR ( m e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ m ) -> E. m e. RR A. u e. %s ( abs ` ( F ` u ) ) <_ m )' % (SG, SG))
    w.qed([ex3, strip], 'syl', '( %s -> E. m e. RR A. u e. %s ( abs ` ( F ` u ) ) <_ m )' % (A0, SG))
    run1(w)

    # ---- holfrmbd -----------------------------------------------------------------
    w = W('holfrmbd', 'A continuous function is bounded on the frame of a rectangle inside its domain.')
    A0 = '( %s /\\ %s /\\ ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (AB, GEO, FR)
    ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
    geo = w.s([], 'simp2', '( %s -> %s )' % (A0, GEO))
    fc = w.s([], 'simp3', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, FR))
    fcn = w.s([fc, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    frd = w.s([fc, w.inst('simpr')], 'syl', '( %s -> %s C_ D )' % (A0, FR))
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
    ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
    sd = edges4(w, A0, frd, 'D')
    bds = []
    for i in range(4):
        S, T = EDGES[i]
        st = w.s([cc[S], cc[T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
        fs = w.s([fcn, sd[i]], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, SEGS[i]))
        bds.append(w.s([st, fs, w.inst('bddseg')], 'syl2anc', '( %s -> E. m e. RR %s )' % (A0, BD(SEGS[i], 'm'))))
    def union(X, Y, xd, yd, bx, by):
        ty = w.s([ff, xd, yd], '3jca', '( %s -> ( F : D --> CC /\\ %s C_ D /\\ %s C_ D ) )' % (A0, X, Y))
        return w.s([ty, w.s([bx, by], 'jca', '( %s -> ( E. m e. RR %s /\\ E. m e. RR %s ) )' % (A0, BD(X, 'm'), BD(Y, 'm'))), w.inst('bddun')], 'syl2anc',
                   '( %s -> E. m e. RR %s )' % (A0, BD('( %s u. %s )' % (X, Y), 'm')))
    L = '( %s u. %s )' % (SEGS[0], SEGS[1]); Rr = '( %s u. %s )' % (SEGS[2], SEGS[3])
    bl = union(SEGS[0], SEGS[1], sd[0], sd[1], bds[0], bds[1])
    brr = union(SEGS[2], SEGS[3], sd[2], sd[3], bds[2], bds[3])
    ld = w.s([sd[0], sd[1]], 'unssd', '( %s -> %s C_ D )' % (A0, L))
    rd = w.s([sd[2], sd[3]], 'unssd', '( %s -> %s C_ D )' % (A0, Rr))
    ty = w.s([ff, ld, rd], '3jca', '( %s -> ( F : D --> CC /\\ %s C_ D /\\ %s C_ D ) )' % (A0, L, Rr))
    w.qed([ty, w.s([bl, brr], 'jca', '( %s -> ( E. m e. RR %s /\\ E. m e. RR %s ) )' % (A0, BD(L, 'm'), BD(Rr, 'm'))), w.inst('bddun')], 'syl2anc', '( %s -> E. m e. RR %s )' % (A0, BD(FR, 'm')))
    run1(w)
