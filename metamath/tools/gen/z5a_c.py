"""Sortie Z5a, section C: the window W (Detector.lean 1278-1358, GramFunction.lean 2622-2668, 2829-2846)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5alib import *
from cl import Closure, lift
import lin

OT = '<. M , X , L >.'
X1, M1, L1 = '( 2nd ` ( 1st ` u ) )', '( 1st ` ( 1st ` u ) )', '( 2nd ` u )'
OX1, OM1, OL1 = '( 2nd ` ( 1st ` %s ) )' % OT, '( 1st ` ( 1st ` %s ) )' % OT, '( 2nd ` %s )' % OT


def wparts(w, ante, eX, eM, eL, X0, Xn, M0_, Mn, L0, Ln, K):
    """from ( ante -> X0 = Xn ), ( ante -> M0 = Mn ), ( ante -> L0 = Ln ): ( ante -> WBODY(M0,X0,L0,K) = WBODY(Mn,Xn,Ln,K) )"""
    st = mkst(w, ante)

    def side(e, A0, An):
        la = st([e], 'fveq2d', '( log ` %s ) = ( log ` %s )' % (A0, An))
        a0 = '( log ` %s )' % A0; an = '( log ` %s )' % An
        sa = st([la, eL], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (a0, L0, an, Ln))
        dmid = 'S_ [ %s -> ( %s + %s ) ] %s _d t' % (an, a0, L0, WG(K))
        d1 = w.s([la, w.inst('ditgeq1')], 'syl', '( %s -> %s = %s )' % (ante, DI(a0, L0, K), dmid))
        d2 = w.s([sa, w.inst('ditgeq2')], 'syl', '( %s -> %s = %s )' % (ante, dmid, DI(an, Ln, K)))
        d = st([d1, d2], 'eqtrd', '%s = %s' % (DI(a0, L0, K), DI(an, Ln, K)))
        r = st([eL], 'oveq2d', '( 1 / %s ) = ( 1 / %s )' % (L0, Ln))
        return st([r, d], 'oveq12d', '%s = %s' % (AV(a0, L0, K), AV(an, Ln, K)))
    px = side(eX, X0, Xn); pm = side(eM, M0_, Mn)
    return st([px, pm], 'oveq12d', '%s = %s' % (WBODY(M0_, X0, L0, K), WBODY(Mn, Xn, Ln, K)))


def z5wwinval():
    w = W('z5wwinval', "Value of the double window (Lean Wwin, Detector.lean 1282): ( ( WWin ` <. M , X , L >. ) ` K ) is the average of "
                       "e ^ ( - K / e ^ t ) over t from log X to log X + L minus its average from log M to log M + L.")
    ante = '( ( M e. U /\\ X e. V /\\ L e. W ) /\\ K e. NN )'
    st = mkst(w, ante)
    # the mapping at u = OT
    ua = 'u = %s' % OT
    eL = w.s([], 'fveq2', '( %s -> %s = %s )' % (ua, L1, OL1))
    e1 = w.s([], 'fveq2', '( %s -> ( 1st ` u ) = ( 1st ` %s ) )' % (ua, OT))
    eX = w.s([e1], 'fveq2d', '( %s -> %s = %s )' % (ua, X1, OX1))
    eM = w.s([e1], 'fveq2d', '( %s -> %s = %s )' % (ua, M1, OM1))
    bd = wparts(w, ua, eX, eM, eL, X1, OX1, M1, OM1, L1, OL1, 'n')
    MPU = '( n e. NN |-> %s )' % WBODY(M1, X1, L1, 'n')
    MPO = '( n e. NN |-> %s )' % WBODY(OM1, OX1, OL1, 'n')
    mp = w.s([bd], 'mpteq2dv', '( %s -> %s = %s )' % (ua, MPU, MPO))
    df = w.s([], 'df-wwin', 'WWin = ( u e. _V |-> %s )' % MPU)
    ex = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % MPO)
    fv = w.s([mp, df, ex], 'fvmpt', '( %s e. _V -> ( WWin ` %s ) = %s )' % (OT, OT, MPO))
    fv2 = w.s([w.s([], 'otex', '%s e. _V' % OT), fv], 'ax-mp', '( WWin ` %s ) = %s' % (OT, MPO))
    f1 = st([a1(w, ante, fv2, '( WWin ` %s ) = %s' % (OT, MPO))], 'fveq1d', '( ( WWin ` %s ) ` K ) = ( %s ` K )' % (OT, MPO))
    # the value at K
    na = 'n = K'
    idn = w.s([], 'id', '( n = K -> n = K )')
    gn, _g = w.congr(WG('n'), {'n': 'K'}, na, {'n': idn})
    gt = w.s([gn], 'adantr', '( ( n = K /\\ t e. RR ) -> %s = %s )' % (WG('n'), WG('K')))
    def dside(A0):
        a0 = '( log ` %s )' % A0
        d = w.s([gt], 'ditgeq3dv', '( n = K -> %s = %s )' % (DI(a0, OL1, 'n'), DI(a0, OL1, 'K')))
        return w.s([d], 'oveq2d', '( n = K -> %s = %s )' % (AV(a0, OL1, 'n'), AV(a0, OL1, 'K')))
    cn = w.s([dside(OX1), dside(OM1)], 'oveq12d', '( n = K -> %s = %s )' % (WBODY(OM1, OX1, OL1, 'n'), WBODY(OM1, OX1, OL1, 'K')))
    eq = w.s([], 'eqid', '%s = %s' % (MPO, MPO))
    fk = w.s([cn, eq, w.s([], 'ovex', '%s e. _V' % WBODY(OM1, OX1, OL1, 'K'))], 'fvmpt', '( K e. NN -> ( %s ` K ) = %s )' % (MPO, WBODY(OM1, OX1, OL1, 'K')))
    f2 = st([st([], 'simpr', 'K e. NN'), fk], 'syl', '( %s ` K ) = %s' % (MPO, WBODY(OM1, OX1, OL1, 'K')))
    # the components of the triple
    h3 = st([], 'simpl', '( M e. U /\\ X e. V /\\ L e. W )')
    o1 = st([h3, w.inst('ot1stg')], 'syl', '%s = M' % OM1)
    o2 = st([h3, w.inst('ot2ndg')], 'syl', '%s = X' % OX1)
    o3 = st([st([h3], 'simp3d', 'L e. W'), w.inst('ot3rdg')], 'syl', '%s = L' % OL1)
    f3 = wparts(w, ante, o2, o1, o3, OX1, 'X', OM1, 'M', OL1, 'L', 'K')
    last = eqtr(w, ante, [f1, f2], None)
    w.qed([last, f3], 'eqtrd', STATEMENTS['z5wwinval'])
    return w


def wgre(w, a, kr, tr, t='t'):
    """( a -> WG(K,t) e. RR ) from K e. RR, t e. RR"""
    st = mkst(w, a)
    q = st([st([kr], 'renegcld', '-u K e. RR'), st([tr], 'rpefcld', '( exp ` %s ) e. RR+' % t)], 'rerpdivcld', '( -u K / ( exp ` %s ) ) e. RR' % t)
    return st([q], 'reefcld', '%s e. RR' % WG('K', t))


def z5wcn():
    w = W('z5wcn', "Lean continuous_windowIntegrand, on a compact interval: t |-> e ^ ( - K / e ^ t ) is continuous on ( A [,] B ).")
    ante = '( ( A e. RR /\\ B e. RR ) /\\ K e. RR )'
    st = mkst(w, ante)
    ar = st([], 'simpll', 'A e. RR'); br = st([], 'simplr', 'B e. RR'); kr = st([], 'simpr', 'K e. RR')
    I = '( A [,] B )'
    ssr = st([ar, br, w.inst('iccssre')], 'syl2anc', '%s C_ RR' % I)
    ssc = st([ssr, a1c(w, ante, 'ax-resscn', 'RR C_ CC')], 'sstrd', '%s C_ CC' % I)
    ccss = st([], 'ssidd', 'CC C_ CC')
    idc = st([ssc, ccss, w.inst('cncfmptid')], 'syl2anc', '( t e. %s |-> t ) e. ( %s -cn-> CC )' % (I, I))
    EX = '( t e. %s |-> ( exp ` t ) )' % I
    exc = st([a1c(w, ante, 'efcn', 'exp e. ( CC -cn-> CC )'), idc], 'cncfmpt1f', '%s e. ( %s -cn-> CC )' % (EX, I))
    a = '( %s /\\ t e. %s )' % (ante, I)
    sa = mkst(w, a)
    tr = sa([lift(w, ssr, a), sa([], 'simpr', 't e. %s' % I)], 'sseldd', 't e. RR')
    ecd = sy(w, a, sa([tr], 'rpefcld', '( exp ` t ) e. RR+'), 'rpcndif0', '( exp ` t ) e. ( CC \\ { 0 } )')
    fm = st([ecd, w.s([], 'eqid', '%s = %s' % (EX, EX))], 'fmptd', '%s : %s --> ( CC \\ { 0 } )' % (EX, I))
    cd = st([st([], 'difssd', '( CC \\ { 0 } ) C_ CC'), exc, w.inst('cncfcdm')], 'syl2anc',
            '( %s e. ( %s -cn-> ( CC \\ { 0 } ) ) <-> %s : %s --> ( CC \\ { 0 } ) )' % (EX, I, EX, I))
    ex0 = st([fm, cd], 'mpbird', '%s e. ( %s -cn-> ( CC \\ { 0 } ) )' % (EX, I))
    nk = st([st([kr], 'renegcld', '-u K e. RR')], 'recnd', '-u K e. CC')
    cc = st([nk, ssc, ccss, w.inst('cncfmptc')], 'syl3anc', '( t e. %s |-> -u K ) e. ( %s -cn-> CC )' % (I, I))
    dv = st([cc, ex0], 'divcncf', '( t e. %s |-> ( -u K / ( exp ` t ) ) ) e. ( %s -cn-> CC )' % (I, I))
    w.qed([a1c(w, ante, 'efcn', 'exp e. ( CC -cn-> CC )'), dv], 'cncfmpt1f', STATEMENTS['z5wcn'])
    return w


def z5wibl():
    w = W('z5wibl', "The window integrand is integrable on ( A (,) B ) and its integral is real (the integrability behind Lean's "
                    "intervalIntegral.integral_mono_on in exp_sub_exp_le_Wwin).")
    ante = '( ( A e. RR /\\ B e. RR ) /\\ K e. RR )'
    st = mkst(w, ante)
    ar = st([], 'simpll', 'A e. RR'); br = st([], 'simplr', 'B e. RR'); kr = st([], 'simpr', 'K e. RR')
    I = '( A [,] B )'; O = '( A (,) B )'
    cn = st([st([], 'id', ante), w.inst('z5wcn')], 'syl', '( t e. %s |-> %s ) e. ( %s -cn-> CC )' % (I, WG('K'), I))
    ib = st([ar, br, cn, w.inst('cniccibl')], 'syl3anc', '( t e. %s |-> %s ) e. L^1' % (I, WG('K')))
    ai = '( %s /\\ t e. %s )' % (ante, I)
    iv = w.s([], 'fvexd', '( %s -> %s e. _V )' % (ai, WG('K')))
    ibo = st([a1c(w, ante, 'ioossicc', '%s C_ %s' % (O, I)), a1c(w, ante, 'ioombl', '%s e. dom vol' % O), iv, ib], 'iblss', '( t e. %s |-> %s ) e. L^1' % (O, WG('K')))
    ao = '( %s /\\ t e. %s )' % (ante, O)
    tr = sy(w, ao, w.s([], 'simpr', '( %s -> t e. %s )' % (ao, O)), 'elioore', 't e. RR')
    gr = wgre(w, ao, lift(w, kr, ao), tr)
    re = st([gr, ibo], 'itgrecl', 'S. %s %s _d t e. RR' % (O, WG('K')))
    w.qed([ibo, re], 'jca', STATEMENTS['z5wibl'])
    return w


def z5wmono():
    w = W('z5wmono', "The window integrand e ^ ( - K / e ^ t ) is nondecreasing in t for K >_ 0 (Lean hmono in exp_sub_exp_le_Wwin).")
    ante = '( ( K e. RR /\\ 0 <_ K ) /\\ ( Y e. RR /\\ Z e. RR /\\ Y <_ Z ) )'
    st = mkst(w, ante)
    kr = st([], 'simpll', 'K e. RR'); k0 = st([], 'simplr', '0 <_ K')
    h = st([], 'simpr', '( Y e. RR /\\ Z e. RR /\\ Y <_ Z )')
    yr = st([h], 'simp1d', 'Y e. RR'); zr = st([h], 'simp2d', 'Z e. RR'); yz = st([h], 'simp3d', 'Y <_ Z')
    EY = '( exp ` Y )'; EZ = '( exp ` Z )'
    ey = st([yr], 'rpefcld', '%s e. RR+' % EY); ez = st([zr], 'rpefcld', '%s e. RR+' % EZ)
    le = st([yz, sy2(w, ante, yr, zr, 'efle', '( Y <_ Z <-> %s <_ %s )' % (EY, EZ))], 'mpbid', '%s <_ %s' % (EY, EZ))
    dv = st([ey, ez, kr, k0, le], 'lediv2ad', '( K / %s ) <_ ( K / %s )' % (EZ, EY))
    qy = st([kr, ey], 'rerpdivcld', '( K / %s ) e. RR' % EY); qz = st([kr, ez], 'rerpdivcld', '( K / %s ) e. RR' % EZ)
    ng = st([dv, st([qz, qy], 'lenegd', '( ( K / %s ) <_ ( K / %s ) <-> -u ( K / %s ) <_ -u ( K / %s ) )' % (EZ, EY, EY, EZ))], 'mpbid',
            '-u ( K / %s ) <_ -u ( K / %s )' % (EY, EZ))
    kc = st([kr], 'recnd', 'K e. CC')
    dy = st([kc, st([ey], 'rpcnd', '%s e. CC' % EY), st([ey], 'rpne0d', '%s =/= 0' % EY)], 'divnegd', '-u ( K / %s ) = ( -u K / %s )' % (EY, EY))
    dz = st([kc, st([ez], 'rpcnd', '%s e. CC' % EZ), st([ez], 'rpne0d', '%s =/= 0' % EZ)], 'divnegd', '-u ( K / %s ) = ( -u K / %s )' % (EZ, EZ))
    ng2 = st([ng, dy, dz], '3brtr3d', '( -u K / %s ) <_ ( -u K / %s )' % (EY, EZ))
    ry = st([st([kr], 'renegcld', '-u K e. RR'), ey], 'rerpdivcld', '( -u K / %s ) e. RR' % EY)
    rz = st([st([kr], 'renegcld', '-u K e. RR'), ez], 'rerpdivcld', '( -u K / %s ) e. RR' % EZ)
    bi = sy2(w, ante, ry, rz, 'efle', '( ( -u K / %s ) <_ ( -u K / %s ) <-> %s <_ %s )' % (EY, EZ, WG('K', 'Y'), WG('K', 'Z')))
    w.qed([ng2, bi], 'mpbid', STATEMENTS['z5wmono'])
    return w


def z5wavg():
    w = W('z5wavg', "The average of the window integrand over [ A , A + L ] lies between its values at the two ends (Lean h1, h2 of "
                    "exp_sub_exp_le_Wwin: integral_mono_on against a constant, integral_const).")
    ante = '( ( A e. RR /\\ L e. RR+ ) /\\ ( K e. RR /\\ 0 <_ K ) )'
    st = mkst(w, ante)
    ar = st([], 'simpll', 'A e. RR'); lrp = st([], 'simplr', 'L e. RR+'); kr = st([], 'simprl', 'K e. RR'); k0 = st([], 'simprr', '0 <_ K')
    lr = st([lrp], 'rpred', 'L e. RR')
    B = '( A + L )'
    br = st([ar, lr], 'readdcld', '%s e. RR' % B)
    ab = lin.linarith(w, ante, [st([lrp], 'rpgt0d', '0 < L')], 'A <_ %s' % B, leaves={'A': ar, 'L': lr})
    O = '( A (,) %s )' % B
    G = WG('K')
    DIS = DI('A', 'L', 'K')
    I = 'S. %s %s _d t' % (O, G)
    dp = st([ab], 'ditgpos', '%s = %s' % (DIS, I))
    ib = st([ar, br, kr, w.inst('z5wibl')], 'syl21anc', '( ( t e. %s |-> %s ) e. L^1 /\\ %s e. RR )' % (O, G, I))
    ibl = st([ib], 'simpld', '( t e. %s |-> %s ) e. L^1' % (O, G)); ir = st([ib], 'simprd', '%s e. RR' % I)
    C1 = WG('K', 'A'); C2 = WG('K', B)
    c1r = wgre(w, ante, kr, ar, 'A'); c2r = wgre(w, ante, kr, br, B)
    vo = st([ar, br, ab, w.inst('volioo')], 'syl3anc', '( vol ` %s ) = ( %s - A )' % (O, B))
    vl = st([vo, st([st([ar], 'recnd', 'A e. CC'), st([lr], 'recnd', 'L e. CC')], 'pncan2d', '( %s - A ) = L' % B)], 'eqtrd', '( vol ` %s ) = L' % O)
    vr = st([vl, lr], 'eqeltrd', '( vol ` %s ) e. RR' % O)
    dvo = a1c(w, ante, 'ioombl', '%s e. dom vol' % O)
    a = '( %s /\\ t e. %s )' % (ante, O)
    sa = mkst(w, a)
    tin = w.s([], 'simpr', '( %s -> t e. %s )' % (a, O))
    tr = sy(w, a, tin, 'elioore', 't e. RR')
    od = sy(w, a, tin, 'eliooord', '( A < t /\\ t < %s )' % B)
    at = sa([sa([od], 'simpld', 'A < t')], 'ltled', 'A <_ t'); tb = sa([sa([od], 'simprd', 't < %s' % B)], 'ltled', 't <_ %s' % B)
    kk = sa([lift(w, kr, a), lift(w, k0, a)], 'jca', '( K e. RR /\\ 0 <_ K )')
    m1 = sa([kk, sa([lift(w, ar, a), tr, at], '3jca', '( A e. RR /\\ t e. RR /\\ A <_ t )'), w.inst('z5wmono')], 'syl2anc', '%s <_ %s' % (C1, G))
    m2 = sa([kk, sa([tr, lift(w, br, a), tb], '3jca', '( t e. RR /\\ %s e. RR /\\ t <_ %s )' % (B, B)), w.inst('z5wmono')], 'syl2anc', '%s <_ %s' % (G, C2))
    gr = wgre(w, a, lift(w, kr, a), tr)
    def const(C, cr):
        cc = st([cr], 'recnd', '%s e. CC' % C)
        ic0 = st([dvo, vr, cc, w.inst('iblconst')], 'syl3anc', '( %s X. { %s } ) e. L^1' % (O, C))
        ic = st([a1c(w, ante, 'fconstmpt', '( %s X. { %s } ) = ( t e. %s |-> %s )' % (O, C, O, C)), ic0], 'eqeltrrd', '( t e. %s |-> %s ) e. L^1' % (O, C))
        it = st([dvo, vr, cc, w.inst('itgconst')], 'syl3anc', 'S. %s %s _d t = ( %s x. ( vol ` %s ) )' % (O, C, C, O))
        it2 = st([it, st([vl], 'oveq2d', '( %s x. ( vol ` %s ) ) = ( %s x. L )' % (C, O, C))], 'eqtrd', 'S. %s %s _d t = ( %s x. L )' % (O, C, C))
        return ic, it2
    ic1, it1 = const(C1, c1r); ic2, it2 = const(C2, c2r)
    l1 = st([ic1, ibl, lift(w, c1r, a), gr, m1], 'itgle', 'S. %s %s _d t <_ %s' % (O, C1, I))
    l1b = st([it1, l1], 'eqbrtrrd', '( %s x. L ) <_ %s' % (C1, I))
    u1 = st([ibl, ic2, gr, lift(w, c2r, a), m2], 'itgle', '%s <_ S. %s %s _d t' % (I, O, C2))
    u1b = st([u1, it2], 'breqtrd', '%s <_ ( %s x. L )' % (I, C2))
    # the average
    AVS = AV('A', 'L', 'K')
    av1 = st([dp], 'oveq2d', '%s = ( ( 1 / L ) x. %s )' % (AVS, I))
    av2 = st([st([ir], 'recnd', '%s e. CC' % I), st([lrp], 'rpcnd', 'L e. CC'), st([lrp], 'rpne0d', 'L =/= 0')], 'divrec2d', '( %s / L ) = ( ( 1 / L ) x. %s )' % (I, I))
    av = st([av1, av2], 'eqtr4d', '%s = ( %s / L )' % (AVS, I))
    lo = st([l1b, st([c1r, ir, lrp], 'lemuldivd', '( ( %s x. L ) <_ %s <-> %s <_ ( %s / L ) )' % (C1, I, C1, I))], 'mpbid', '%s <_ ( %s / L )' % (C1, I))
    u1c = st([u1b, st([st([c2r], 'recnd', '%s e. CC' % C2), st([lr], 'recnd', 'L e. CC')], 'mulcomd', '( %s x. L ) = ( L x. %s )' % (C2, C2))], 'breqtrd',
             '%s <_ ( L x. %s )' % (I, C2))
    up = st([u1c, st([ir, c2r, lrp], 'ledivmuld', '( ( %s / L ) <_ %s <-> %s <_ ( L x. %s ) )' % (I, C2, I, C2))], 'mpbird', '( %s / L ) <_ %s' % (I, C2))
    lo2 = st([lo, av], 'breqtrrd', '%s <_ %s' % (C1, AVS))
    up2 = st([av, up], 'eqbrtrd', '%s <_ %s' % (AVS, C2))
    w.qed([lo2, up2], 'jca', STATEMENTS['z5wavg'])
    return w


def avre(w, ante, ar, lrp, kr, a):
    """( ante -> AV(a,L,K) e. RR ) from a e. RR (ar), L e. RR+, K e. RR"""
    st = mkst(w, ante)
    lr = st([lrp], 'rpred', 'L e. RR')
    B = '( %s + L )' % a
    br = st([ar, lr], 'readdcld', '%s e. RR' % B)
    ab = lin.linarith(w, ante, [st([lrp], 'rpgt0d', '0 < L')], '%s <_ %s' % (a, B), leaves={a: ar, 'L': lr})
    O = '( %s (,) %s )' % (a, B)
    I = 'S. %s %s _d t' % (O, WG('K'))
    dp = st([ab], 'ditgpos', '%s = %s' % (DI(a, 'L', 'K'), I))
    ir = st([st([ar, br, kr, w.inst('z5wibl')], 'syl21anc', '( ( t e. %s |-> %s ) e. L^1 /\\ %s e. RR )' % (O, WG('K'), I))], 'simprd', '%s e. RR' % I)
    dr = st([dp, ir], 'eqeltrd', '%s e. RR' % DI(a, 'L', 'K'))
    return st([st([st([lrp], 'rpreccld', '( 1 / L ) e. RR+')], 'rpred', '( 1 / L ) e. RR'), dr], 'remulcld',
              '%s e. RR' % AV(a, 'L', 'K'))


def z5wlow():
    w = W('z5wlow', "Lean exp_sub_exp_le_Wwin: e ^ ( - K / X ) - e ^ ( - K / ( M e ^ L ) ) <_ W ( K ) (the two halves of z5wavg at log X and log M).")
    ante = '( ( M e. RR+ /\\ X e. RR+ /\\ L e. RR+ ) /\\ K e. NN )'
    st = mkst(w, ante)
    h3 = st([], 'simpl', '( M e. RR+ /\\ X e. RR+ /\\ L e. RR+ )')
    mrp = st([h3], 'simp1d', 'M e. RR+'); xrp = st([h3], 'simp2d', 'X e. RR+'); lrp = st([h3], 'simp3d', 'L e. RR+')
    knn = st([], 'simpr', 'K e. NN')
    wv = st([mrp, xrp, lrp, knn, w.inst('z5wwinval')], 'syl31anc', '%s = %s' % (WV('K'), WBODY('M', 'X', 'L', 'K')))
    kr = st([knn], 'nnred', 'K e. RR'); k0 = st([st([knn], 'nngt0d', '0 < K')], 'ltled', '0 <_ K')
    LX = '( log ` X )'; LM = '( log ` M )'
    lxr = st([xrp], 'relogcld', '%s e. RR' % LX); lmr = st([mrp], 'relogcld', '%s e. RR' % LM)
    kk = st([kr, k0], 'jca', '( K e. RR /\\ 0 <_ K )')
    ax = st([st([lxr, lrp], 'jca', '( %s e. RR /\\ L e. RR+ )' % LX), kk, w.inst('z5wavg')], 'syl2anc',
            '( %s <_ %s /\\ %s <_ %s )' % (WG('K', LX), AV(LX, 'L', 'K'), AV(LX, 'L', 'K'), WG('K', '( %s + L )' % LX)))
    am = st([st([lmr, lrp], 'jca', '( %s e. RR /\\ L e. RR+ )' % LM), kk, w.inst('z5wavg')], 'syl2anc',
            '( %s <_ %s /\\ %s <_ %s )' % (WG('K', LM), AV(LM, 'L', 'K'), AV(LM, 'L', 'K'), WG('K', '( %s + L )' % LM)))
    lo = st([ax], 'simpld', '%s <_ %s' % (WG('K', LX), AV(LX, 'L', 'K')))
    up = st([am], 'simprd', '%s <_ %s' % (AV(LM, 'L', 'K'), WG('K', '( %s + L )' % LM)))
    ex = sy(w, ante, xrp, 'reeflog', '( exp ` %s ) = X' % LX)
    E1 = '( exp ` ( -u K / X ) )'
    r1, _n = w.rewrite(WG('K', LX), {'( exp ` %s )' % LX: ('X', ex)}, ante)
    lo2 = st([r1, lo], 'eqbrtrrd', '%s <_ %s' % (E1, AV(LX, 'L', 'K')))
    ML = '( M x. ( exp ` L ) )'
    ea = sy2(w, ante, st([lmr], 'recnd', '%s e. CC' % LM), st([st([lrp], 'rpred', 'L e. RR')], 'recnd', 'L e. CC'), 'efadd',
             '( exp ` ( %s + L ) ) = ( ( exp ` %s ) x. ( exp ` L ) )' % (LM, LM))
    em = st([ea, st([sy(w, ante, mrp, 'reeflog', '( exp ` %s ) = M' % LM)], 'oveq1d', '( ( exp ` %s ) x. ( exp ` L ) ) = %s' % (LM, ML))], 'eqtrd',
            '( exp ` ( %s + L ) ) = %s' % (LM, ML))
    E2 = '( exp ` ( -u K / %s ) )' % ML
    r2, _n = w.rewrite(WG('K', '( %s + L )' % LM), {'( exp ` ( %s + L ) )' % LM: (ML, em)}, ante)
    up2 = st([up, r2], 'breqtrd', '%s <_ %s' % (AV(LM, 'L', 'K'), E2))
    e1r = st([st([st([kr], 'renegcld', '-u K e. RR'), xrp], 'rerpdivcld', '( -u K / X ) e. RR')], 'reefcld', '%s e. RR' % E1)
    mlrp = st([mrp, st([st([lrp], 'rpred', 'L e. RR')], 'rpefcld', '( exp ` L ) e. RR+')], 'rpmulcld', '%s e. RR+' % ML)
    e2r = st([st([st([kr], 'renegcld', '-u K e. RR'), mlrp], 'rerpdivcld', '( -u K / %s ) e. RR' % ML)], 'reefcld', '%s e. RR' % E2)
    axr = avre(w, ante, lxr, lrp, kr, LX); amr = avre(w, ante, lmr, lrp, kr, LM)
    d = st([e1r, amr, axr, e2r, lo2, up2], 'le2subd', '( %s - %s ) <_ ( %s - %s )' % (E1, E2, AV(LX, 'L', 'K'), AV(LM, 'L', 'K')))
    w.qed([d, wv], 'breqtrrd', STATEMENTS['z5wlow'])
    return w


def wvre(w, ante, mrp, xrp, lrp, knn):
    """( ante -> WV(K) e. RR )"""
    st = mkst(w, ante)
    wv = st([mrp, xrp, lrp, knn, w.inst('z5wwinval')], 'syl31anc', '%s = %s' % (WV('K'), WBODY('M', 'X', 'L', 'K')))
    kr = st([knn], 'nnred', 'K e. RR')
    LX = '( log ` X )'; LM = '( log ` M )'
    ax = avre(w, ante, st([xrp], 'relogcld', '%s e. RR' % LX), lrp, kr, LX)
    am = avre(w, ante, st([mrp], 'relogcld', '%s e. RR' % LM), lrp, kr, LM)
    return st([wv, st([ax, am], 'resubcld', '%s e. RR' % WBODY('M', 'X', 'L', 'K'))], 'eqeltrd', '%s e. RR' % WV('K'))


def negdiv(w, ante, kc, drp, D):
    """( ante -> -u ( K / D ) = ( -u K / D ) )"""
    return w.s([kc, w.s([drp], 'rpcnd', '( %s -> %s e. CC )' % (ante, D)), w.s([drp], 'rpne0d', '( %s -> %s =/= 0 )' % (ante, D))], 'divnegd',
               '( %s -> -u ( K / %s ) = ( -u K / %s ) )' % (ante, D, D))


def z5wpos():
    w = W('z5wpos', "Lean Wwin_pos: W ( K ) > 0 for K >_ 1 when M e ^ L < X.")
    ante = '( ( ( M e. RR+ /\\ L e. RR+ ) /\\ ( X e. RR /\\ ( M x. ( exp ` L ) ) < X ) ) /\\ K e. NN )'
    st = mkst(w, ante)
    mrp = st([], 'simplll', 'M e. RR+'); lrp = st([], 'simpllr', 'L e. RR+')
    h = st([], 'simplr', '( X e. RR /\\ ( M x. ( exp ` L ) ) < X )')
    xr = st([h], 'simpld', 'X e. RR'); lt = st([h], 'simprd', '( M x. ( exp ` L ) ) < X')
    knn = st([], 'simpr', 'K e. NN')
    ML = '( M x. ( exp ` L ) )'
    mlrp = st([mrp, st([st([lrp], 'rpred', 'L e. RR')], 'rpefcld', '( exp ` L ) e. RR+')], 'rpmulcld', '%s e. RR+' % ML)
    xgt = lin.linarith(w, ante, [lt, st([mlrp], 'rpgt0d', '0 < %s' % ML)], '0 < X', leaves={'X': xr, ML: st([mlrp], 'rpred', '%s e. RR' % ML)})
    xrp = st([xr, xgt], 'elrpd', 'X e. RR+')
    E1 = '( exp ` ( -u K / X ) )'; E2 = '( exp ` ( -u K / %s ) )' % ML
    wl = st([mrp, xrp, lrp, knn, w.inst('z5wlow')], 'syl31anc', '( %s - %s ) <_ %s' % (E1, E2, WV('K')))
    krp = st([knn], 'nnrpd', 'K e. RR+'); kr = st([krp], 'rpred', 'K e. RR'); kc = st([krp], 'rpcnd', 'K e. CC')
    q = st([lt, st([mlrp, xrp, krp], 'ltdiv2d', '( %s < X <-> ( K / X ) < ( K / %s ) )' % (ML, ML))], 'mpbid', '( K / X ) < ( K / %s )' % ML)
    qx = st([kr, xrp], 'rerpdivcld', '( K / X ) e. RR'); qm = st([kr, mlrp], 'rerpdivcld', '( K / %s ) e. RR' % ML)
    ng = st([q, st([qx, qm], 'ltnegd', '( ( K / X ) < ( K / %s ) <-> -u ( K / %s ) < -u ( K / X ) )' % (ML, ML))], 'mpbid', '-u ( K / %s ) < -u ( K / X )' % ML)
    ng2 = st([ng, negdiv(w, ante, kc, mlrp, ML), negdiv(w, ante, kc, xrp, 'X')], '3brtr3d', '( -u K / %s ) < ( -u K / X )' % ML)
    am = st([st([kr], 'renegcld', '-u K e. RR'), mlrp], 'rerpdivcld', '( -u K / %s ) e. RR' % ML)
    ax = st([st([kr], 'renegcld', '-u K e. RR'), xrp], 'rerpdivcld', '( -u K / X ) e. RR')
    e = st([ng2, sy2(w, ante, am, ax, 'eflt', '( ( -u K / %s ) < ( -u K / X ) <-> %s < %s )' % (ML, E2, E1))], 'mpbid', '%s < %s' % (E2, E1))
    e1r = st([ax], 'reefcld', '%s e. RR' % E1); e2r = st([am], 'reefcld', '%s e. RR' % E2)
    p = st([e, st([e2r, e1r], 'posdifd', '( %s < %s <-> 0 < ( %s - %s ) )' % (E2, E1, E1, E2))], 'mpbid', '0 < ( %s - %s )' % (E1, E2))
    wr = wvre(w, ante, mrp, xrp, lrp, knn)
    w.qed([st([], '0red', '0 e. RR'), st([e1r, e2r], 'resubcld', '( %s - %s ) e. RR' % (E1, E2)), wr, p, wl], 'ltletrd', STATEMENTS['z5wpos'])
    return w


def z5wthird():
    w = W('z5wthird', "Lean Wwin_ge_third (GramFunction.lean 2624): W ( K ) >_ e ^ ( - K / X ) / 3 on K > Z when M e ^ L <_ Z and 2 Z <_ X "
                      "(e ^ ( - K / ( M e ^ L ) ) <_ e ^ ( - K / Z ) <_ e ^ ( - 1 / 2 ) e ^ ( - K / X ) <_ ( 2 / 3 ) e ^ ( - K / X )).")
    ante = STATEMENTS['z5wthird'].split(' -> ( ( 1 / 3 )')[0][2:]
    st = mkst(w, ante)
    H1 = '( ( M e. RR+ /\\ L e. RR+ ) /\\ ( Z e. RR+ /\\ X e. RR ) )'
    H2 = '( ( ( M x. ( exp ` L ) ) <_ Z /\\ ( 2 x. Z ) <_ X ) /\\ ( K e. NN /\\ Z < K ) )'
    h1 = st([], 'simpl', H1); h2 = st([], 'simpr', H2)
    mrp = st([st([h1], 'simpld', '( M e. RR+ /\\ L e. RR+ )')], 'simpld', 'M e. RR+'); lrp = st([st([h1], 'simpld', '( M e. RR+ /\\ L e. RR+ )')], 'simprd', 'L e. RR+')
    zrp = st([st([h1], 'simprd', '( Z e. RR+ /\\ X e. RR )')], 'simpld', 'Z e. RR+'); xr = st([st([h1], 'simprd', '( Z e. RR+ /\\ X e. RR )')], 'simprd', 'X e. RR')
    ML = '( M x. ( exp ` L ) )'
    g1 = st([h2], 'simpld', '( %s <_ Z /\\ ( 2 x. Z ) <_ X )' % ML); g2 = st([h2], 'simprd', '( K e. NN /\\ Z < K )')
    mz = st([g1], 'simpld', '%s <_ Z' % ML); zx = st([g1], 'simprd', '( 2 x. Z ) <_ X')
    knn = st([g2], 'simpld', 'K e. NN'); zk = st([g2], 'simprd', 'Z < K')
    zr = st([zrp], 'rpred', 'Z e. RR')
    xgt = lin.linarith(w, ante, [zx, st([zrp], 'rpgt0d', '0 < Z')], '0 < X', leaves={'X': xr, 'Z': zr})
    xrp = st([xr, xgt], 'elrpd', 'X e. RR+')
    krp = st([knn], 'nnrpd', 'K e. RR+'); kr = st([krp], 'rpred', 'K e. RR'); kc = st([krp], 'rpcnd', 'K e. CC')
    mlrp = st([mrp, st([st([lrp], 'rpred', 'L e. RR')], 'rpefcld', '( exp ` L ) e. RR+')], 'rpmulcld', '%s e. RR+' % ML)
    E1 = '( exp ` ( -u K / X ) )'; E2 = '( exp ` ( -u K / %s ) )' % ML; EZ = '( exp ` ( -u K / Z ) )'
    wl = st([mrp, xrp, lrp, knn, w.inst('z5wlow')], 'syl31anc', '( %s - %s ) <_ %s' % (E1, E2, WV('K')))
    Q = '( K / Z )'; P = '( K / X )'; B = '( Z / X )'
    qr = st([kr, zrp], 'rerpdivcld', '%s e. RR' % Q); pr = st([kr, xrp], 'rerpdivcld', '%s e. RR' % P); br = st([zr, xrp], 'rerpdivcld', '%s e. RR' % B)
    q1 = onele(w, ante, kr, zrp, st([zk], 'ltled', 'Z <_ K'), 'K', 'Z')
    zh = lin.linarith(w, ante, [zx], 'Z <_ ( X x. ( 1 / 2 ) )', leaves={'X': xr, 'Z': zr})
    bh = st([zh, st([zr, a1c(w, ante, 'halfre', '( 1 / 2 ) e. RR'), xrp], 'ledivmuld', '( %s <_ ( 1 / 2 ) <-> Z <_ ( X x. ( 1 / 2 ) ) )' % B)], 'mpbird', '%s <_ ( 1 / 2 )' % B)
    pq = st([kc, st([zrp], 'rpcnd', 'Z e. CC'), st([xrp], 'rpcnd', 'X e. CC'), st([zrp], 'rpne0d', 'Z =/= 0'), st([xrp], 'rpne0d', 'X =/= 0')], 'dmdcand',
            '( %s x. %s ) = %s' % (B, Q, P))
    lv = {Q: qr, P: pr, B: br}
    key = lin.nlinarith(w, ante, [q1, bh, pq], '( 1 / 2 ) <_ ( %s - %s )' % (Q, P), leaves=lv)
    nz = negdiv(w, ante, kc, zrp, 'Z'); nx = negdiv(w, ante, kc, xrp, 'X')
    az = st([st([kr], 'renegcld', '-u K e. RR'), zrp], 'rerpdivcld', '( -u K / Z ) e. RR')
    ax = st([st([kr], 'renegcld', '-u K e. RR'), xrp], 'rerpdivcld', '( -u K / X ) e. RR')
    lv2 = {Q: qr, P: pr, '( -u K / Z )': az, '( -u K / X )': ax}
    ex = lin.linarith(w, ante, [key, nz, nx], '( -u K / Z ) <_ ( -u ( 1 / 2 ) + ( -u K / X ) )', leaves=lv2)
    S = '( -u ( 1 / 2 ) + ( -u K / X ) )'
    sr = st([st([a1c(w, ante, 'halfre', '( 1 / 2 ) e. RR')], 'renegcld', '-u ( 1 / 2 ) e. RR'), ax], 'readdcld', '%s e. RR' % S)
    e3 = st([ex, sy2(w, ante, az, sr, 'efle', '( ( -u K / Z ) <_ %s <-> %s <_ ( exp ` %s ) )' % (S, EZ, S))], 'mpbid', '%s <_ ( exp ` %s )' % (EZ, S))
    H = '( exp ` -u ( 1 / 2 ) )'
    ea = sy2(w, ante, st([a1c(w, ante, 'halfcn', '( 1 / 2 ) e. CC')], 'negcld', '-u ( 1 / 2 ) e. CC'),
             st([ax], 'recnd', '( -u K / X ) e. CC'), 'efadd', '( exp ` %s ) = ( %s x. %s )' % (S, H, E1))
    e4 = st([e3, ea], 'breqtrd', '%s <_ ( %s x. %s )' % (EZ, H, E1))
    # E2 <_ EZ
    dz = st([mlrp, zrp, kr, st([krp], 'rpge0d', '0 <_ K'), mz], 'lediv2ad', '( K / Z ) <_ ( K / %s )' % ML)
    qm = st([kr, mlrp], 'rerpdivcld', '( K / %s ) e. RR' % ML)
    ng = st([dz, st([qr, qm], 'lenegd', '( ( K / Z ) <_ ( K / %s ) <-> -u ( K / %s ) <_ -u ( K / Z ) )' % (ML, ML))], 'mpbid', '-u ( K / %s ) <_ -u ( K / Z )' % ML)
    ng2 = st([ng, negdiv(w, ante, kc, mlrp, ML), nz], '3brtr3d', '( -u K / %s ) <_ ( -u K / Z )' % ML)
    am = st([st([kr], 'renegcld', '-u K e. RR'), mlrp], 'rerpdivcld', '( -u K / %s ) e. RR' % ML)
    e5 = st([ng2, sy2(w, ante, am, az, 'efle', '( ( -u K / %s ) <_ ( -u K / Z ) <-> %s <_ %s )' % (ML, E2, EZ))], 'mpbid', '%s <_ %s' % (E2, EZ))
    # e ^ ( - 1 / 2 ) <_ 2 / 3
    hh = st([a1c(w, ante, 'halfre', '( 1 / 2 ) e. RR'), a1c(w, ante, 'halfge0', '0 <_ ( 1 / 2 )'), w.inst('bvefge1p')], 'syl2anc',
            '( 1 + ( 1 / 2 ) ) <_ ( exp ` ( 1 / 2 ) )')
    EH = '( exp ` ( 1 / 2 ) )'
    ehrp = st([a1c(w, ante, 'halfre', '( 1 / 2 ) e. RR')], 'rpefcld', '%s e. RR+' % EH)
    en = sy(w, ante, a1c(w, ante, 'halfcn', '( 1 / 2 ) e. CC'), 'efneg', '%s = ( 1 / %s )' % (H, EH))
    c23 = lin.linarith(w, ante, [hh], '1 <_ ( %s x. ( 2 / 3 ) )' % EH, leaves={EH: st([ehrp], 'rpred', '%s e. RR' % EH)})
    r23 = st([c23, st([st([], '1red', '1 e. RR'), litr(w, ante, '( 2 / 3 )'), ehrp], 'ledivmuld', '( ( 1 / %s ) <_ ( 2 / 3 ) <-> 1 <_ ( %s x. ( 2 / 3 ) ) )' % (EH, EH))],
             'mpbird', '( 1 / %s ) <_ ( 2 / 3 )' % EH)
    h23 = st([en, r23], 'eqbrtrd', '%s <_ ( 2 / 3 )' % H)
    e1r = st([ax], 'reefcld', '%s e. RR' % E1)
    hr = st([st([a1c(w, ante, 'halfre', '( 1 / 2 ) e. RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'reefcld', '%s e. RR' % H)
    e6 = st([hr, litr(w, ante, '( 2 / 3 )'), e1r, st([st([ax], 'rpefcld', '%s e. RR+' % E1)], 'rpge0d', '0 <_ %s' % E1), h23], 'lemul1ad',
            '( %s x. %s ) <_ ( ( 2 / 3 ) x. %s )' % (H, E1, E1))
    ezr = st([az], 'reefcld', '%s e. RR' % EZ); e2r = st([am], 'reefcld', '%s e. RR' % E2)
    lv3 = {E1: e1r, E2: e2r, EZ: ezr, '( %s x. %s )' % (H, E1): st([hr, e1r], 'remulcld', '( %s x. %s ) e. RR' % (H, E1))}
    fin = lin.linarith(w, ante, [e5, e4, e6], '( ( 1 / 3 ) x. %s ) <_ ( %s - %s )' % (E1, E1, E2), leaves=lv3)
    wr = wvre(w, ante, mrp, xrp, lrp, knn)
    w.qed([st([litr(w, ante, '( 1 / 3 )'), e1r], 'remulcld', '( ( 1 / 3 ) x. %s ) e. RR' % E1), st([e1r, e2r], 'resubcld', '( %s - %s ) e. RR' % (E1, E2)), wr, fin, wl],
          'letrd', STATEMENTS['z5wthird'])
    return w


def z5fwin():
    w = W('z5fwin', "Lean frozen_window_hyps (GramFunction.lean 2829) for 1 < D, 2 <_ log D: 1 <_ z1 < z2, M0 e ^ ell <_ z1, 2 z1 <_ X at "
                    "z1 = D ^c ( 31 / 50 ), z2 = D ^c ( 63 / 100 ), M0 = D ^c ( 3 / 5 ), ell = log D / 100, X = D ^c ( 6 / 5 ).")
    ante = HZ2
    st = mkst(w, ante)
    dr = st([], 'simp1', 'D e. RR'); d1 = st([], 'simp2', '1 < D'); l2 = st([], 'simp3', '2 <_ ( log ` D )')
    drp = st([dr, lin.linarith(w, ante, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    LD = '( log ` D )'
    lr = st([drp], 'relogcld', '%s e. RR' % LD)
    l0 = lin.linarith(w, ante, [l2], '0 <_ %s' % LD, leaves={LD: lr})
    dc = st([dr], 'recnd', 'D e. CC'); dne = st([drp], 'rpne0d', 'D =/= 0')
    def cx(q):
        qr = litr(w, ante, q)
        e = st([dc, dne, st([qr], 'recnd', '%s e. CC' % q)], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (q, q, LD))
        ar = st([qr, lr], 'remulcld', '( %s x. %s ) e. RR' % (q, LD))
        return e, qr, ar
    C29 = '( ; 2 9 / ; 5 0 )'
    ez, zq, za = cx(C31); em, mq, ma = cx('( 3 / 5 )'); e29, q29, a29 = cx(C29)
    # 1 <_ z1
    g1 = st([za, lin.linarith(w, ante, [l0], '0 <_ ( %s x. %s )' % (C31, LD), leaves={LD: lr}), w.inst('bvefge1p')], 'syl2anc',
            '( 1 + ( %s x. %s ) ) <_ ( exp ` ( %s x. %s ) )' % (C31, LD, C31, LD))
    EZ = '( exp ` ( %s x. %s ) )' % (C31, LD)
    ezr = st([za], 'reefcld', '%s e. RR' % EZ)
    i1 = lin.linarith(w, ante, [g1, l0], '1 <_ %s' % EZ, leaves={LD: lr, EZ: ezr})
    c1 = st([i1, ez], 'breqtrrd', '1 <_ %s' % Z1)
    c2 = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1, Z2, Z1, Z2))
    c2 = st([c2], 'simp3d', '%s < %s' % (Z1, Z2))
    # M0 e ^ ell <_ z1
    SM = '( ( ( 3 / 5 ) x. %s ) + %s )' % (LD, ELLD)
    ellr = st([litr(w, ante, '( 1 / ; ; 1 0 0 )'), lr], 'remulcld', '%s e. RR' % ELLD)
    fa = sy2(w, ante, st([ma], 'recnd', '( ( 3 / 5 ) x. %s ) e. CC' % LD), st([ellr], 'recnd', '%s e. CC' % ELLD), 'efadd',
             '( exp ` %s ) = ( ( exp ` ( ( 3 / 5 ) x. %s ) ) x. ( exp ` %s ) )' % (SM, LD, ELLD))
    m1 = st([st([em], 'oveq1d', '( %s x. ( exp ` %s ) ) = ( ( exp ` ( ( 3 / 5 ) x. %s ) ) x. ( exp ` %s ) )' % (M0, ELLD, LD, ELLD)), fa], 'eqtr4d',
            '( %s x. ( exp ` %s ) ) = ( exp ` %s )' % (M0, ELLD, SM))
    sr = st([ma, ellr], 'readdcld', '%s e. RR' % SM)
    le = lin.linarith(w, ante, [l0], '%s <_ ( %s x. %s )' % (SM, C31, LD), leaves={LD: lr})
    m2 = st([le, sy2(w, ante, sr, za, 'efle', '( %s <_ ( %s x. %s ) <-> ( exp ` %s ) <_ %s )' % (SM, C31, LD, SM, EZ))], 'mpbid', '( exp ` %s ) <_ %s' % (SM, EZ))
    c3 = st([m1, st([m2, ez], 'breqtrrd', '( exp ` %s ) <_ %s' % (SM, Z1))], 'eqbrtrd', '( %s x. ( exp ` %s ) ) <_ %s' % (M0, ELLD, Z1))
    # 2 z1 <_ X
    Y = '( D ^c %s )' % C29
    E29 = '( exp ` ( %s x. %s ) )' % (C29, LD)
    g2 = st([a29, lin.linarith(w, ante, [l0], '0 <_ ( %s x. %s )' % (C29, LD), leaves={LD: lr}), w.inst('bvefge1p')], 'syl2anc',
            '( 1 + ( %s x. %s ) ) <_ %s' % (C29, LD, E29))
    e29r = st([a29], 'reefcld', '%s e. RR' % E29)
    t2 = lin.linarith(w, ante, [g2, l2], '2 <_ %s' % E29, leaves={LD: lr, E29: e29r})
    y2 = st([t2, e29], 'breqtrrd', '2 <_ %s' % Y)
    z1rp = st([drp, zq], 'rpcxpcld', '%s e. RR+' % Z1)
    yr = st([st([drp, q29], 'rpcxpcld', '%s e. RR+' % Y)], 'rpred', '%s e. RR' % Y)
    mm = st([a1c(w, ante, '2re', '2 e. RR'), yr, st([z1rp], 'rpred', '%s e. RR' % Z1), st([z1rp], 'rpge0d', '0 <_ %s' % Z1), y2], 'lemul1ad',
            '( 2 x. %s ) <_ ( %s x. %s )' % (Z1, Y, Z1))
    ad = st([dc, dne, st([q29], 'recnd', '%s e. CC' % C29), st([zq], 'recnd', '%s e. CC' % C31)], 'cxpaddd', '( D ^c ( %s + %s ) ) = ( %s x. %s )' % (C29, C31, Y, Z1))
    sx = lin.lineq(w, ante, '( %s + %s )' % (C29, C31), '( 6 / 5 )')
    xe = st([st([sx], 'oveq2d', '( D ^c ( %s + %s ) ) = %s' % (C29, C31, XP)), ad], 'eqtr3d', '%s = ( %s x. %s )' % (XP, Y, Z1))
    c4 = st([mm, xe], 'breqtrrd', '( 2 x. %s ) <_ %s' % (Z1, XP))
    w.qed([st([c1, c2], 'jca', '( 1 <_ %s /\\ %s < %s )' % (Z1, Z1, Z2)), st([c3, c4], 'jca', '( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s )' % (M0, ELLD, Z1, Z1, XP))],
          'jca', STATEMENTS['z5fwin'])
    return w


if __name__ == '__main__':
    import z5alib
    for f in sys.argv[1:]:
        z5alib.run(globals()[f]())
