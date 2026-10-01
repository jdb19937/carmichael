"""Sortie z4d, section A: indicator integrals over RR (lsind, lswpairlem, lswpair, lswint)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
import lin
lin.FASTPATH = True
from lin import linarith, lineq
from z4dlib import STATEMENTS as S, HYPS, ICC, TRI, ITG


def mk(w, a):
    return lambda hyps, ref, g, name=None: w.s(hyps, ref, '( %s -> %s )' % (a, g), name=name)


def a1(w, ante, ref, fact, hyps=()):
    return w.s([w.s(list(hyps), ref, fact)], 'a1i', '( %s -> %s )' % (ante, fact))


def hyps(w, lab):
    out = {}
    for n, f in HYPS[lab]:
        w.s([], '%s.%s' % (lab, n), f, name='h' + n)
        out[n] = n
    return out


def indint(w, ante, ure, vre, kc, U, V, K, u='u'):
    """( ante -> ( ( u e. RR |-> if ( u e. [U,V] , K , 0 ) ) e. L^1 /\\ S. RR ... = ( K x. if ( U <_ V , ( V - U ) , 0 ) ) ) )
    by lsind"""
    I = ICC(U, V)
    IF = 'if ( %s e. %s , %s , 0 )' % (u, I, K)
    c = '( ( %s e. RR |-> %s ) e. L^1 /\\ %s = ( %s x. if ( %s <_ %s , ( %s - %s ) , 0 ) ) )' % (
        u, IF, ITG('RR', IF, u), K, U, V, V, U)
    return w.s([ure, vre, kc, w.inst('lsind')], 'syl3anc', '( %s -> %s )' % (ante, c))


def lsind():
    w = W('lsind', 'The integral over RR of a constant times the indicator of a closed interval '
          '(Lean integral_indicator_const with volume_Icc), with its integrability.')
    AA = '( U e. RR /\\ V e. RR /\\ K e. CC )'
    s = mk(w, AA)
    I = ICC('U', 'V')
    IF = 'if ( u e. %s , K , 0 )' % I
    VOL = 'if ( U <_ V , ( V - U ) , 0 )'
    ure = s([], 'simp1', 'U e. RR')
    vre = s([], 'simp2', 'V e. RR')
    kc = s([], 'simp3', 'K e. CC')
    iss = s([ure, vre, w.inst('iccssre')], 'syl2anc', '%s C_ RR' % I)
    imbl = s([ure, vre, w.inst('iccmbl')], 'syl2anc', '%s e. dom vol' % I)
    # the volume
    A1 = '( %s /\\ U <_ V )' % AA
    t = mk(w, A1)
    v1 = t([t([ure], 'adantr', 'U e. RR'), t([vre], 'adantr', 'V e. RR'), t([], 'simpr', 'U <_ V'),
            w.inst('ovolicc')], 'syl3anc', '( vol* ` %s ) = ( V - U )' % I)
    i1 = t([t([], 'simpr', 'U <_ V'), w.inst('iftrue')], 'syl', '%s = ( V - U )' % VOL)
    b1 = t([v1, i1], 'eqtr4d', '( vol* ` %s ) = %s' % (I, VOL))
    A2 = '( %s /\\ -. U <_ V )' % AA
    f = mk(w, A2)
    ure2 = f([ure], 'adantr', 'U e. RR')
    vre2 = f([vre], 'adantr', 'V e. RR')
    vu = f([f([vre2, ure2], 'ltnled', '( V < U <-> -. U <_ V )'), f([], 'simpr', '-. U <_ V')], 'mpbird', 'V < U')
    e0 = f([f([f([ure2], 'rexrd', 'U e. RR*'), f([vre2], 'rexrd', 'V e. RR*'), w.inst('icc0')], 'syl2anc',
              '( %s = (/) <-> V < U )' % I), vu], 'mpbird', '%s = (/)' % I)
    v0 = f([f([e0], 'fveq2d', '( vol* ` %s ) = ( vol* ` (/) )' % I), a1(w, A2, 'ovol0', '( vol* ` (/) ) = 0')],
           'eqtrd', '( vol* ` %s ) = 0' % I)
    i0 = f([f([], 'simpr', '-. U <_ V'), w.inst('iffalse')], 'syl', '%s = 0' % VOL)
    b0 = f([v0, i0], 'eqtr4d', '( vol* ` %s ) = %s' % (I, VOL))
    vols = s([b1, b0], 'pm2.61dan', '( vol* ` %s ) = %s' % (I, VOL))
    vol = s([s([imbl, w.inst('mblvol')], 'syl', '( vol ` %s ) = ( vol* ` %s )' % (I, I)), vols], 'eqtrd',
            '( vol ` %s ) = %s' % (I, VOL))
    volre = s([vol, s([s([vre, ure], 'resubcld', '( V - U ) e. RR'), s([], '0red', '0 e. RR')], 'ifcld',
                      '%s e. RR' % VOL)], 'eqeltrd', '( vol ` %s ) e. RR' % I)
    # the integral
    ss2 = s([iss, w.inst('itgss2')], 'syl', '%s = %s' % (ITG(I, 'K', 'u'), ITG('RR', IF, 'u')))
    ic = s([imbl, volre, kc, w.inst('itgconst')], 'syl3anc', '%s = ( K x. ( vol ` %s ) )' % (ITG(I, 'K', 'u'), I))
    val = s([ss2, ic], 'eqtr3d', '%s = ( K x. ( vol ` %s ) )' % (ITG('RR', IF, 'u'), I))
    val2 = s([val, s([vol], 'oveq2d', '( K x. ( vol ` %s ) ) = ( K x. %s )' % (I, VOL))], 'eqtrd',
             '%s = ( K x. %s )' % (ITG('RR', IF, 'u'), VOL))
    # integrability
    ib0 = s([imbl, volre, kc, w.inst('iblconst')], 'syl3anc', '( %s X. { K } ) e. L^1' % I)
    fc = a1(w, AA, 'fconstmpt', '( %s X. { K } ) = ( u e. %s |-> K )' % (I, I))
    ib1 = s([fc, ib0], 'eqeltrrd', '( u e. %s |-> K ) e. L^1' % I)
    mt = w.s([w.s([], 'iftrue', '( u e. %s -> %s = K )' % (I, IF))], 'mpteq2ia',
             '( u e. %s |-> %s ) = ( u e. %s |-> K )' % (I, IF, I))
    ib2 = s([s([mt], 'a1i', '( u e. %s |-> %s ) = ( u e. %s |-> K )' % (I, IF, I)), ib1], 'eqeltrd',
            '( u e. %s |-> %s ) e. L^1' % (I, IF))
    AU = '( %s /\\ u e. %s )' % (AA, I)
    g = mk(w, AU)
    h3 = g([g([kc], 'adantr', 'K e. CC'), g([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF)
    AD = '( %s /\\ u e. ( RR \\ %s ) )' % (AA, I)
    d = mk(w, AD)
    h4 = d([d([d([], 'simpr', 'u e. ( RR \\ %s )' % I), w.inst('eldifn')], 'syl', '-. u e. %s' % I),
            w.inst('iffalse')], 'syl', '%s = 0' % IF)
    ib = s([iss, a1(w, AA, 'rembl', 'RR e. dom vol'), h3, h4, ib2], 'iblss2', '( u e. RR |-> %s ) e. L^1' % IF)
    w.qed([ib, val2], 'jca', S['lsind'])
    return w


def absint(w, B, ure, xre, hre, X, H, u='u'):
    """( B -> ( ( abs ` ( X - u ) ) <_ H <-> ( ( X - H ) <_ u /\\ u <_ ( X + H ) ) ) )"""
    s = mk(w, B)
    e = s([s([xre], 'recnd', '%s e. CC' % X), s([ure], 'recnd', '%s e. CC' % u), w.inst('abssub')], 'syl2anc',
          '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (X, u, u, X))
    b1 = s([e], 'breq1d', '( ( abs ` ( %s - %s ) ) <_ %s <-> ( abs ` ( %s - %s ) ) <_ %s )' % (X, u, H, u, X, H))
    b2 = s([ure, xre, hre, w.inst('absdifle')], 'syl3anc',
           '( ( abs ` ( %s - %s ) ) <_ %s <-> ( ( %s - %s ) <_ %s /\\ %s <_ ( %s + %s ) ) )' % (u, X, H, X, H, u, u, X, H))
    return s([b1, b2], 'bitrd', '( ( abs ` ( %s - %s ) ) <_ %s <-> ( ( %s - %s ) <_ %s /\\ %s <_ ( %s + %s ) ) )'
             % (X, u, H, X, H, u, u, X, H))


def lswpairlem():
    w = W('lswpairlem', 'For X <_ Y the pair of windows of half-width H around X and Y meet in '
          '[ Y - H , X + H ], whose length is TRI ( 2 H , X - Y ) (Lean tri_bilinear_eq hprod, hvol, tri_mul_eq).')
    A0 = '( ( X e. RR /\\ Y e. RR /\\ X <_ Y ) /\\ ( H e. RR+ /\\ K e. CC ) )'
    s = mk(w, A0)
    xre = s([], 'simpl1', 'X e. RR')
    yre = s([], 'simpl2', 'Y e. RR')
    xy = s([], 'simpl3', 'X <_ Y')
    hrp = s([], 'simprl', 'H e. RR+')
    hre = s([hrp], 'rpred', 'H e. RR')
    kc = s([], 'simprr', 'K e. CC')
    U = '( Y - H )'; V = '( X + H )'
    I = ICC(U, V)
    ure0 = s([yre, hre], 'resubcld', '%s e. RR' % U)
    vre0 = s([xre, hre], 'readdcld', '%s e. RR' % V)
    B = '( %s /\\ u e. RR )' % A0
    b = mk(w, B)
    ure = b([], 'simpr', 'u e. RR')
    bx = b([xre], 'adantr', 'X e. RR'); by = b([yre], 'adantr', 'Y e. RR'); bh = b([hre], 'adantr', 'H e. RR')
    bxy = b([xy], 'adantr', 'X <_ Y')
    ax = absint(w, B, ure, bx, bh, 'X', 'H')
    ay = absint(w, B, ure, by, bh, 'Y', 'H')
    a1_, a2_ = '( X - H ) <_ u', 'u <_ ( X + H )'
    b1_, b2_ = '( Y - H ) <_ u', 'u <_ ( Y + H )'
    BIG = '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (a1_, a2_, b1_, b2_)
    SM = '( %s /\\ %s )' % (b1_, a2_)
    P1 = '( ( abs ` ( X - u ) ) <_ H /\\ ( abs ` ( Y - u ) ) <_ H )'
    p1 = b([ax, ay], 'anbi12d', '( %s <-> %s )' % (P1, BIG))
    BF = '( %s /\\ %s )' % (B, BIG)
    f = mk(w, BF)
    big = f([], 'simpr', BIG)
    fw = f([f([f([big], 'simprd', '( %s /\\ %s )' % (b1_, b2_))], 'simpld', b1_),
            f([f([big], 'simpld', '( %s /\\ %s )' % (a1_, a2_))], 'simprd', a2_)], 'jca', SM)
    BS = '( %s /\\ %s )' % (B, SM)
    g = mk(w, BS)
    gb1 = g([], 'simprl', b1_)
    ga2 = g([], 'simprr', a2_)
    lv = {'X': g([bx], 'adantr', 'X e. RR'), 'Y': g([by], 'adantr', 'Y e. RR'), 'H': g([bh], 'adantr', 'H e. RR'),
          'u': g([ure], 'adantr', 'u e. RR')}
    gxy = g([bxy], 'adantr', 'X <_ Y')
    ga1 = linarith(w, BS, [gb1, gxy], a1_, leaves=lv)
    gb2 = linarith(w, BS, [ga2, gxy], b2_, leaves=lv)
    bw = g([g([ga1, ga2], 'jca', '( %s /\\ %s )' % (a1_, a2_)), g([gb1, gb2], 'jca', '( %s /\\ %s )' % (b1_, b2_))],
           'jca', BIG)
    mid = b([fw, bw], 'impbida', '( %s <-> %s )' % (BIG, SM))
    el = b([b([ure0], 'adantr', '%s e. RR' % U), b([vre0], 'adantr', '%s e. RR' % V), w.inst('elicc2')], 'syl2anc',
           '( u e. %s <-> ( u e. RR /\\ %s /\\ %s ) )' % (I, b1_, a2_))
    el2 = b([el, w.s([], '3anass', '( ( u e. RR /\\ %s /\\ %s ) <-> ( u e. RR /\\ %s ) )' % (b1_, a2_, SM))], 'bitrdi',
            '( u e. %s <-> ( u e. RR /\\ %s ) )' % (I, SM))
    ba = b([ure], 'biantrurd', '( %s <-> ( u e. RR /\\ %s ) )' % (SM, SM))
    p2 = b([el2, ba], 'bitr4d', '( u e. %s <-> %s )' % (I, SM))
    cond = b([b([p1, mid], 'bitrd', '( %s <-> %s )' % (P1, SM)), p2], 'bitr4d', '( %s <-> u e. %s )' % (P1, I))
    PAIR = 'if ( %s , K , 0 )' % P1
    IF = 'if ( u e. %s , K , 0 )' % I
    ifq = b([cond], 'ifbid', '%s = %s' % (PAIR, IF))
    mq = s([ifq], 'mpteq2dva', '( u e. RR |-> %s ) = ( u e. RR |-> %s )' % (PAIR, IF))
    iq = s([ifq], 'itgeq2dv', '%s = %s' % (ITG('RR', PAIR, 'u'), ITG('RR', IF, 'u')))
    VOL = 'if ( %s <_ %s , ( %s - %s ) , 0 )' % (U, V, V, U)
    ind = indint(w, A0, ure0, vre0, kc, U, V, 'K')
    ib = s([mq, s([ind], 'simpld', '( u e. RR |-> %s ) e. L^1' % IF)], 'eqeltrd', '( u e. RR |-> %s ) e. L^1' % PAIR)
    iv = s([iq, s([ind], 'simprd', '%s = ( K x. %s )' % (ITG('RR', IF, 'u'), VOL))], 'eqtrd',
           '%s = ( K x. %s )' % (ITG('RR', PAIR, 'u'), VOL))
    # VOL = TRI ( 2 H , X - Y )
    AB = '( abs ` ( X - Y ) )'
    H2 = '( 2 x. H )'
    ab = s([xre, yre, xy, w.inst('abssuble0')], 'syl3anc', '%s = ( Y - X )' % AB)
    abre = s([s([s([xre, yre], 'resubcld', '( X - Y ) e. RR')], 'recnd', '( X - Y ) e. CC')], 'abscld', '%s e. RR' % AB)
    lv0 = {'X': xre, 'Y': yre, 'H': hre, AB: abre}
    C1 = '( %s /\\ %s <_ %s )' % (A0, U, V)
    c1 = mk(w, C1)
    lv1 = {k: c1([v], 'adantr', '%s e. RR' % k) for k, v in lv0.items()}
    d1 = linarith(w, C1, [c1([], 'simpr', '%s <_ %s' % (U, V)), c1([ab], 'adantr', '%s = ( Y - X )' % AB)],
                  '%s <_ %s' % (AB, H2), leaves=lv1)
    C2 = '( %s /\\ %s <_ %s )' % (A0, AB, H2)
    c2 = mk(w, C2)
    lv2 = {k: c2([v], 'adantr', '%s e. RR' % k) for k, v in lv0.items()}
    d2 = linarith(w, C2, [c2([], 'simpr', '%s <_ %s' % (AB, H2)), c2([ab], 'adantr', '%s = ( Y - X )' % AB)],
                  '%s <_ %s' % (U, V), leaves=lv2)
    cb = s([d1, d2], 'impbida', '( %s <_ %s <-> %s <_ %s )' % (U, V, AB, H2))
    vq = lineq(w, A0, '( %s - %s )' % (V, U), '( %s - %s )' % (H2, AB), hyps=[ab], leaves=lv0)
    tri = s([cb, vq, s([], 'eqidd', '0 = 0')], 'ifbieq12d', '%s = %s' % (VOL, TRI(H2, '( X - Y )')))
    iv2 = s([iv, s([tri], 'oveq2d', '( K x. %s ) = ( K x. %s )' % (VOL, TRI(H2, '( X - Y )')))], 'eqtrd',
            '%s = ( K x. %s )' % (ITG('RR', PAIR, 'u'), TRI(H2, '( X - Y )')))
    w.qed([ib, iv2], 'jca', S['lswpairlem'])
    return w


def lswpair():
    w = W('lswpair', 'The pair of windows of half-width H around X and Y overlaps in length TRI ( 2 H , X - Y ) '
          '(both orders of X, Y from lswpairlem).')
    A0 = '( ( X e. RR /\\ Y e. RR ) /\\ ( H e. RR+ /\\ K e. CC ) )'
    s = mk(w, A0)
    xre = s([], 'simpll', 'X e. RR')
    yre = s([], 'simplr', 'Y e. RR')
    hk = s([], 'simpr', '( H e. RR+ /\\ K e. CC )')
    H2 = '( 2 x. H )'
    P1 = '( ( abs ` ( X - u ) ) <_ H /\\ ( abs ` ( Y - u ) ) <_ H )'
    P2 = '( ( abs ` ( Y - u ) ) <_ H /\\ ( abs ` ( X - u ) ) <_ H )'
    PAIR = 'if ( %s , K , 0 )' % P1
    PAIR2 = 'if ( %s , K , 0 )' % P2
    GOAL = S['lswpair'].split(' -> ', 1)[1][:-2]
    C1 = '( %s /\\ X <_ Y )' % A0
    c = mk(w, C1)
    h1 = c([c([c([xre], 'adantr', 'X e. RR'), c([yre], 'adantr', 'Y e. RR'), c([], 'simpr', 'X <_ Y')], '3jca',
              '( X e. RR /\\ Y e. RR /\\ X <_ Y )'), c([hk], 'adantr', '( H e. RR+ /\\ K e. CC )')], 'jca',
           '( ( X e. RR /\\ Y e. RR /\\ X <_ Y ) /\\ ( H e. RR+ /\\ K e. CC ) )')
    r1 = c([h1, w.inst('lswpairlem')], 'syl', GOAL)
    C2 = '( %s /\\ Y <_ X )' % A0
    d = mk(w, C2)
    h2 = d([d([d([yre], 'adantr', 'Y e. RR'), d([xre], 'adantr', 'X e. RR'), d([], 'simpr', 'Y <_ X')], '3jca',
              '( Y e. RR /\\ X e. RR /\\ Y <_ X )'), d([hk], 'adantr', '( H e. RR+ /\\ K e. CC )')], 'jca',
           '( ( Y e. RR /\\ X e. RR /\\ Y <_ X ) /\\ ( H e. RR+ /\\ K e. CC ) )')
    G2 = '( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( K x. %s ) )' % (PAIR2, ITG('RR', PAIR2, 'u'), TRI(H2, '( Y - X )'))
    r2 = d([h2, w.inst('lswpairlem')], 'syl', G2)
    pq = w.s([w.s([], 'ancom', '( %s <-> %s )' % (P2, P1)), w.inst('ifbi')], 'ax-mp', '%s = %s' % (PAIR2, PAIR))
    pqd = d([pq], 'a1i', '%s = %s' % (PAIR2, PAIR))
    D2 = '( %s /\\ u e. RR )' % C2
    mq = d([w.s([pq], 'a1i', '( %s -> %s = %s )' % (D2, PAIR2, PAIR))], 'mpteq2dva',
           '( u e. RR |-> %s ) = ( u e. RR |-> %s )' % (PAIR2, PAIR))
    iq = d([w.s([pq], 'a1i', '( %s -> %s = %s )' % (D2, PAIR2, PAIR))], 'itgeq2dv',
           '%s = %s' % (ITG('RR', PAIR2, 'u'), ITG('RR', PAIR, 'u')))
    ab = d([d([d([yre], 'adantr', 'Y e. RR')], 'recnd', 'Y e. CC'), d([d([xre], 'adantr', 'X e. RR')], 'recnd', 'X e. CC'),
            w.inst('abssub')], 'syl2anc', '( abs ` ( Y - X ) ) = ( abs ` ( X - Y ) )')
    tq = d([d([ab], 'breq1d', '( ( abs ` ( Y - X ) ) <_ %s <-> ( abs ` ( X - Y ) ) <_ %s )' % (H2, H2)),
            d([ab], 'oveq2d', '( %s - ( abs ` ( Y - X ) ) ) = ( %s - ( abs ` ( X - Y ) ) )' % (H2, H2)),
            d([], 'eqidd', '0 = 0')], 'ifbieq12d', '%s = %s' % (TRI(H2, '( Y - X )'), TRI(H2, '( X - Y )')))
    ib = d([mq, d([r2], 'simpld', '( u e. RR |-> %s ) e. L^1' % PAIR2)], 'eqeltrrd', '( u e. RR |-> %s ) e. L^1' % PAIR)
    iv = d([iq, d([d([r2], 'simprd', '%s = ( K x. %s )' % (ITG('RR', PAIR2, 'u'), TRI(H2, '( Y - X )'))),
                   d([tq], 'oveq2d', '( K x. %s ) = ( K x. %s )' % (TRI(H2, '( Y - X )'), TRI(H2, '( X - Y )')))],
                  'eqtrd', '%s = ( K x. %s )' % (ITG('RR', PAIR2, 'u'), TRI(H2, '( X - Y )')))], 'eqtr3d',
           '%s = ( K x. %s )' % (ITG('RR', PAIR, 'u'), TRI(H2, '( X - Y )')))
    r2b = d([ib, iv], 'jca', GOAL)
    w.qed([xre, yre, r1, r2b], 'lecasei', S['lswpair'])
    return w


def wincond(w, B, ure, lre, hre, Lx, H, u='u'):
    """( B -> ( ( abs ` ( L - u ) ) <_ H <-> u e. ( ( L - H ) [,] ( L + H ) ) ) )"""
    b = mk(w, B)
    U = '( %s - %s )' % (Lx, H); V = '( %s + %s )' % (Lx, H)
    I = ICC(U, V)
    ax = absint(w, B, ure, lre, hre, Lx, H, u)
    c1, c2 = '%s <_ %s' % (U, u), '%s <_ %s' % (u, V)
    SM = '( %s /\\ %s )' % (c1, c2)
    el = b([b([lre, hre], 'resubcld', '%s e. RR' % U), b([lre, hre], 'readdcld', '%s e. RR' % V), w.inst('elicc2')],
           'syl2anc', '( %s e. %s <-> ( %s e. RR /\\ %s /\\ %s ) )' % (u, I, u, c1, c2))
    el2 = b([el, w.s([], '3anass', '( ( %s e. RR /\\ %s /\\ %s ) <-> ( %s e. RR /\\ %s ) )' % (u, c1, c2, u, SM))],
            'bitrdi', '( %s e. %s <-> ( %s e. RR /\\ %s ) )' % (u, I, u, SM))
    ba = b([ure], 'biantrurd', '( %s <-> ( %s e. RR /\\ %s ) )' % (SM, u, SM))
    p2 = b([el2, ba], 'bitr4d', '( %s e. %s <-> %s )' % (u, I, SM))
    return b([ax, p2], 'bitr4d', '( ( abs ` ( %s - %s ) ) <_ %s <-> %s e. %s )' % (Lx, u, H, u, I))


def lswint():
    w = W('lswint', 'A finite sum of window indicators of half-width H integrates over RR to 2 H times the sum '
          'of the weights (Lean integral_window_weight, window_sum_integrable).')
    h = hyps(w, 'lswint')
    s = mk(w, 'ph')
    WIF = 'if ( ( abs ` ( L - u ) ) <_ H , G , 0 )'
    WI = 'sum_ i e. P %s' % WIF
    hre = s([h['4']], 'rpred', 'H e. RR')
    C = '( ph /\\ i e. P )'
    c = mk(w, C)
    chre = c([hre], 'adantr', 'H e. RR')
    U = '( L - H )'; V = '( L + H )'
    I = ICC(U, V)
    IF = 'if ( u e. %s , G , 0 )' % I
    B = '( %s /\\ u e. RR )' % C
    b = mk(w, B)
    cond = wincond(w, B, b([], 'simpr', 'u e. RR'), b([h['2']], 'adantr', 'L e. RR'), b([chre], 'adantr', 'H e. RR'),
                   'L', 'H')
    ifq = b([cond], 'ifbid', '%s = %s' % (WIF, IF))
    mq = c([ifq], 'mpteq2dva', '( u e. RR |-> %s ) = ( u e. RR |-> %s )' % (WIF, IF))
    iq = c([ifq], 'itgeq2dv', '%s = %s' % (ITG('RR', WIF, 'u'), ITG('RR', IF, 'u')))
    ure0 = c([h['2'], chre], 'resubcld', '%s e. RR' % U)
    vre0 = c([h['2'], chre], 'readdcld', '%s e. RR' % V)
    ind = indint(w, C, ure0, vre0, h['3'], U, V, 'G')
    VOL = 'if ( %s <_ %s , ( %s - %s ) , 0 )' % (U, V, V, U)
    ib = c([mq, c([ind], 'simpld', '( u e. RR |-> %s ) e. L^1' % IF)], 'eqeltrd', '( u e. RR |-> %s ) e. L^1' % WIF)
    iv = c([iq, c([ind], 'simprd', '%s = ( G x. %s )' % (ITG('RR', IF, 'u'), VOL))], 'eqtrd',
           '%s = ( G x. %s )' % (ITG('RR', WIF, 'u'), VOL))
    lv = {'L': h['2'], 'H': chre}
    hge = c([c([h['4']], 'adantr', 'H e. RR+')], 'rpge0d', '0 <_ H')
    uv = linarith(w, C, [hge], '%s <_ %s' % (U, V), leaves=lv)
    vt = c([uv, w.inst('iftrue')], 'syl', '%s = ( %s - %s )' % (VOL, V, U))
    v2 = lineq(w, C, '( %s - %s )' % (V, U), '( 2 x. H )', leaves=lv)
    iv2 = c([iv, c([c([vt, v2], 'eqtrd', '%s = ( 2 x. H )' % VOL)], 'oveq2d', '( G x. %s ) = ( G x. ( 2 x. H ) )' % VOL)],
            'eqtrd', '%s = ( G x. ( 2 x. H ) )' % ITG('RR', WIF, 'u'))
    D = '( ph /\\ ( u e. RR /\\ i e. P ) )'
    h3 = w.s([w.s([h['3']], 'adantrl', '( %s -> G e. CC )' % D), w.s([], '0cnd', '( %s -> 0 e. CC )' % D)], 'ifcld',
             '( %s -> %s e. CC )' % (D, WIF))
    fs = s([s([], 'rembl', 'RR e. dom vol') if False else w.s([w.s([], 'rembl', 'RR e. dom vol')], 'a1i', '( ph -> RR e. dom vol )'),
            h['1'], h3, ib], 'itgfsum', '( ( u e. RR |-> %s ) e. L^1 /\\ %s = sum_ i e. P %s )' % (WI, ITG('RR', WI, 'u'), ITG('RR', WIF, 'u')))
    H2 = '( 2 x. H )'
    sq = s([iv2], 'sumeq2dv', 'sum_ i e. P %s = sum_ i e. P ( G x. %s )' % (ITG('RR', WIF, 'u'), H2))
    h2c = s([s([s([], '2re', '2 e. RR') if False else w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( ph -> 2 e. RR )'), hre],
               'remulcld', '%s e. RR' % H2)], 'recnd', '%s e. CC' % H2)
    mc = s([h['1'], h2c, h['3']], 'fsummulc1', '( sum_ i e. P G x. %s ) = sum_ i e. P ( G x. %s )' % (H2, H2))
    sg = s([h['1'], h['3']], 'fsumcl', 'sum_ i e. P G e. CC')
    val = s([s([s([fs], 'simprd', '%s = sum_ i e. P %s' % (ITG('RR', WI, 'u'), ITG('RR', WIF, 'u'))), sq], 'eqtrd',
               '%s = sum_ i e. P ( G x. %s )' % (ITG('RR', WI, 'u'), H2)),
             s([mc, s([sg, h2c], 'mulcomd', '( sum_ i e. P G x. %s ) = ( %s x. sum_ i e. P G )' % (H2, H2))], 'eqtr3d',
               'sum_ i e. P ( G x. %s ) = ( %s x. sum_ i e. P G )' % (H2, H2))], 'eqtrd',
            '%s = ( %s x. sum_ i e. P G )' % (ITG('RR', WI, 'u'), H2))
    w.qed([s([fs], 'simpld', '( u e. RR |-> %s ) e. L^1' % WI), val], 'jca', S['lswint'])
    return w


ALL = {'lswint': lswint, 'lswpair': lswpair, 'lsind': lsind, 'lswpairlem': lswpairlem}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
