"""T1: the accumulating word-recursion rule --- the induction every mover
fragment of the machine layer runs on (Lean's `moveNum_loop`, `move2Num_loop`,
`incLoop_loop`, `predLoop_loop`, and the machine model's `revrun`)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

CFGT = CFG('T')
TL = lambda x: '( %s substr <. 1 , ( # ` %s ) >. )' % (x, x)
AC = lambda x, y: '( <" ( %s ` 0 ) "> ++ %s )' % (x, y)


def TRI2(x, y):
    return HR('( J ` <. %s , %s >. )' % (x, y), 'T', 'M',
              '( J ` <. %s , %s >. )' % (TL(x), AC(x, y)), 'P')


HYP2 = 'A. x e. Word B A. s e. Word B ( x =/= (/) -> %s )' % TRI2('x', 's')
ZC = 'A. s e. Word B ( J ` <. (/) , s >. ) C_ %s' % CFGT
ANT2 = '( %s /\\ ( P e. NN0 /\\ %s ) /\\ %s )' % (PHM, ZC, HYP2)
REV = lambda b, d: '( ( reverse ` %s ) ++ %s )' % (b, d)


def CON2(b, d, n):
    return HR('( J ` <. %s , %s >. )' % (b, d), 'T', 'M',
              '( J ` <. (/) , %s >. )' % REV(b, d), '( %s x. P )' % n)


def PSI2(n):
    return ('( %s -> A. b e. Word B A. d e. Word B ( ( # ` b ) = %s -> %s ) )'
            % (ANT2, n, CON2('b', 'd', n)))


def zcat(w, ph, zc, Y, ycl):
    """( ph -> ( J ` <. (/) , Y >. ) C_ Cfg ) from ZC at y := Y"""
    s1 = w.s([], 'opeq2', '( s = %s -> <. (/) , s >. = <. (/) , %s >. )' % (Y, Y))
    s2 = w.s([s1], 'fveq2d', '( s = %s -> ( J ` <. (/) , s >. ) = ( J ` <. (/) , %s >. ) )' % (Y, Y))
    s3 = w.s([s2], 'sseq1d', '( s = %s -> ( ( J ` <. (/) , s >. ) C_ %s <-> ( J ` <. (/) , %s >. ) C_ %s ) )'
             % (Y, CFGT, Y, CFGT))
    return w.s([s3, zc, ycl], 'rspcdva', '( %s -> ( J ` <. (/) , %s >. ) C_ %s )' % (ph, Y, CFGT))


def tm2hwr20():
    lab = 'tm2hwr20'
    ph2 = '( ( %s /\\ b e. Word B ) /\\ d e. Word B )' % ANT2
    ph3 = '( %s /\\ ( # ` b ) = 0 )' % ph2
    JD = '( J ` <. (/) , d >. )'
    w = W(lab, 'The base case of the accumulating word-recursion rule of the '
               'machine layer: the empty word needs no steps and leaves the '
               'accumulator alone.')
    ant = w.s([], 'simplll', '( %s -> %s )' % (ph3, ANT2))
    phm = w.s([ant, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph3, PHM))
    pn = w.s([ant, w.inst('simp2l')], 'syl', '( %s -> P e. NN0 )' % ph3)
    zc = w.s([ant, w.inst('simp2r')], 'syl', '( %s -> %s )' % (ph3, ZC))
    bw = w.s([], 'simpllr', '( %s -> b e. Word B )' % ph3)
    dw = w.s([], 'simplr', '( %s -> d e. Word B )' % ph3)
    h0 = w.s([], 'simpr', '( %s -> ( # ` b ) = 0 )' % ph3)
    bv = w.s([bw], 'elexd', '( %s -> b e. _V )' % ph3)
    heq = w.s([bv, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` b ) = 0 <-> b = (/) ) )' % ph3)
    bz = w.s([heq, h0], 'mpbid', '( %s -> b = (/) )' % ph3)
    cl = zcat(w, ph3, zc, 'd', dw)
    idt = w.s([phm, cl, w.inst('tm2hid')], 'syl2anc', '( %s -> %s )' % (ph3, HR(JD, 'T', 'M', JD, '0')))
    # ( reverse ` b ) ++ d = d
    rb = w.s([bz], 'fveq2d', '( %s -> ( reverse ` b ) = ( reverse ` (/) ) )' % ph3)
    r0 = w.s([], 'rev0', '( reverse ` (/) ) = (/)')
    r0a = w.s([r0], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % ph3)
    rb2 = w.s([rb, r0a], 'eqtrd', '( %s -> ( reverse ` b ) = (/) )' % ph3)
    o1 = w.s([rb2], 'oveq1d', '( %s -> %s = ( (/) ++ d ) )' % (ph3, REV('b', 'd')))
    l0 = w.s([dw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ d ) = d )' % ph3)
    rv = w.s([o1, l0], 'eqtrd', '( %s -> %s = d )' % (ph3, REV('b', 'd')))
    # the two classes
    c1 = w.s([bz], 'opeq1d', '( %s -> <. b , d >. = <. (/) , d >. )' % ph3)
    c2 = w.s([c1], 'fveq2d', '( %s -> ( J ` <. b , d >. ) = %s )' % (ph3, JD))
    c3 = w.s([rv], 'opeq2d', '( %s -> <. (/) , %s >. = <. (/) , d >. )' % (ph3, REV('b', 'd')))
    c4 = w.s([c3], 'fveq2d', '( %s -> ( J ` <. (/) , %s >. ) = %s )' % (ph3, REV('b', 'd'), JD))
    pc = w.s([pn], 'nn0cnd', '( %s -> P e. CC )' % ph3)
    m0 = w.s([pc, w.inst('mul02')], 'syl', '( %s -> ( 0 x. P ) = 0 )' % ph3)
    o2 = w.s([c4, m0], 'opeq12d', '( %s -> <. ( J ` <. (/) , %s >. ) , ( 0 x. P ) >. = <. %s , 0 >. )'
             % (ph3, REV('b', 'd'), JD))
    b1 = w.s([c2, o2], 'breq12d', '( %s -> ( %s <-> %s ) )' % (ph3, CON2('b', 'd', '0'), HR(JD, 'T', 'M', JD, '0')))
    fin = w.s([b1, idt], 'mpbird', '( %s -> %s )' % (ph3, CON2('b', 'd', '0')))
    e1 = w.s([fin], 'ex', '( %s -> ( ( # ` b ) = 0 -> %s ) )' % (ph2, CON2('b', 'd', '0')))
    e2 = w.s([e1], 'ralrimiva', '( ( %s /\\ b e. Word B ) -> A. d e. Word B ( ( # ` b ) = 0 -> %s ) )'
             % (ANT2, CON2('b', 'd', '0')))
    w.qed([e2], 'ralrimiva', PSI2('0'))
    return w.run()


def tm2hwr2s():
    lab = 'tm2hwr2s'
    th = '( ( y e. NN0 /\\ %s ) /\\ %s )' % (ANT2, PSI2('y'))
    l1 = '( %s /\\ a e. Word B )' % th
    l2 = '( %s /\\ c e. Word B )' % l1
    l3 = '( %s /\\ ( # ` a ) = ( y + 1 ) )' % l2
    AT = TL('a')
    ACc = AC('a', 'c')
    w = W(lab, 'The induction step of the accumulating word-recursion rule of '
               'the machine layer: one more letter is one composition, and the '
               'letter moves to the head of the accumulator.')
    yn = w.s([], 'simp-5l', '( %s -> y e. NN0 )' % l3)
    ant = w.s([], 'simp-5r', '( %s -> %s )' % (l3, ANT2))
    psi = w.s([], 'simp-4r', '( %s -> %s )' % (l3, PSI2('y')))
    aw = w.s([], 'simpllr', '( %s -> a e. Word B )' % l3)
    cw = w.s([], 'simplr', '( %s -> c e. Word B )' % l3)
    hl = w.s([], 'simpr', '( %s -> ( # ` a ) = ( y + 1 ) )' % l3)
    phm = w.s([ant, w.inst('simp1')], 'syl', '( %s -> %s )' % (l3, PHM))
    pn = w.s([ant, w.inst('simp2l')], 'syl', '( %s -> P e. NN0 )' % l3)
    hyp = w.s([ant, w.inst('simp3')], 'syl', '( %s -> %s )' % (l3, HYP2))
    # a is nonempty
    av = w.s([aw], 'elexd', '( %s -> a e. _V )' % l3)
    heq = w.s([av, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` a ) = 0 <-> a = (/) ) )' % l3)
    yc = w.s([yn], 'nn0cnd', '( %s -> y e. CC )' % l3)
    onec = w.s([], 'ax-1cn', '1 e. CC')
    oneca = w.s([onec], 'a1i', '( %s -> 1 e. CC )' % l3)
    y1n = w.s([yn, w.inst('nn0p1nn')], 'syl', '( %s -> ( y + 1 ) e. NN )' % l3)
    y1n0 = w.s([y1n, w.inst('nnne0')], 'syl', '( %s -> ( y + 1 ) =/= 0 )' % l3)
    hn0 = w.s([hl, y1n0], 'eqnetrd', '( %s -> ( # ` a ) =/= 0 )' % l3)
    hnq = w.s([hn0], 'neneqd', '( %s -> -. ( # ` a ) = 0 )' % l3)
    an0 = w.s([heq, hnq], 'mtbid', '( %s -> -. a = (/) )' % l3)
    ane = w.s([an0], 'neqned', '( %s -> a =/= (/) )' % l3)
    atw = w.s([aw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (l3, AT))
    atl0 = w.s([aw, ane, w.inst('wrdtllen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` a ) - 1 ) )' % (l3, AT))
    sub1 = w.s([hl], 'oveq1d', '( %s -> ( ( # ` a ) - 1 ) = ( ( y + 1 ) - 1 ) )' % l3)
    pnc = w.s([yc, oneca], 'pncand', '( %s -> ( ( y + 1 ) - 1 ) = y )' % l3)
    atl = w.s([atl0, w.s([sub1, pnc], 'eqtrd', '( %s -> ( ( # ` a ) - 1 ) = y )' % l3)], 'eqtrd',
              '( %s -> ( # ` %s ) = y )' % (l3, AT))
    a0 = w.s([aw, ane, w.inst('wrdfv0')], 'syl2anc', '( %s -> ( a ` 0 ) e. B )' % l3)
    s1c = w.s([a0], 's1cld', '( %s -> <" ( a ` 0 ) "> e. Word B )' % l3)
    acw = w.s([s1c, cw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word B )' % (l3, ACc))
    # HYP2 at x := a then y := c
    lx = w.s([], 'id', '( x = a -> x = a )')
    h1, n1 = W.wcongr(w, TRI2('x', 's'), {'x': 'a'}, 'x = a', {'x': lx})
    assert n1 == TRI2('a', 's'), n1
    h2 = w.s([], 'neeq1', '( x = a -> ( x =/= (/) <-> a =/= (/) ) )')
    h3 = w.s([h2, h1], 'imbi12d', '( x = a -> ( ( x =/= (/) -> %s ) <-> ( a =/= (/) -> %s ) ) )'
             % (TRI2('x', 's'), TRI2('a', 's')))
    h4 = w.s([h3], 'ralbidv', '( x = a -> ( A. s e. Word B ( x =/= (/) -> %s ) <-> A. s e. Word B ( a =/= (/) -> %s ) ) )'
             % (TRI2('x', 's'), TRI2('a', 's')))
    h5 = w.s([h4, hyp, aw], 'rspcdva', '( %s -> A. s e. Word B ( a =/= (/) -> %s ) )' % (l3, TRI2('a', 's')))
    ly = w.s([], 'id', '( s = c -> s = c )')
    k1, n2 = W.wcongr(w, TRI2('a', 's'), {'s': 'c'}, 's = c', {'s': ly})
    assert n2 == TRI2('a', 'c'), n2
    k2 = w.s([k1], 'imbi2d', '( s = c -> ( ( a =/= (/) -> %s ) <-> ( a =/= (/) -> %s ) ) )'
             % (TRI2('a', 's'), TRI2('a', 'c')))
    k3 = w.s([k2, h5, cw], 'rspcdva', '( %s -> ( a =/= (/) -> %s ) )' % (l3, TRI2('a', 'c')))
    tri1 = w.s([k3, ane], 'mpd', '( %s -> %s )' % (l3, TRI2('a', 'c')))
    # PSI2(y) at b := AT then d := ACc
    ral = w.s([psi, ant], 'mpd',
              '( %s -> A. b e. Word B A. d e. Word B ( ( # ` b ) = y -> %s ) )' % (l3, CON2('b', 'd', 'y')))
    lb = w.s([], 'id', '( b = %s -> b = %s )' % (AT, AT))
    p1, m1 = W.wcongr(w, CON2('b', 'd', 'y'), {'b': AT}, 'b = %s' % AT, {'b': lb})
    assert m1 == CON2(AT, 'd', 'y'), m1
    p2 = w.s([], 'fveq2', '( b = %s -> ( # ` b ) = ( # ` %s ) )' % (AT, AT))
    p3 = w.s([p2], 'eqeq1d', '( b = %s -> ( ( # ` b ) = y <-> ( # ` %s ) = y ) )' % (AT, AT))
    p4 = w.s([p3, p1], 'imbi12d', '( b = %s -> ( ( ( # ` b ) = y -> %s ) <-> ( ( # ` %s ) = y -> %s ) ) )'
             % (AT, CON2('b', 'd', 'y'), AT, CON2(AT, 'd', 'y')))
    p5 = w.s([p4], 'ralbidv', '( b = %s -> ( A. d e. Word B ( ( # ` b ) = y -> %s ) <-> A. d e. Word B ( ( # ` %s ) = y -> %s ) ) )'
             % (AT, CON2('b', 'd', 'y'), AT, CON2(AT, 'd', 'y')))
    p6 = w.s([p5, ral, atw], 'rspcdva', '( %s -> A. d e. Word B ( ( # ` %s ) = y -> %s ) )' % (l3, AT, CON2(AT, 'd', 'y')))
    ld = w.s([], 'id', '( d = %s -> d = %s )' % (ACc, ACc))
    q1, m2 = W.wcongr(w, CON2(AT, 'd', 'y'), {'d': ACc}, 'd = %s' % ACc, {'d': ld})
    assert m2 == CON2(AT, ACc, 'y'), m2
    q2 = w.s([q1], 'imbi2d', '( d = %s -> ( ( ( # ` %s ) = y -> %s ) <-> ( ( # ` %s ) = y -> %s ) ) )'
             % (ACc, AT, CON2(AT, 'd', 'y'), AT, CON2(AT, ACc, 'y')))
    q3 = w.s([q2, p6, acw], 'rspcdva', '( %s -> ( ( # ` %s ) = y -> %s ) )' % (l3, AT, CON2(AT, ACc, 'y')))
    tri2 = w.s([q3, atl], 'mpd', '( %s -> %s )' % (l3, CON2(AT, ACc, 'y')))
    # compose
    sq = w.s([phm, tri1, tri2, w.inst('tm2hseq')], 'syl3anc', '( %s -> %s )'
             % (l3, HR('( J ` <. a , c >. )', 'T', 'M', '( J ` <. (/) , %s >. )' % REV(AT, ACc), '( P + ( y x. P ) )')))
    rt = w.s([aw, ane, cw, w.inst('revtail')], 'syl3anc', '( %s -> %s = %s )' % (l3, REV('a', 'c'), REV(AT, ACc)))
    r1 = w.s([rt], 'opeq2d', '( %s -> <. (/) , %s >. = <. (/) , %s >. )' % (l3, REV('a', 'c'), REV(AT, ACc)))
    r2 = w.s([r1], 'fveq2d', '( %s -> ( J ` <. (/) , %s >. ) = ( J ` <. (/) , %s >. ) )'
             % (l3, REV('a', 'c'), REV(AT, ACc)))
    pc = w.s([pn], 'nn0cnd', '( %s -> P e. CC )' % l3)
    ypc = w.s([yc, pc], 'mulcld', '( %s -> ( y x. P ) e. CC )' % l3)
    acm = w.s([pc, ypc], 'addcomd', '( %s -> ( P + ( y x. P ) ) = ( ( y x. P ) + P ) )' % l3)
    dd = w.s([yc, oneca, pc, w.inst('adddir')], 'syl3anc',
             '( %s -> ( ( y + 1 ) x. P ) = ( ( y x. P ) + ( 1 x. P ) ) )' % l3)
    mu = w.s([pc, w.inst('mullid')], 'syl', '( %s -> ( 1 x. P ) = P )' % l3)
    mo = w.s([mu], 'oveq2d', '( %s -> ( ( y x. P ) + ( 1 x. P ) ) = ( ( y x. P ) + P ) )' % l3)
    ar = w.s([dd, mo], 'eqtrd', '( %s -> ( ( y + 1 ) x. P ) = ( ( y x. P ) + P ) )' % l3)
    ar2 = w.s([acm, ar], 'eqtr4d', '( %s -> ( P + ( y x. P ) ) = ( ( y + 1 ) x. P ) )' % l3)
    o1 = w.s([r2, ar2], 'opeq12d',
             '( %s -> <. ( J ` <. (/) , %s >. ) , ( P + ( y x. P ) ) >. = <. ( J ` <. (/) , %s >. ) , ( ( y + 1 ) x. P ) >. )'
             % (l3, REV('a', 'c'), REV(AT, ACc)))
    ar3 = w.s([ar2], 'eqcomd', '( %s -> ( ( y + 1 ) x. P ) = ( P + ( y x. P ) ) )' % l3)
    o2 = w.s([r2, ar3], 'opeq12d',
             '( %s -> <. ( J ` <. (/) , %s >. ) , ( ( y + 1 ) x. P ) >. = <. ( J ` <. (/) , %s >. ) , ( P + ( y x. P ) ) >. )'
             % (l3, REV('a', 'c'), REV(AT, ACc)))
    b1 = w.s([o2], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (l3, CON2('a', 'c', '( y + 1 )'),
                HR('( J ` <. a , c >. )', 'T', 'M', '( J ` <. (/) , %s >. )' % REV(AT, ACc), '( P + ( y x. P ) )')))
    fin = w.s([b1, sq], 'mpbird', '( %s -> %s )' % (l3, CON2('a', 'c', '( y + 1 )')))
    e1 = w.s([fin], 'ex', '( %s -> ( ( # ` a ) = ( y + 1 ) -> %s ) )' % (l2, CON2('a', 'c', '( y + 1 )')))
    e2 = w.s([e1], 'ralrimiva', '( %s -> A. c e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) )'
             % (l1, CON2('a', 'c', '( y + 1 )')))
    e3 = w.s([e2], 'ralrimiva', '( %s -> A. a e. Word B A. c e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) )'
             % (th, CON2('a', 'c', '( y + 1 )')))
    # rename a -> b, c -> d
    lc = w.s([], 'id', '( c = d -> c = d )')
    z1, w1 = W.wcongr(w, CON2('a', 'c', '( y + 1 )'), {'c': 'd'}, 'c = d', {'c': lc})
    assert w1 == CON2('a', 'd', '( y + 1 )'), w1
    z2 = w.s([z1], 'imbi2d', '( c = d -> ( ( ( # ` a ) = ( y + 1 ) -> %s ) <-> ( ( # ` a ) = ( y + 1 ) -> %s ) ) )'
             % (CON2('a', 'c', '( y + 1 )'), CON2('a', 'd', '( y + 1 )')))
    z3 = w.s([z2], 'cbvralvw', '( A. c e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. d e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) )'
             % (CON2('a', 'c', '( y + 1 )'), CON2('a', 'd', '( y + 1 )')))
    z4 = w.s([z3], 'ralbii', '( A. a e. Word B A. c e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. a e. Word B A. d e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) )'
             % (CON2('a', 'c', '( y + 1 )'), CON2('a', 'd', '( y + 1 )')))
    lb2 = w.s([], 'id', '( a = b -> a = b )')
    z5, w2 = W.wcongr(w, CON2('a', 'd', '( y + 1 )'), {'a': 'b'}, 'a = b', {'a': lb2})
    assert w2 == CON2('b', 'd', '( y + 1 )'), w2
    z6 = w.s([], 'fveq2', '( a = b -> ( # ` a ) = ( # ` b ) )')
    z7 = w.s([z6], 'eqeq1d', '( a = b -> ( ( # ` a ) = ( y + 1 ) <-> ( # ` b ) = ( y + 1 ) ) )')
    z8 = w.s([z7, z5], 'imbi12d', '( a = b -> ( ( ( # ` a ) = ( y + 1 ) -> %s ) <-> ( ( # ` b ) = ( y + 1 ) -> %s ) ) )'
             % (CON2('a', 'd', '( y + 1 )'), CON2('b', 'd', '( y + 1 )')))
    z9 = w.s([z8], 'ralbidv', '( a = b -> ( A. d e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. d e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) ) )'
             % (CON2('a', 'd', '( y + 1 )'), CON2('b', 'd', '( y + 1 )')))
    z10 = w.s([z9], 'cbvralvw', '( A. a e. Word B A. d e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. b e. Word B A. d e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) )'
              % (CON2('a', 'd', '( y + 1 )'), CON2('b', 'd', '( y + 1 )')))
    z11 = w.s([z4, z10], 'bitri', '( A. a e. Word B A. c e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. b e. Word B A. d e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) )'
              % (CON2('a', 'c', '( y + 1 )'), CON2('b', 'd', '( y + 1 )')))
    z12 = w.s([z11], 'a1i', '( %s -> ( A. a e. Word B A. c e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. b e. Word B A. d e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) ) )'
              % (th, CON2('a', 'c', '( y + 1 )'), CON2('b', 'd', '( y + 1 )')))
    e4 = w.s([z12, e3], 'mpbid', '( %s -> A. b e. Word B A. d e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) )'
             % (th, CON2('b', 'd', '( y + 1 )')))
    e5 = w.s([e4], 'ex', '( ( y e. NN0 /\\ %s ) -> ( %s -> A. b e. Word B A. d e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) ) )'
             % (ANT2, PSI2('y'), CON2('b', 'd', '( y + 1 )')))
    e6 = w.s([e5], 'ex', '( y e. NN0 -> ( %s -> ( %s -> A. b e. Word B A. d e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) ) ) )'
             % (ANT2, PSI2('y'), CON2('b', 'd', '( y + 1 )')))
    w.qed([e6], 'com23', '( y e. NN0 -> ( %s -> %s ) )' % (PSI2('y'), PSI2('( y + 1 )')))
    return w.run()


def tm2hwrd2():
    lab = 'tm2hwrd2'
    ph = '( %s /\\ ( X e. Word B /\\ Y e. Word B ) )' % ANT2
    w = W(lab, 'The accumulating word-recursion rule of the fragment calculus '
               'of the machine layer: a family of classes of configurations '
               'indexed by the word still to scan and by the accumulated '
               'output, each reaching the family member of the tail with the '
               'letter prepended to the accumulator within ` P ` steps, '
               'reaches the empty-word member with the reversed word prepended '
               'to the accumulator within ` ( # ` X ) x. P ` steps.  This is '
               'the induction every mover fragment of Lean\'s Arith.lean and '
               'Prims.lean runs by hand (` moveNum_loop ` , ` move2Num_loop ` , '
               '` incLoop_loop ` , ` predLoop_loop ` ) and the one the machine '
               'model spends ~ revrun on.')
    def subst(tgt, ante, leaf):
        return W.wcongr(w, PSI2('n'), {'n': tgt}, ante, {'n': leaf})
    l1 = w.s([], 'id', '( n = 0 -> n = 0 )')
    h1, b1 = subst('0', 'n = 0', l1)
    assert b1 == PSI2('0'), b1
    l2 = w.s([], 'id', '( n = y -> n = y )')
    h2, b2 = subst('y', 'n = y', l2)
    l3 = w.s([], 'id', '( n = ( y + 1 ) -> n = ( y + 1 ) )')
    h3, b3 = subst('( y + 1 )', 'n = ( y + 1 )', l3)
    l4 = w.s([], 'id', '( n = ( # ` X ) -> n = ( # ` X ) )')
    h4, b4 = subst('( # ` X )', 'n = ( # ` X )', l4)
    h5 = w.s([], 'tm2hwr20', PSI2('0'))
    h6 = w.s([], 'tm2hwr2s', '( y e. NN0 -> ( %s -> %s ) )' % (PSI2('y'), PSI2('( y + 1 )')))
    ind = w.s([h1, h2, h3, h4, h5, h6], 'nn0ind', '( ( # ` X ) e. NN0 -> %s )' % PSI2('( # ` X )'))
    ant = w.s([], 'simpl', '( %s -> %s )' % (ph, ANT2))
    xw = w.s([], 'simprl', '( %s -> X e. Word B )' % ph)
    yw = w.s([], 'simprr', '( %s -> Y e. Word B )' % ph)
    hx = w.s([xw, w.inst('lencl')], 'syl', '( %s -> ( # ` X ) e. NN0 )' % ph)
    psi = w.s([hx, ind], 'syl', '( %s -> %s )' % (ph, PSI2('( # ` X )')))
    ral = w.s([psi, ant], 'mpd',
              '( %s -> A. b e. Word B A. d e. Word B ( ( # ` b ) = ( # ` X ) -> %s ) )'
              % (ph, CON2('b', 'd', '( # ` X )')))
    lb = w.s([], 'id', '( b = X -> b = X )')
    p1, m1 = W.wcongr(w, CON2('b', 'd', '( # ` X )'), {'b': 'X'}, 'b = X', {'b': lb})
    assert m1 == CON2('X', 'd', '( # ` X )'), m1
    p2 = w.s([], 'fveq2', '( b = X -> ( # ` b ) = ( # ` X ) )')
    p3 = w.s([p2], 'eqeq1d', '( b = X -> ( ( # ` b ) = ( # ` X ) <-> ( # ` X ) = ( # ` X ) ) )')
    p4 = w.s([p3, p1], 'imbi12d', '( b = X -> ( ( ( # ` b ) = ( # ` X ) -> %s ) <-> ( ( # ` X ) = ( # ` X ) -> %s ) ) )'
             % (CON2('b', 'd', '( # ` X )'), CON2('X', 'd', '( # ` X )')))
    p5 = w.s([p4], 'ralbidv', '( b = X -> ( A. d e. Word B ( ( # ` b ) = ( # ` X ) -> %s ) <-> A. d e. Word B ( ( # ` X ) = ( # ` X ) -> %s ) ) )'
             % (CON2('b', 'd', '( # ` X )'), CON2('X', 'd', '( # ` X )')))
    p6 = w.s([p5, ral, xw], 'rspcdva', '( %s -> A. d e. Word B ( ( # ` X ) = ( # ` X ) -> %s ) )'
             % (ph, CON2('X', 'd', '( # ` X )')))
    ld = w.s([], 'id', '( d = Y -> d = Y )')
    q1, m2 = W.wcongr(w, CON2('X', 'd', '( # ` X )'), {'d': 'Y'}, 'd = Y', {'d': ld})
    assert m2 == CON2('X', 'Y', '( # ` X )'), m2
    q2 = w.s([q1], 'imbi2d', '( d = Y -> ( ( ( # ` X ) = ( # ` X ) -> %s ) <-> ( ( # ` X ) = ( # ` X ) -> %s ) ) )'
             % (CON2('X', 'd', '( # ` X )'), CON2('X', 'Y', '( # ` X )')))
    q3 = w.s([q2, p6, yw], 'rspcdva', '( %s -> ( ( # ` X ) = ( # ` X ) -> %s ) )' % (ph, CON2('X', 'Y', '( # ` X )')))
    eqi = w.s([], 'eqid', '( # ` X ) = ( # ` X )')
    eqia = w.s([eqi], 'a1i', '( %s -> ( # ` X ) = ( # ` X ) )' % ph)
    w.qed([q3, eqia], 'mpd', '( %s -> %s )' % (ph, CON2('X', 'Y', '( # ` X )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2hwr20'): tm2hwr20()
    if want('tm2hwr2s'): tm2hwr2s()
    if want('tm2hwrd2'): tm2hwrd2()
