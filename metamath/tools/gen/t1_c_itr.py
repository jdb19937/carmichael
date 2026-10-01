"""T1: the iteration rule of the fragment calculus --- the single induction
that replaces every bounded loop of the machine layer."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

CFGT = CFG('T')
TRI = HR('( I ` i )', 'T', 'M', '( I ` ( i + 1 ) )', 'P')


def ANT(n):
    return ('( %s /\\ ( ( I ` 0 ) C_ %s /\\ P e. NN0 ) /\\ A. i e. ( 0 ..^ %s ) %s )'
            % (PHM, CFGT, n, TRI))


def CON(n):
    return HR('( I ` 0 )', 'T', 'M', '( I ` %s )' % n, '( %s x. P )' % n)


def PH(n):
    return '( %s -> %s )' % (ANT(n), CON(n))


def tm2hitr0():
    lab = 'tm2hitr0'
    ph = ANT('0')
    w = W(lab, 'The base case of the iteration rule of the machine layer: no '
               'iterations, no steps.')
    phm = w.s([], 'simp1', '( %s -> %s )' % (ph, PHM))
    i0 = w.s([], 'simp2l', '( %s -> ( I ` 0 ) C_ %s )' % (ph, CFGT))
    pn = w.s([], 'simp2r', '( %s -> P e. NN0 )' % ph)
    idt = w.s([phm, i0, w.inst('tm2hid')], 'syl2anc', '( %s -> %s )' % (ph, HR('( I ` 0 )', 'T', 'M', '( I ` 0 )', '0')))
    pc = w.s([pn], 'nn0cnd', '( %s -> P e. CC )' % ph)
    m0 = w.s([pc, w.inst('mul02')], 'syl', '( %s -> ( 0 x. P ) = 0 )' % ph)
    m0c = w.s([m0], 'eqcomd', '( %s -> 0 = ( 0 x. P ) )' % ph)
    op = w.s([m0c], 'opeq2d', '( %s -> <. ( I ` 0 ) , 0 >. = <. ( I ` 0 ) , ( 0 x. P ) >. )' % ph)
    bq = w.s([op], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( I ` 0 )', 'T', 'M', '( I ` 0 )', '0'), CON('0')))
    w.qed([bq, idt], 'mpbid', '( %s -> %s )' % (ph, CON('0')))
    return w.run()


def tm2hitrs():
    lab = 'tm2hitrs'
    th = '( ( y e. NN0 /\\ %s ) /\\ %s )' % (ANT('( y + 1 )'), PH('y'))
    TRIy = HR('( I ` y )', 'T', 'M', '( I ` ( y + 1 ) )', 'P')
    w = W(lab, 'The induction step of the iteration rule of the machine layer: '
               'one more iteration is one composition.')
    yn = w.s([], 'simpll', '( %s -> y e. NN0 )' % th)
    ant = w.s([], 'simplr', '( %s -> %s )' % (th, ANT('( y + 1 )')))
    phy = w.s([], 'simpr', '( %s -> %s )' % (th, PH('y')))
    phm = w.s([ant, w.inst('simp1')], 'syl', '( %s -> %s )' % (th, PHM))
    i0 = w.s([ant, w.inst('simp2l')], 'syl', '( %s -> ( I ` 0 ) C_ %s )' % (th, CFGT))
    pn = w.s([ant, w.inst('simp2r')], 'syl', '( %s -> P e. NN0 )' % th)
    ral1 = w.s([ant, w.inst('simp3')], 'syl', '( %s -> A. i e. ( 0 ..^ ( y + 1 ) ) %s )' % (th, TRI))
    # ( 0 ..^ y ) C_ ( 0 ..^ ( y + 1 ) )
    yz = w.s([yn], 'nn0zd', '( %s -> y e. ZZ )' % th)
    uzi = w.s([yz, w.inst('uzid')], 'syl', '( %s -> y e. ( ZZ>= ` y ) )' % th)
    uz1 = w.s([uzi, w.inst('peano2uz')], 'syl', '( %s -> ( y + 1 ) e. ( ZZ>= ` y ) )' % th)
    fss = w.s([uz1, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ y ) C_ ( 0 ..^ ( y + 1 ) ) )' % th)
    ralr = w.s([fss, ral1, w.inst('ssralv')], 'mpd' if False else 'sylc',
               '( %s -> A. i e. ( 0 ..^ y ) %s )' % (th, TRI))
    ipn = w.s([i0, pn], 'jca', '( %s -> ( ( I ` 0 ) C_ %s /\\ P e. NN0 ) )' % (th, CFGT))
    anty = w.s([phm, ipn, ralr], '3jca', '( %s -> %s )' % (th, ANT('y')))
    cony = w.s([phy, anty], 'mpd', '( %s -> %s )' % (th, CON('y')))
    # y e. ( 0 ..^ ( y + 1 ) )
    y1nn = w.s([yn, w.inst('nn0p1nn')], 'syl', '( %s -> ( y + 1 ) e. NN )' % th)
    fend = w.s([y1nn, w.inst('fzo0end')], 'syl', '( %s -> ( ( y + 1 ) - 1 ) e. ( 0 ..^ ( y + 1 ) ) )' % th)
    yc = w.s([yn], 'nn0cnd', '( %s -> y e. CC )' % th)
    onec = w.s([], 'ax-1cn', '1 e. CC')
    oneca = w.s([onec], 'a1i', '( %s -> 1 e. CC )' % th)
    pnc = w.s([yc, oneca], 'pncand', '( %s -> ( ( y + 1 ) - 1 ) = y )' % th)
    pncr = w.s([pnc], 'eqcomd', '( %s -> y = ( ( y + 1 ) - 1 ) )' % th)
    yfzo = w.s([pncr, fend], 'eqeltrd', '( %s -> y e. ( 0 ..^ ( y + 1 ) ) )' % th)
    # the triple at i := y
    sb, nb = W.congr(w, '<. ( I ` ( i + 1 ) ) , P >.', {'i': 'y'}, 'i = y',
                     {'i': w.s([], 'id', '( i = y -> i = y )')})
    sb1 = w.s([sb], 'breq2d', '( i = y -> ( %s <-> %s ) )'
              % (TRI, HR('( I ` i )', 'T', 'M', '( I ` ( y + 1 ) )', 'P')))
    sb2 = w.s([], 'fveq2', '( i = y -> ( I ` i ) = ( I ` y ) )')
    sb3 = w.s([sb2], 'breq1d', '( i = y -> ( %s <-> %s ) )'
              % (HR('( I ` i )', 'T', 'M', '( I ` ( y + 1 ) )', 'P'), TRIy))
    sb4 = w.s([sb1, sb3], 'bitrd', '( i = y -> ( %s <-> %s ) )' % (TRI, TRIy))
    triy = w.s([sb4, ral1, yfzo], 'rspcdva', '( %s -> %s )' % (th, TRIy))
    # compose
    sq = w.s([phm, cony, triy, w.inst('tm2hseq')], 'syl3anc',
             '( %s -> %s )' % (th, HR('( I ` 0 )', 'T', 'M', '( I ` ( y + 1 ) )', '( ( y x. P ) + P )')))
    pc = w.s([pn], 'nn0cnd', '( %s -> P e. CC )' % th)
    dd = w.s([yc, oneca, pc, w.inst('adddir')], 'syl3anc',
             '( %s -> ( ( y + 1 ) x. P ) = ( ( y x. P ) + ( 1 x. P ) ) )' % th)
    m1 = w.s([pc, w.inst('mullid')], 'syl', '( %s -> ( 1 x. P ) = P )' % th)
    m1o = w.s([m1], 'oveq2d', '( %s -> ( ( y x. P ) + ( 1 x. P ) ) = ( ( y x. P ) + P ) )' % th)
    ar = w.s([dd, m1o], 'eqtrd', '( %s -> ( ( y + 1 ) x. P ) = ( ( y x. P ) + P ) )' % th)
    arc = w.s([ar], 'eqcomd', '( %s -> ( ( y x. P ) + P ) = ( ( y + 1 ) x. P ) )' % th)
    op = w.s([arc], 'opeq2d', '( %s -> <. ( I ` ( y + 1 ) ) , ( ( y x. P ) + P ) >. = <. ( I ` ( y + 1 ) ) , ( ( y + 1 ) x. P ) >. )' % th)
    bq = w.s([op], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (th, HR('( I ` 0 )', 'T', 'M', '( I ` ( y + 1 ) )', '( ( y x. P ) + P )'), CON('( y + 1 )')))
    fin = w.s([bq, sq], 'mpbid', '( %s -> %s )' % (th, CON('( y + 1 )')))
    e1 = w.s([fin], 'ex', '( ( y e. NN0 /\\ %s ) -> ( %s -> %s ) )' % (ANT('( y + 1 )'), PH('y'), CON('( y + 1 )')))
    e2 = w.s([e1], 'ex', '( y e. NN0 -> ( %s -> ( %s -> %s ) ) )' % (ANT('( y + 1 )'), PH('y'), CON('( y + 1 )')))
    w.qed([e2], 'com23', '( y e. NN0 -> ( %s -> %s ) )' % (PH('y'), PH('( y + 1 )')))
    return w.run()


def tm2hitr():
    lab = 'tm2hitr'
    w = W(lab, 'The iteration rule of the fragment calculus of the machine '
               'layer: an indexed family of classes of configurations, each '
               'reaching the next within ` P ` steps, reaches the last from the '
               'first within ` N x. P ` steps.  This single induction replaces '
               'Lean\'s ` Frag.loop_runs ` : with whole configurations in the '
               'invariant there is no test label and no condition function in '
               'the statement, and bounded looping is iterated composition.')
    def subst(tgt, ante, leaf):
        return W.wcongr(w, PH('x'), {'x': tgt}, ante, {'x': leaf})
    l1 = w.s([], 'id', '( x = 0 -> x = 0 )')
    h1, b1 = subst('0', 'x = 0', l1)
    assert b1 == PH('0'), b1
    l2 = w.s([], 'id', '( x = y -> x = y )')
    h2, b2 = subst('y', 'x = y', l2)
    l3 = w.s([], 'id', '( x = ( y + 1 ) -> x = ( y + 1 ) )')
    h3, b3 = subst('( y + 1 )', 'x = ( y + 1 )', l3)
    l4 = w.s([], 'id', '( x = N -> x = N )')
    h4, b4 = subst('N', 'x = N', l4)
    h5 = w.s([], 'tm2hitr0', PH('0'))
    h6 = w.s([], 'tm2hitrs', '( y e. NN0 -> ( %s -> %s ) )' % (PH('y'), PH('( y + 1 )')))
    w.qed([h1, h2, h3, h4, h5, h6], 'nn0ind', '( N e. NN0 -> %s )' % PH('N'))
    return w.run()


if __name__ == '__main__':
    if want('tm2hitr0'): tm2hitr0()
    if want('tm2hitrs'): tm2hitrs()
    if want('tm2hitr'): tm2hitr()


def tm2hev():
    lab = 'tm2hev'
    ph0 = '( %s /\\ ( X e. %s /\\ Y e. %s ) )' % (PHM, CFGT, CFGT)
    HRS = HR('{ X }', 'T', 'M', '{ Y }', 'N')
    ph = '( %s /\\ %s )' % (ph0, HRS)
    G = OPS('T', 'M')
    ST = '( T TM2step M )'
    def Ei(v, x):
        return 'E. %s e. ( 0 ... N ) E. w e. { Y } %s = ( inl ` w )' % (v, ITER('T', 'M', v, '( inl ` %s )' % x))
    w = W(lab, 'A Hoare triple between two single configurations is Mathlib\'s '
               '` EvalsToInTime ` : the triple iterates the same optional-step '
               'function, so the conversion is an unfolding.  Lean: '
               '` Frag.toFinTM2_outputs_exists ` .')
    phm = w.s([], 'simpll', '( %s -> %s )' % (ph, PHM))
    xc = w.s([], 'simplrl', '( %s -> X e. %s )' % (ph, CFGT))
    yc = w.s([], 'simplrr', '( %s -> Y e. %s )' % (ph, CFGT))
    br = w.s([], 'simpr', '( %s -> %s )' % (ph, HRS))
    ty, bd = hrelim(w, ph, phm, '{ X }', '{ Y }', 'N', br)
    nn = w.s([ty], 'simp3d', '( %s -> N e. NN0 )' % ph)
    xv = w.s([xc], 'elexd', '( %s -> X e. _V )' % ph)
    yv = w.s([yc], 'elexd', '( %s -> Y e. _V )' % ph)
    # peel the outer singleton
    a1 = w.s([], 'fveq2', '( u = X -> ( inl ` u ) = ( inl ` X ) )')
    a2 = w.s([a1], 'fveq2d', '( u = X -> %s = %s )'
             % (ITER('T', 'M', 'i', '( inl ` u )'), ITER('T', 'M', 'i', '( inl ` X )')))
    a3 = w.s([a2], 'eqeq1d', '( u = X -> ( %s = ( inl ` w ) <-> %s = ( inl ` w ) ) )'
             % (ITER('T', 'M', 'i', '( inl ` u )'), ITER('T', 'M', 'i', '( inl ` X )')))
    a4 = w.s([a3], 'rexbidv', '( u = X -> ( E. w e. { Y } %s = ( inl ` w ) <-> E. w e. { Y } %s = ( inl ` w ) ) )'
             % (ITER('T', 'M', 'i', '( inl ` u )'), ITER('T', 'M', 'i', '( inl ` X )')))
    a5 = w.s([a4], 'rexbidv', '( u = X -> ( %s <-> %s ) )' % (Ei('i', 'u'), Ei('i', 'X')))
    a6 = w.s([a5], 'ralsng', '( X e. _V -> ( A. u e. { X } %s <-> %s ) )' % (Ei('i', 'u'), Ei('i', 'X')))
    a7 = w.s([xv, a6], 'syl', '( %s -> ( A. u e. { X } %s <-> %s ) )' % (ph, Ei('i', 'u'), Ei('i', 'X')))
    bd1 = w.s([a7, bd], 'mpbid', '( %s -> %s )' % (ph, Ei('i', 'X')))
    # peel the inner singleton
    EQ = lambda v: '%s = ( inl ` Y )' % ITER('T', 'M', v, '( inl ` X )')
    b1 = w.s([], 'fveq2', '( w = Y -> ( inl ` w ) = ( inl ` Y ) )')
    b2 = w.s([b1], 'eqeq2d', '( w = Y -> ( %s = ( inl ` w ) <-> %s ) )'
             % (ITER('T', 'M', 'i', '( inl ` X )'), EQ('i')))
    b3 = w.s([b2], 'rexsng', '( Y e. _V -> ( E. w e. { Y } %s = ( inl ` w ) <-> %s ) )'
             % (ITER('T', 'M', 'i', '( inl ` X )'), EQ('i')))
    b4 = w.s([yv, b3], 'syl', '( %s -> ( E. w e. { Y } %s = ( inl ` w ) <-> %s ) )'
             % (ph, ITER('T', 'M', 'i', '( inl ` X )'), EQ('i')))
    b5 = w.s([b4], 'rexbidv', '( %s -> ( %s <-> E. i e. ( 0 ... N ) %s ) )' % (ph, Ei('i', 'X'), EQ('i')))
    bd2 = w.s([b5, bd1], 'mpbid', '( %s -> E. i e. ( 0 ... N ) %s )' % (ph, EQ('i')))
    # rename i to n
    c1 = w.s([], 'oveq2', '( i = n -> ( %s ^r i ) = ( %s ^r n ) )' % (G, G))
    c2 = w.s([c1], 'fveq1d', '( i = n -> %s = %s )'
             % (ITER('T', 'M', 'i', '( inl ` X )'), ITER('T', 'M', 'n', '( inl ` X )')))
    c3 = w.s([c2], 'eqeq1d', '( i = n -> ( %s <-> %s ) )' % (EQ('i'), EQ('n')))
    c4 = w.s([c3], 'cbvrexvw', '( E. i e. ( 0 ... N ) %s <-> E. n e. ( 0 ... N ) %s )' % (EQ('i'), EQ('n')))
    c4a = w.s([c4], 'a1i', '( %s -> ( E. i e. ( 0 ... N ) %s <-> E. n e. ( 0 ... N ) %s ) )' % (ph, EQ('i'), EQ('n')))
    bd3 = w.s([c4a, bd2], 'mpbid', '( %s -> E. n e. ( 0 ... N ) %s )' % (ph, EQ('n')))
    # the domain facts
    dm = w.s([phm, w.inst('tm2hsdm')], 'syl', '( %s -> dom %s = %s )' % (ph, ST, CFGT))
    xdm = w.s([xc, dm], 'eleqtrrd', '( %s -> X e. dom %s )' % (ph, ST))
    ydm = w.s([yc, dm], 'eleqtrrd', '( %s -> Y e. dom %s )' % (ph, ST))
    ydj = w.s([ydm, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Y ) e. ( dom %s |_| 1o ) )' % (ph, ST))
    sve = w.s([], 'ovex', '%s e. _V' % ST)
    svea = w.s([sve], 'a1i', '( %s -> %s e. _V )' % (ph, ST))
    ilv = w.s([], 'fvex', '( inl ` Y ) e. _V')
    ilva = w.s([ilv], 'a1i', '( %s -> ( inl ` Y ) e. _V )' % ph)
    j1 = w.s([xv, ilva], 'jca', '( %s -> ( X e. _V /\\ ( inl ` Y ) e. _V ) )' % ph)
    ev = w.s([svea, nn, j1, w.inst('evalsttbr')], 'syl3anc',
             '( %s -> ( X ( %s EvalsToInTime N ) ( inl ` Y ) <-> ( ( X e. dom %s /\\ ( inl ` Y ) e. ( dom %s |_| 1o ) ) /\\ E. n e. ( 0 ... N ) %s ) ) )'
             % (ph, ST, ST, ST, EQ('n')))
    j2 = w.s([xdm, ydj], 'jca', '( %s -> ( X e. dom %s /\\ ( inl ` Y ) e. ( dom %s |_| 1o ) ) )' % (ph, ST, ST))
    j3 = w.s([j2, bd3], 'jca',
             '( %s -> ( ( X e. dom %s /\\ ( inl ` Y ) e. ( dom %s |_| 1o ) ) /\\ E. n e. ( 0 ... N ) %s ) )'
             % (ph, ST, ST, EQ('n')))
    w.qed([ev, j3], 'mpbird', '( %s -> X ( %s EvalsToInTime N ) ( inl ` Y ) )' % (ph, ST))
    return w.run()

    if want('tm2hev'): tm2hev()
