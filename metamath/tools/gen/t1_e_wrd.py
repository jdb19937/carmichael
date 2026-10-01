"""T1: the word-recursion rule of the fragment calculus --- the induction every
scan loop of the machine layer runs on (Lean's `induction l` in the `_loop`
lemmas of Arith.lean and Prims.lean)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

CFGT = CFG('T')
TL = lambda x: '( %s substr <. 1 , ( # ` %s ) >. )' % (x, x)
HYP = 'A. x e. Word B ( x =/= (/) -> %s )' % HR('( J ` x )', 'T', 'M', '( J ` %s )' % TL('x'), 'P')
ANT = '( %s /\\ ( P e. NN0 /\\ ( J ` (/) ) C_ %s ) /\\ %s )' % (PHM, CFGT, HYP)


def TRI(b, n):
    return HR('( J ` %s )' % b, 'T', 'M', '( J ` (/) )', '( %s x. P )' % n)


def PSI(n):
    return '( %s -> A. b e. Word B ( ( # ` b ) = %s -> %s ) )' % (ANT, n, TRI('b', n))


def ctx(w, ph, lift):
    """the four context steps of ANT under an antecedent ph reached by `lift`"""
    def L_(st, f):
        return w.s([st], lift, '( %s -> %s )' % (ph, f)) if lift else st
    return L_


def tm2hwrd0():
    lab = 'tm2hwrd0'
    ph2 = '( %s /\\ b e. Word B )' % ANT
    ph3 = '( %s /\\ ( # ` b ) = 0 )' % ph2
    w = W(lab, 'The base case of the word-recursion rule of the machine layer: '
               'the empty word needs no steps.')
    phm = w.s([], 'simp-3l' if False else 'simpll', '( %s -> %s )' % (ph3, ANT))
    phmm = w.s([phm, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph3, PHM))
    pn = w.s([phm, w.inst('simp2l')], 'syl', '( %s -> P e. NN0 )' % ph3)
    j0 = w.s([phm, w.inst('simp2r')], 'syl', '( %s -> ( J ` (/) ) C_ %s )' % (ph3, CFGT))
    bw = w.s([], 'simplr', '( %s -> b e. Word B )' % ph3)
    bv = w.s([bw], 'elexd', '( %s -> b e. _V )' % ph3)
    h0 = w.s([], 'simpr', '( %s -> ( # ` b ) = 0 )' % ph3)
    heq = w.s([bv, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` b ) = 0 <-> b = (/) ) )' % ph3)
    b0 = w.s([heq, h0], 'mpbid', '( %s -> b = (/) )' % ph3)
    jb = w.s([b0], 'fveq2d', '( %s -> ( J ` b ) = ( J ` (/) ) )' % ph3)
    idt = w.s([phmm, j0, w.inst('tm2hid')], 'syl2anc',
              '( %s -> %s )' % (ph3, HR('( J ` (/) )', 'T', 'M', '( J ` (/) )', '0')))
    pc = w.s([pn], 'nn0cnd', '( %s -> P e. CC )' % ph3)
    m0 = w.s([pc, w.inst('mul02')], 'syl', '( %s -> ( 0 x. P ) = 0 )' % ph3)
    m0c = w.s([m0], 'eqcomd', '( %s -> 0 = ( 0 x. P ) )' % ph3)
    op = w.s([m0c], 'opeq2d', '( %s -> <. ( J ` (/) ) , 0 >. = <. ( J ` (/) ) , ( 0 x. P ) >. )' % ph3)
    b1 = w.s([op], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph3, HR('( J ` (/) )', 'T', 'M', '( J ` (/) )', '0'), TRI('(/)', '0')))
    t1 = w.s([b1, idt], 'mpbid', '( %s -> %s )' % (ph3, TRI('(/)', '0')))
    b2 = w.s([jb], 'breq1d', '( %s -> ( %s <-> %s ) )' % (ph3, TRI('b', '0'), TRI('(/)', '0')))
    t2 = w.s([b2, t1], 'mpbird', '( %s -> %s )' % (ph3, TRI('b', '0')))
    e1 = w.s([t2], 'ex', '( %s -> ( ( # ` b ) = 0 -> %s ) )' % (ph2, TRI('b', '0')))
    w.qed([e1], 'ralrimiva', PSI('0'))
    return w.run()


def tm2hwrds():
    lab = 'tm2hwrds'
    th = '( ( y e. NN0 /\\ %s ) /\\ %s )' % (ANT, PSI('y'))
    l1 = '( %s /\\ a e. Word B )' % th
    l2 = '( %s /\\ ( # ` a ) = ( y + 1 ) )' % l1
    AT = TL('a')
    w = W(lab, 'The induction step of the word-recursion rule of the machine '
               'layer: one more letter is one composition.')
    yn = w.s([], 'simp-4l', '( %s -> y e. NN0 )' % l2)
    ant = w.s([], 'simp-4r', '( %s -> %s )' % (l2, ANT))
    psi = w.s([], 'simpllr', '( %s -> %s )' % (l2, PSI('y')))
    aw = w.s([], 'simplr', '( %s -> a e. Word B )' % l2)
    hl = w.s([], 'simpr', '( %s -> ( # ` a ) = ( y + 1 ) )' % l2)
    phm = w.s([ant, w.inst('simp1')], 'syl', '( %s -> %s )' % (l2, PHM))
    pn = w.s([ant, w.inst('simp2l')], 'syl', '( %s -> P e. NN0 )' % l2)
    hyp = w.s([ant, w.inst('simp3')], 'syl', '( %s -> %s )' % (l2, HYP))
    # a is nonempty
    av = w.s([aw], 'elexd', '( %s -> a e. _V )' % l2)
    heq = w.s([av, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` a ) = 0 <-> a = (/) ) )' % l2)
    yc = w.s([yn], 'nn0cnd', '( %s -> y e. CC )' % l2)
    onec = w.s([], 'ax-1cn', '1 e. CC')
    oneca = w.s([onec], 'a1i', '( %s -> 1 e. CC )' % l2)
    y1n = w.s([yn, w.inst('nn0p1nn')], 'syl', '( %s -> ( y + 1 ) e. NN )' % l2)
    y1n0 = w.s([y1n, w.inst('nnne0')], 'syl', '( %s -> ( y + 1 ) =/= 0 )' % l2)
    hn0 = w.s([hl, y1n0], 'eqnetrd', '( %s -> ( # ` a ) =/= 0 )' % l2)
    hnq = w.s([hn0], 'neneqd', '( %s -> -. ( # ` a ) = 0 )' % l2)
    an0 = w.s([heq, hnq], 'mtbid', '( %s -> -. a = (/) )' % l2)
    ane = w.s([an0], 'neqned', '( %s -> a =/= (/) )' % l2)
    # the tail
    atw = w.s([aw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B )' % (l2, AT))
    atl0 = w.s([aw, ane, w.inst('wrdtllen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` a ) - 1 ) )' % (l2, AT))
    sub1 = w.s([hl], 'oveq1d', '( %s -> ( ( # ` a ) - 1 ) = ( ( y + 1 ) - 1 ) )' % l2)
    pnc = w.s([yc, oneca], 'pncand', '( %s -> ( ( y + 1 ) - 1 ) = y )' % l2)
    atl1 = w.s([atl0, sub1], 'eqtrd', '( %s -> ( # ` %s ) = ( ( y + 1 ) - 1 ) )' % (l2, AT))
    atl = w.s([atl1, pnc], 'eqtrd', '( %s -> ( # ` %s ) = y )' % (l2, AT))
    # HYP at x := a
    s1 = w.s([], 'neeq1', '( x = a -> ( x =/= (/) <-> a =/= (/) ) )')
    s2, _n = W.congr(w, '<. ( J ` %s ) , P >.' % TL('x'), {'x': 'a'}, 'x = a',
                     {'x': w.s([], 'id', '( x = a -> x = a )')})
    s3 = w.s([s2], 'breq2d', '( x = a -> ( %s <-> %s ) )'
             % (HR('( J ` x )', 'T', 'M', '( J ` %s )' % TL('x'), 'P'),
                HR('( J ` x )', 'T', 'M', '( J ` %s )' % AT, 'P')))
    s4 = w.s([], 'fveq2', '( x = a -> ( J ` x ) = ( J ` a ) )')
    s5 = w.s([s4], 'breq1d', '( x = a -> ( %s <-> %s ) )'
             % (HR('( J ` x )', 'T', 'M', '( J ` %s )' % AT, 'P'),
                HR('( J ` a )', 'T', 'M', '( J ` %s )' % AT, 'P')))
    s6 = w.s([s3, s5], 'bitrd', '( x = a -> ( %s <-> %s ) )'
             % (HR('( J ` x )', 'T', 'M', '( J ` %s )' % TL('x'), 'P'),
                HR('( J ` a )', 'T', 'M', '( J ` %s )' % AT, 'P')))
    s7 = w.s([s1, s6], 'imbi12d', '( x = a -> ( ( x =/= (/) -> %s ) <-> ( a =/= (/) -> %s ) ) )'
             % (HR('( J ` x )', 'T', 'M', '( J ` %s )' % TL('x'), 'P'),
                HR('( J ` a )', 'T', 'M', '( J ` %s )' % AT, 'P')))
    ins = w.s([s7, hyp, aw], 'rspcdva', '( %s -> ( a =/= (/) -> %s ) )'
              % (l2, HR('( J ` a )', 'T', 'M', '( J ` %s )' % AT, 'P')))
    tri1 = w.s([ins, ane], 'mpd', '( %s -> %s )' % (l2, HR('( J ` a )', 'T', 'M', '( J ` %s )' % AT, 'P')))
    # PSI(y) at b := the tail
    p1, _n2 = W.congr(w, '( J ` b )', {'b': AT}, 'b = %s' % AT,
                      {'b': w.s([], 'id', '( b = %s -> b = %s )' % (AT, AT))})
    p2 = w.s([p1], 'breq1d', '( b = %s -> ( %s <-> %s ) )' % (AT, TRI('b', 'y'), TRI(AT, 'y')))
    p3 = w.s([], 'fveq2', '( b = %s -> ( # ` b ) = ( # ` %s ) )' % (AT, AT))
    p4 = w.s([p3], 'eqeq1d', '( b = %s -> ( ( # ` b ) = y <-> ( # ` %s ) = y ) )' % (AT, AT))
    p5 = w.s([p4, p2], 'imbi12d', '( b = %s -> ( ( ( # ` b ) = y -> %s ) <-> ( ( # ` %s ) = y -> %s ) ) )'
             % (AT, TRI('b', 'y'), AT, TRI(AT, 'y')))
    ral = w.s([psi, ant], 'mpd', '( %s -> A. b e. Word B ( ( # ` b ) = y -> %s ) )' % (l2, TRI('b', 'y')))
    inp = w.s([p5, ral, atw], 'rspcdva', '( %s -> ( ( # ` %s ) = y -> %s ) )' % (l2, AT, TRI(AT, 'y')))
    tri2 = w.s([inp, atl], 'mpd', '( %s -> %s )' % (l2, TRI(AT, 'y')))
    # compose
    sq = w.s([phm, tri1, tri2, w.inst('tm2hseq')], 'syl3anc',
             '( %s -> %s )' % (l2, HR('( J ` a )', 'T', 'M', '( J ` (/) )', '( P + ( y x. P ) )')))
    pc = w.s([pn], 'nn0cnd', '( %s -> P e. CC )' % l2)
    ypc = w.s([yc, pc], 'mulcld', '( %s -> ( y x. P ) e. CC )' % l2)
    acm = w.s([pc, ypc], 'addcomd', '( %s -> ( P + ( y x. P ) ) = ( ( y x. P ) + P ) )' % l2)
    dd = w.s([yc, oneca, pc, w.inst('adddir')], 'syl3anc',
             '( %s -> ( ( y + 1 ) x. P ) = ( ( y x. P ) + ( 1 x. P ) ) )' % l2)
    m1 = w.s([pc, w.inst('mullid')], 'syl', '( %s -> ( 1 x. P ) = P )' % l2)
    m1o = w.s([m1], 'oveq2d', '( %s -> ( ( y x. P ) + ( 1 x. P ) ) = ( ( y x. P ) + P ) )' % l2)
    ar = w.s([dd, m1o], 'eqtrd', '( %s -> ( ( y + 1 ) x. P ) = ( ( y x. P ) + P ) )' % l2)
    ar2 = w.s([acm, ar], 'eqtr4d', '( %s -> ( P + ( y x. P ) ) = ( ( y + 1 ) x. P ) )' % l2)
    op = w.s([ar2], 'opeq2d', '( %s -> <. ( J ` (/) ) , ( P + ( y x. P ) ) >. = <. ( J ` (/) ) , ( ( y + 1 ) x. P ) >. )' % l2)
    bq = w.s([op], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (l2, HR('( J ` a )', 'T', 'M', '( J ` (/) )', '( P + ( y x. P ) )'), TRI('a', '( y + 1 )')))
    fin = w.s([bq, sq], 'mpbid', '( %s -> %s )' % (l2, TRI('a', '( y + 1 )')))
    e1 = w.s([fin], 'ex', '( %s -> ( ( # ` a ) = ( y + 1 ) -> %s ) )' % (l1, TRI('a', '( y + 1 )')))
    e2 = w.s([e1], 'ralrimiva', '( %s -> A. a e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) )'
             % (th, TRI('a', '( y + 1 )')))
    # rename a to b
    c1, _n3 = W.congr(w, '( J ` a )', {'a': 'b'}, 'a = b', {'a': w.s([], 'id', '( a = b -> a = b )')})
    c2 = w.s([c1], 'breq1d', '( a = b -> ( %s <-> %s ) )' % (TRI('a', '( y + 1 )'), TRI('b', '( y + 1 )')))
    c3 = w.s([], 'fveq2', '( a = b -> ( # ` a ) = ( # ` b ) )')
    c4 = w.s([c3], 'eqeq1d', '( a = b -> ( ( # ` a ) = ( y + 1 ) <-> ( # ` b ) = ( y + 1 ) ) )')
    c5 = w.s([c4, c2], 'imbi12d', '( a = b -> ( ( ( # ` a ) = ( y + 1 ) -> %s ) <-> ( ( # ` b ) = ( y + 1 ) -> %s ) ) )'
             % (TRI('a', '( y + 1 )'), TRI('b', '( y + 1 )')))
    c6 = w.s([c5], 'cbvralvw', '( A. a e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. b e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) )'
             % (TRI('a', '( y + 1 )'), TRI('b', '( y + 1 )')))
    c7 = w.s([c6], 'a1i', '( %s -> ( A. a e. Word B ( ( # ` a ) = ( y + 1 ) -> %s ) <-> A. b e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) ) )'
             % (th, TRI('a', '( y + 1 )'), TRI('b', '( y + 1 )')))
    e3 = w.s([c7, e2], 'mpbid', '( %s -> A. b e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) )' % (th, TRI('b', '( y + 1 )')))
    e4 = w.s([e3], 'ex', '( ( y e. NN0 /\\ %s ) -> ( %s -> A. b e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) ) )'
             % (ANT, PSI('y'), TRI('b', '( y + 1 )')))
    e5 = w.s([e4], 'ex', '( y e. NN0 -> ( %s -> ( %s -> A. b e. Word B ( ( # ` b ) = ( y + 1 ) -> %s ) ) ) )'
             % (ANT, PSI('y'), TRI('b', '( y + 1 )')))
    w.qed([e5], 'com23', '( y e. NN0 -> ( %s -> %s ) )' % (PSI('y'), PSI('( y + 1 )')))
    return w.run()


def tm2hwrd():
    lab = 'tm2hwrd'
    ph = '( %s /\\ X e. Word B )' % ANT
    w = W(lab, 'The word-recursion rule of the fragment calculus of the machine '
               'layer: a family of classes of configurations indexed by the '
               'word still to scan, each reaching the family member of the '
               'tail within ` P ` steps, reaches the empty-word member within '
               '` ( # ` X ) x. P ` steps.  This single induction is the one '
               'every scan loop of Lean\'s Arith.lean and Prims.lean runs by '
               'hand (` dropNum_loop ` , ` clear_loop ` , ` moveNum_loop ` , '
               '` move2Num_loop ` , ` zeroScan_loop ` , ` incLoop_loop ` , '
               '` predLoop_loop ` ), and the one the machine model spends '
               '~ revrun on.')
    def subst(tgt, ante, leaf):
        return W.wcongr(w, PSI('n'), {'n': tgt}, ante, {'n': leaf})
    l1 = w.s([], 'id', '( n = 0 -> n = 0 )')
    h1, b1 = subst('0', 'n = 0', l1)
    assert b1 == PSI('0'), b1
    l2 = w.s([], 'id', '( n = y -> n = y )')
    h2, b2 = subst('y', 'n = y', l2)
    l3 = w.s([], 'id', '( n = ( y + 1 ) -> n = ( y + 1 ) )')
    h3, b3 = subst('( y + 1 )', 'n = ( y + 1 )', l3)
    l4 = w.s([], 'id', '( n = ( # ` X ) -> n = ( # ` X ) )')
    h4, b4 = subst('( # ` X )', 'n = ( # ` X )', l4)
    h5 = w.s([], 'tm2hwrd0', PSI('0'))
    h6 = w.s([], 'tm2hwrds', '( y e. NN0 -> ( %s -> %s ) )' % (PSI('y'), PSI('( y + 1 )')))
    ind = w.s([h1, h2, h3, h4, h5, h6], 'nn0ind', '( ( # ` X ) e. NN0 -> %s )' % PSI('( # ` X )'))
    xw = w.s([], 'simpr', '( %s -> X e. Word B )' % ph)
    ant = w.s([], 'simpl', '( %s -> %s )' % (ph, ANT))
    hx = w.s([xw, w.inst('lencl')], 'syl', '( %s -> ( # ` X ) e. NN0 )' % ph)
    psi = w.s([hx, ind], 'syl', '( %s -> %s )' % (ph, PSI('( # ` X )')))
    ral = w.s([psi, ant], 'mpd', '( %s -> A. b e. Word B ( ( # ` b ) = ( # ` X ) -> %s ) )' % (ph, TRI('b', '( # ` X )')))
    q1, _q = W.congr(w, '( J ` b )', {'b': 'X'}, 'b = X', {'b': w.s([], 'id', '( b = X -> b = X )')})
    q2 = w.s([q1], 'breq1d', '( b = X -> ( %s <-> %s ) )' % (TRI('b', '( # ` X )'), TRI('X', '( # ` X )')))
    q3 = w.s([], 'fveq2', '( b = X -> ( # ` b ) = ( # ` X ) )')
    q4 = w.s([q3], 'eqeq1d', '( b = X -> ( ( # ` b ) = ( # ` X ) <-> ( # ` X ) = ( # ` X ) ) )')
    q5 = w.s([q4, q2], 'imbi12d', '( b = X -> ( ( ( # ` b ) = ( # ` X ) -> %s ) <-> ( ( # ` X ) = ( # ` X ) -> %s ) ) )'
             % (TRI('b', '( # ` X )'), TRI('X', '( # ` X )')))
    ins = w.s([q5, ral, xw], 'rspcdva', '( %s -> ( ( # ` X ) = ( # ` X ) -> %s ) )' % (ph, TRI('X', '( # ` X )')))
    eqi = w.s([], 'eqid', '( # ` X ) = ( # ` X )')
    eqia = w.s([eqi], 'a1i', '( %s -> ( # ` X ) = ( # ` X ) )' % ph)
    w.qed([ins, eqia], 'mpd', '( %s -> %s )' % (ph, TRI('X', '( # ` X )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2hwrd0'): tm2hwrd0()
    if want('tm2hwrds'): tm2hwrds()
    if want('tm2hwrd'): tm2hwrd()
