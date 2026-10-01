"""T-PL: the Sigma-cost iteration rule ~ tm2hitsum of the fragment calculus:
~ tm2hitr with a per-iteration bound family ` ( U ` i ) ` and the total
` sum_ i e. ( 0 ..^ R ) ( U ` i ) ` (blueprint D4; Lean ` Frag.loop_runs' `
and ` loop_runs_budget ` rest on it).  Induction on ` R ` as ~ tm2hitr , the
sum split by ~ fsumsplitsnun ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

ANTE, CONCL, RAL = HITS_ANTE, HITS_CONCL, HITS_HYP
PH = lambda X: '( %s -> %s )' % (ANTE(X), CONCL(X))
BODY = lambda i: '( %s e. NN0 /\\ %s )' % (UF(i), TRI('( I ` %s )' % i, '( I ` ( %s + 1 ) )' % i, UF(i)))
SM = lambda X: SUM('i', X, UF('i'))
HRI = lambda X, n: TRI('( I ` 0 )', '( I ` %s )' % X, n)


def congr(w, X):
    """( x = X -> ( PH( x ) <-> PH( X ) ) )"""
    e = 'x = %s' % X
    s1 = w.s([], 'id', '( %s -> %s )' % (e, e))
    c1 = w.s([s1], 'oveq2d', '( %s -> ( 0 ..^ x ) = ( 0 ..^ %s ) )' % (e, X))
    c2 = w.s([c1], 'raleqdv', '( %s -> ( %s <-> %s ) )' % (e, RAL('x'), RAL(X)))
    c3 = w.s([c2], '3anbi3d', '( %s -> ( %s <-> %s ) )' % (e, ANTE('x'), ANTE(X)))
    c4 = w.s([s1], 'fveq2d', '( %s -> ( I ` x ) = ( I ` %s ) )' % (e, X))
    c5 = w.s([c1], 'sumeq1d', '( %s -> %s = %s )' % (e, SM('x'), SM(X)))
    c6 = w.s([c4, c5], 'opeq12d', '( %s -> <. ( I ` x ) , %s >. = <. ( I ` %s ) , %s >. )' % (e, SM('x'), X, SM(X)))
    c7 = w.s([c6], 'breq2d', '( %s -> ( %s <-> %s ) )' % (e, HRI('x', SM('x')), HRI(X, SM(X))))
    return w.s([c3, c7], 'imbi12d', '( %s -> ( %s <-> %s ) )' % (e, PH('x'), PH(X)))


def tm2hitsum():
    lab = 'tm2hitsum'
    w = W(lab, 'The iteration rule of the fragment calculus with a per-iteration bound family: an indexed family '
               'of classes of configurations, the ` i ` -th reaching the next within ` ( U ` i ) ` steps, reaches '
               'the last from the first within ` sum_ i e. ( 0 ..^ R ) ( U ` i ) ` steps.  ~ tm2hitr is the '
               'uniform case; the Sigma form carries Lean\'s ` Frag.loop_runs\' ` and ` Frag.loop_runs_budget ` '
               '(PrimTD.lean, PrimList.lean), whose per-iteration costs vary.')
    cs = [congr(w, X) for X in ('0', 'y', '( y + 1 )', 'R')]
    # ---- the base
    a = ANTE('0')
    phm = w.s([], 'simp1', '( %s -> %s )' % (a, PHM))
    i0 = w.s([], 'simp2', '( %s -> ( I ` 0 ) C_ %s )' % (a, CFG_T))
    j = w.s([phm, i0], 'jca', '( %s -> ( %s /\\ ( I ` 0 ) C_ %s ) )' % (a, PHM, CFG_T))
    hid = w.s([j, w.inst('tm2hid')], 'syl', '( %s -> %s )' % (a, HRI('0', '0')))
    f0 = w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')
    s0 = w.s([f0], 'sumeq1i', '%s = %s' % (SM('0'), SUM('i', '', UF('i')).replace('( 0 ..^  )', '(/)')))
    z = w.s([], 'sum0', 'sum_ i e. (/) ( U ` i ) = 0')
    e = w.s([s0, z], 'eqtri', '%s = 0' % SM('0'))
    ec = w.s([e], 'eqcomi', '0 = %s' % SM('0'))
    o = w.s([ec], 'opeq2i', '<. ( I ` 0 ) , 0 >. = <. ( I ` 0 ) , %s >.' % SM('0'))
    b = w.s([o], 'breq2i', '( %s <-> %s )' % (HRI('0', '0'), HRI('0', SM('0'))))
    base = w.s([hid, b], 'sylib', PH('0'))
    # ---- the step
    Y1 = '( y + 1 )'
    ps = '( ( y e. NN0 /\\ %s ) /\\ %s )' % (ANTE(Y1), PH('y'))
    yn = w.s([], 'simpll', '( %s -> y e. NN0 )' % ps)
    a1 = w.s([], 'simplr', '( %s -> %s )' % (ps, ANTE(Y1)))
    ih = w.s([], 'simpr', '( %s -> %s )' % (ps, PH('y')))
    phm = w.s([a1, w.inst('simp1')], 'syl', '( %s -> %s )' % (ps, PHM))
    i0 = w.s([a1, w.inst('simp2')], 'syl', '( %s -> ( I ` 0 ) C_ %s )' % (ps, CFG_T))
    ral1 = w.s([a1, w.inst('simp3')], 'syl', '( %s -> %s )' % (ps, RAL(Y1)))
    yz = w.s([yn], 'nn0zd', '( %s -> y e. ZZ )' % ps)
    yu = w.s([yz, w.inst('uzid')], 'syl', '( %s -> y e. ( ZZ>= ` y ) )' % ps)
    y1u = w.s([yu, w.inst('peano2uz')], 'syl', '( %s -> ( y + 1 ) e. ( ZZ>= ` y ) )' % ps)
    ss = w.s([y1u, w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ y ) C_ ( 0 ..^ ( y + 1 ) ) )' % ps)
    ral0 = w.s([ss, ral1, w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ps, RAL('y')))
    ante0 = w.s([phm, i0, ral0], '3jca', '( %s -> %s )' % (ps, ANTE('y')))
    c0 = w.s([ante0, ih], 'mpd', '( %s -> %s )' % (ps, CONCL('y')))
    # the instance at y
    yin = w.s([yn, w.inst('fzonn0p1')], 'syl', '( %s -> y e. ( 0 ..^ ( y + 1 ) ) )' % ps)
    g1 = w.s([], 'fveq2', '( i = y -> ( U ` i ) = ( U ` y ) )')
    g2 = w.s([g1], 'eleq1d', '( i = y -> ( ( U ` i ) e. NN0 <-> ( U ` y ) e. NN0 ) )')
    g3 = w.s([], 'fveq2', '( i = y -> ( I ` i ) = ( I ` y ) )')
    g4 = w.s([], 'oveq1', '( i = y -> ( i + 1 ) = ( y + 1 ) )')
    g5 = w.s([g4], 'fveq2d', '( i = y -> ( I ` ( i + 1 ) ) = ( I ` ( y + 1 ) ) )')
    g6 = w.s([g5, g1], 'opeq12d', '( i = y -> <. ( I ` ( i + 1 ) ) , ( U ` i ) >. = <. ( I ` ( y + 1 ) ) , ( U ` y ) >. )')
    g7 = w.s([g3, g6], 'breq12d', '( i = y -> ( %s <-> %s ) )' % (TRI('( I ` i )', '( I ` ( i + 1 ) )', UF('i')), TRI('( I ` y )', '( I ` ( y + 1 ) )', UF('y'))))
    g8 = w.s([g2, g7], 'anbi12d', '( i = y -> ( %s <-> %s ) )' % (BODY('i'), BODY('y')))
    at = w.s([g8, ral1, yin], 'rspcdva', '( %s -> %s )' % (ps, BODY('y')))
    un = w.s([at], 'simpld', '( %s -> ( U ` y ) e. NN0 )' % ps)
    tr = w.s([at], 'simprd', '( %s -> %s )' % (ps, TRI('( I ` y )', '( I ` ( y + 1 ) )', UF('y'))))
    SUMY = '( %s + ( U ` y ) )' % SM('y')
    seq = w.s([phm, c0, tr, w.inst('tm2hseq')], 'syl3anc', '( %s -> %s )' % (ps, HRI(Y1, SUMY)))
    # the sum split
    yuz = w.s([yn, w.inst('elnn0uz')], 'sylib', '( %s -> y e. ( ZZ>= ` 0 ) )' % ps)
    UN = '( ( 0 ..^ y ) u. { y } )'
    spl = w.s([yuz, w.inst('fzosplitsn')], 'syl', '( %s -> ( 0 ..^ ( y + 1 ) ) = %s )' % (ps, UN))
    fi = w.s([], 'fzofi', '( 0 ..^ y ) e. Fin'); fia = w.s([fi], 'a1i', '( %s -> ( 0 ..^ y ) e. Fin )' % ps)
    nl = w.s([], 'fzonel', '-. y e. ( 0 ..^ y )'); nel = w.s([nl], 'nelir', 'y e/ ( 0 ..^ y )')
    nela = w.s([nel], 'a1i', '( %s -> y e/ ( 0 ..^ y ) )' % ps)
    yy = w.s([yn, nela], 'jca', '( %s -> ( y e. NN0 /\\ y e/ ( 0 ..^ y ) ) )' % ps)
    im1 = w.s([], 'simpl', '( %s -> ( U ` i ) e. NN0 )' % BODY('i'))
    im2 = w.s([im1, w.inst('nn0z')], 'syl', '( %s -> ( U ` i ) e. ZZ )' % BODY('i'))
    rz = w.s([im2], 'ralimi', '( %s -> A. i e. ( 0 ..^ ( y + 1 ) ) ( U ` i ) e. ZZ )' % RAL(Y1))
    ralz1 = w.s([ral1, rz], 'syl', '( %s -> A. i e. ( 0 ..^ ( y + 1 ) ) ( U ` i ) e. ZZ )' % ps)
    req = w.s([spl], 'raleqdv', '( %s -> ( A. i e. ( 0 ..^ ( y + 1 ) ) ( U ` i ) e. ZZ <-> A. i e. %s ( U ` i ) e. ZZ ) )' % (ps, UN))
    ralz2 = w.s([req, ralz1], 'mpbid', '( %s -> A. i e. %s ( U ` i ) e. ZZ )' % (ps, UN))
    CSB = '[_ y / i ]_ ( U ` i )'
    sp = w.s([fia, yy, ralz2, w.inst('fsumsplitsnun')], 'syl3anc', '( %s -> sum_ i e. %s ( U ` i ) = ( %s + %s ) )' % (ps, UN, SM('y'), CSB))
    cb = w.s([], 'csbfv', '%s = ( U ` y )' % CSB); cba = w.s([cb], 'a1i', '( %s -> %s = ( U ` y ) )' % (ps, CSB))
    ov = w.s([cba], 'oveq2d', '( %s -> ( %s + %s ) = %s )' % (ps, SM('y'), CSB, SUMY))
    dom = w.s([spl], 'sumeq1d', '( %s -> %s = sum_ i e. %s ( U ` i ) )' % (ps, SM(Y1), UN))
    t1 = w.s([sp, ov], 'eqtrd', '( %s -> sum_ i e. %s ( U ` i ) = %s )' % (ps, UN, SUMY))
    tot = w.s([dom, t1], 'eqtrd', '( %s -> %s = %s )' % (ps, SM(Y1), SUMY))
    totc = w.s([tot], 'eqcomd', '( %s -> %s = %s )' % (ps, SUMY, SM(Y1)))
    o2 = w.s([totc], 'opeq2d', '( %s -> <. ( I ` ( y + 1 ) ) , %s >. = <. ( I ` ( y + 1 ) ) , %s >. )' % (ps, SUMY, SM(Y1)))
    b2 = w.s([o2], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ps, HRI(Y1, SUMY), HRI(Y1, SM(Y1))))
    fin = w.s([b2, seq], 'mpbid', '( %s -> %s )' % (ps, CONCL(Y1)))
    e1 = w.s([fin], 'ex', '( ( y e. NN0 /\\ %s ) -> ( %s -> %s ) )' % (ANTE(Y1), PH('y'), CONCL(Y1)))
    e2 = w.s([e1], 'ex', '( y e. NN0 -> ( %s -> ( %s -> %s ) ) )' % (ANTE(Y1), PH('y'), CONCL(Y1)))
    step = w.s([e2], 'com23', '( y e. NN0 -> ( %s -> %s ) )' % (PH('y'), PH(Y1)))
    w.qed(cs + [base, step], 'nn0ind', ST_HITSUM)
    return w.run()


if __name__ == '__main__':
    if want('tm2hitsum'): tm2hitsum()
