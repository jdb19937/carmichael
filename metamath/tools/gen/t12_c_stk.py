"""T12: generic lemmas for the final stacks.

  t12fzo8    ( 0 ..^ 8 ) as ( 0 ..^ 4 ) and the singletons 4 5 6 7
  t12stkeq   two stack functions of the eight-stack machine with the same eight values are equal
  t12ini     the value of ` INIT( K , W ) ` at a stack index

    MM_DB=sorties/t12.mm python3 tools/gen/t12_c_stk.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *

SEL = sys.argv[1:]
FZ8 = '( ( ( ( ( 0 ..^ 4 ) u. { 4 } ) u. { 5 } ) u. { 6 } ) u. { 7 } )'
ST_FZO8 = '( 0 ..^ 8 ) = %s' % FZ8
GEQ_ = '( 1st ` ( 1st ` T ) ) = TMGam'
EQ8 = lambda A, B: ((('( %s ` 0 ) = ( %s ` 0 )' % (A, B), '( %s ` 1 ) = ( %s ` 1 )' % (A, B)),
                     ('( %s ` 2 ) = ( %s ` 2 )' % (A, B), '( %s ` 3 ) = ( %s ` 3 )' % (A, B))),
                    (('( %s ` 4 ) = ( %s ` 4 )' % (A, B), '( %s ` 5 ) = ( %s ` 5 )' % (A, B)),
                     ('( %s ` 6 ) = ( %s ` 6 )' % (A, B), '( %s ` 7 ) = ( %s ` 7 )' % (A, B))))
TREE_SE = ((('T e. V', GEQ_), ('A e. ( TM2Stk ` T )', 'B e. ( TM2Stk ` T )')), EQ8('A', 'B'))
ST_STKEQ = '( %s -> A = B )' % cj(TREE_SE)
INITK = '( k e. %s |-> if ( k = K , W , (/) ) )' % DOMT
ST_INI = ('( ( %s /\\ ( J e. ( 0 ..^ 8 ) /\\ W e. _V ) ) -> ( %s ` J ) = if ( J = K , W , (/) ) )' % (GEQ_, INITK))


def t12fzo8():
    lab = 't12fzo8'
    w = W(lab, 'The eight stack indices as ` ( 0 ..^ 4 ) ` and four singletons (for the extensionality of the '
               'stack functions, ~ t12stkeq ).')
    s = w.s
    prev = None
    eqs = {}
    for n in (7, 6, 5, 4):
        un = s([s([], '%dnn0' % n, '%d e. NN0' % n), s([], 'elnn0uz', '( %d e. NN0 <-> %d e. ( ZZ>= ` 0 ) )' % (n, n))], 'mpbi',
               '%d e. ( ZZ>= ` 0 )' % n)
        sp = s([un, w.inst('fzosplitsn')], 'ax-mp', '( 0 ..^ ( %d + 1 ) ) = ( ( 0 ..^ %d ) u. { %d } )' % (n, n, n))
        p1 = s([s([], '%dp1e%d' % (n, n + 1), '( %d + 1 ) = %d' % (n, n + 1))], 'oveq2i', '( 0 ..^ ( %d + 1 ) ) = ( 0 ..^ %d )' % (n, n + 1))
        eqs[n + 1] = s([p1, sp], 'eqtr3i', '( 0 ..^ %d ) = ( ( 0 ..^ %d ) u. { %d } )' % (n + 1, n, n))
    # ( 0 ..^ 6 ) = ( ( ( 0 ..^ 4 ) u. { 4 } ) u. { 5 } )
    t6 = '( ( ( 0 ..^ 4 ) u. { 4 } ) u. { 5 } )'
    e6 = s([eqs[6], s([eqs[5]], 'uneq1i', '( ( 0 ..^ 5 ) u. { 5 } ) = %s' % t6)], 'eqtri', '( 0 ..^ 6 ) = %s' % t6)
    t7 = '( %s u. { 6 } )' % t6
    e7 = s([eqs[7], s([e6], 'uneq1i', '( ( 0 ..^ 6 ) u. { 6 } ) = %s' % t7)], 'eqtri', '( 0 ..^ 7 ) = %s' % t7)
    w.qed([eqs[8], s([e7], 'uneq1i', '( ( 0 ..^ 7 ) u. { 7 } ) = %s' % FZ8)], 'eqtri', ST_FZO8)
    return w.run()


def numex(w, n):
    if n <= 3:
        return w.s([], {0: 'c0ex', 1: '1ex', 2: '2ex', 3: '3ex'}[n], '%d e. _V' % n)
    return w.s([w.s([], '%dre' % n, '%d e. RR' % n)], 'elexi', '%d e. _V' % n)


def t12stkeq():
    lab = 't12stkeq'
    ph = cj(TREE_SE)
    w = W(lab, 'Two stack functions of the eight-stack machine ( ` ( 1st ` ( 1st ` T ) ) = TMGam ` ) with the same '
               'values at ` 0 ... 7 ` are equal (Lean: ` funext ` with ` fin_cases ` ).')
    s = w.s
    c = Ctx(w, ph, TREE_SE)
    tv, geq, an, bn = c['T e. V'], c[GEQ_], c['A e. ( TM2Stk ` T )'], c['B e. ( TM2Stk ` T )']
    dg = s([geq, w.inst('tmcdg')], 'syl', '( %s -> %s = ( 0 ..^ 8 ) )' % (ph, DOMT))
    fns = {}
    for X, xn in (('A', an), ('B', bn)):
        f0 = s([tv, xn, w.inst('tm2stkfn')], 'syl2anc', '( %s -> %s Fn %s )' % (ph, X, DOMT))
        fns[X] = s([f0, s([dg], 'fneq2d', '( %s -> ( %s Fn %s <-> %s Fn ( 0 ..^ 8 ) ) )' % (ph, X, DOMT, X))], 'mpbid',
                   '( %s -> %s Fn ( 0 ..^ 8 ) )' % (ph, X))
    PHI = '( A ` k ) = ( B ` k )'
    RAL = lambda X: 'A. k e. %s %s' % (X, PHI)

    def sub(n):
        """( k = n -> ( PHI <-> ( A ` n ) = ( B ` n ) ) )"""
        a = s([], 'fveq2', '( k = %d -> ( A ` k ) = ( A ` %d ) )' % (n, n))
        b = s([], 'fveq2', '( k = %d -> ( B ` k ) = ( B ` %d ) )' % (n, n))
        return s([a, b], 'eqeq12d', '( k = %d -> ( %s <-> ( A ` %d ) = ( B ` %d ) ) )' % (n, PHI, n, n))

    def val(n):
        return c['( A ` %d ) = ( B ` %d )' % (n, n)]

    def ral_sn(n):
        r = s([numex(w, n), sub(n)], 'ralsn', '( %s <-> ( A ` %d ) = ( B ` %d ) )' % (RAL('{ %d }' % n), n, n))
        return s([val(n), r], 'sylibr', '( %s -> %s )' % (ph, RAL('{ %d }' % n)))

    def ral_pr(a, b):
        X = '{ %d , %d }' % (a, b)
        r = s([numex(w, a), numex(w, b), sub(a), sub(b)], 'ralpr',
              '( %s <-> ( ( A ` %d ) = ( B ` %d ) /\\ ( A ` %d ) = ( B ` %d ) ) )' % (RAL(X), a, a, b, b))
        j = s([val(a), val(b)], 'jca', '( %s -> ( ( A ` %d ) = ( B ` %d ) /\\ ( A ` %d ) = ( B ` %d ) ) )' % (ph, a, a, b, b))
        return s([j, r], 'sylibr', '( %s -> %s )' % (ph, RAL(X)))

    def ral_un(X, Y, rx, ry):
        U = '( %s u. %s )' % (X, Y)
        r = s([], 'ralunb', '( %s <-> ( %s /\\ %s ) )' % (RAL(U), RAL(X), RAL(Y)))
        j = s([rx, ry], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, RAL(X), RAL(Y)))
        return U, s([j, r], 'sylibr', '( %s -> %s )' % (ph, RAL(U)))

    U4, r4 = ral_un('{ 0 , 1 }', '{ 2 , 3 }', ral_pr(0, 1), ral_pr(2, 3))
    q4 = s([s([], 'fzo0to42pr', '( 0 ..^ 4 ) = %s' % U4)], 'raleqi', '( %s <-> %s )' % (RAL('( 0 ..^ 4 )'), RAL(U4)))
    r = s([r4, q4], 'sylibr', '( %s -> %s )' % (ph, RAL('( 0 ..^ 4 )')))
    X = '( 0 ..^ 4 )'
    for n in (4, 5, 6, 7):
        X, r = ral_un(X, '{ %d }' % n, r, ral_sn(n))
    assert X == FZ8
    q8 = s([s([], 't12fzo8', ST_FZO8)], 'raleqi', '( %s <-> %s )' % (RAL('( 0 ..^ 8 )'), RAL(FZ8)))
    r8 = s([r, q8], 'sylibr', '( %s -> %s )' % (ph, RAL('( 0 ..^ 8 )')))
    ef = s([fns['A'], fns['B'], w.inst('eqfnfv')], 'syl2anc', '( %s -> ( A = B <-> %s ) )' % (ph, RAL('( 0 ..^ 8 )')))
    w.qed([r8, ef], 'mpbird', ST_STKEQ)
    return w.run()


def t12ini():
    lab = 't12ini'
    ph = '( %s /\\ ( J e. ( 0 ..^ 8 ) /\\ W e. _V ) )' % GEQ_
    w = W(lab, 'The value of Lean\'s ` Frag.initStacks K W ` (the stacks of ~ df-tm2init ) at a stack index.')
    s = w.s
    g = s([], 'simpl', '( %s -> %s )' % (ph, GEQ_))
    j8 = s([], 'simprl', '( %s -> J e. ( 0 ..^ 8 ) )' % ph)
    wv = s([], 'simprr', '( %s -> W e. _V )' % ph)
    dg = s([g, w.inst('tmcdg')], 'syl', '( %s -> %s = ( 0 ..^ 8 ) )' % (ph, DOMT))
    jd = s([j8, s([dg], 'eqcomd', '( %s -> ( 0 ..^ 8 ) = %s )' % (ph, DOMT))], 'eleqtrd', '( %s -> J e. %s )' % (ph, DOMT))
    IFJ = 'if ( J = K , W , (/) )'
    ifx = s([wv, s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % ph)], 'ifcld', '( %s -> %s e. _V )' % (ph, IFJ))
    eq = s([], 'eqeq1', '( k = J -> ( k = K <-> J = K ) )')
    ife = s([eq], 'ifbid', '( k = J -> if ( k = K , W , (/) ) = %s )' % IFJ)
    df = s([], 'eqid', '%s = %s' % (INITK, INITK))
    fv = s([ife, df], 'fvmptg', '( ( J e. %s /\\ %s e. _V ) -> ( %s ` J ) = %s )' % (DOMT, IFJ, INITK, IFJ))
    w.qed([jd, ifx, fv], 'syl2anc', ST_INI)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
