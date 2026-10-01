"""T1: the iterate-of-a-sum lemma and the value/unfolding of df-tm2hr."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def relexpaddfv():
    lab = 'relexpaddfv'
    ph = ('( ( B e. V /\\ G : B --> B ) /\\ ( N e. NN0 /\\ M e. NN0 ) /\\ X e. B )')
    w = W(lab, 'The iterate of a function at a sum of exponents: the outer '
               'iterate applied to the inner one.  The step-counting engine of '
               'the machine layer.')
    bv = w.s([], 'simp1l', '( %s -> B e. V )' % ph)
    gf = w.s([], 'simp1r', '( %s -> G : B --> B )' % ph)
    nn = w.s([], 'simp2l', '( %s -> N e. NN0 )' % ph)
    mm = w.s([], 'simp2r', '( %s -> M e. NN0 )' % ph)
    xb = w.s([], 'simp3', '( %s -> X e. B )' % ph)
    gex = w.s([gf, bv, w.inst('fex')], 'syl2anc', '( %s -> G e. _V )' % ph)
    gfun = w.s([gf, w.inst('ffun')], 'syl', '( %s -> Fun G )' % ph)
    grel = w.s([gfun, w.inst('funrel')], 'syl', '( %s -> Rel G )' % ph)
    rimp = w.s([grel], 'a1d', '( %s -> ( ( N + M ) = 1 -> Rel G ) )' % ph)
    tri = w.s([mm, gex, rimp], '3jca',
              '( %s -> ( M e. NN0 /\\ G e. _V /\\ ( ( N + M ) = 1 -> Rel G ) ) )' % ph)
    pair = w.s([nn, tri], 'jca',
               '( %s -> ( N e. NN0 /\\ ( M e. NN0 /\\ G e. _V /\\ ( ( N + M ) = 1 -> Rel G ) ) ) )' % ph)
    add = w.s([pair, w.inst('relexpaddg')], 'syl',
              '( %s -> ( ( G ^r N ) o. ( G ^r M ) ) = ( G ^r ( N + M ) ) )' % ph)
    addc = w.s([add], 'eqcomd',
               '( %s -> ( G ^r ( N + M ) ) = ( ( G ^r N ) o. ( G ^r M ) ) )' % ph)
    eq1 = w.s([addc], 'fveq1d',
              '( %s -> ( ( G ^r ( N + M ) ) ` X ) = ( ( ( G ^r N ) o. ( G ^r M ) ) ` X ) )' % ph)
    bg = w.s([bv, gf], 'jca', '( %s -> ( B e. V /\\ G : B --> B ) )' % ph)
    rf0 = w.s([mm, w.inst('relexpfd')], 'syl',
              '( %s -> ( ( B e. V /\\ G : B --> B ) -> ( G ^r M ) : B --> B ) )' % ph)
    gmf = w.s([bg, rf0], 'mpd', '( %s -> ( G ^r M ) : B --> B )' % ph)
    co = w.s([gmf, xb, w.inst('fvco3')], 'syl2anc',
             '( %s -> ( ( ( G ^r N ) o. ( G ^r M ) ) ` X ) = ( ( G ^r N ) ` ( ( G ^r M ) ` X ) ) )' % ph)
    w.qed([eq1, co], 'eqtrd',
          '( %s -> ( ( G ^r ( N + M ) ) ` X ) = ( ( G ^r N ) ` ( ( G ^r M ) ` X ) ) )' % ph)
    return w.run()


if __name__ == '__main__':
    if want('relexpaddfv'): relexpaddfv()


def tm2hrval():
    lab = 'tm2hrval'
    ph = '( T e. V /\\ M e. W )'
    val = HRVAL('T', 'M')
    w = W(lab, 'The value of the Hoare-triple relation of a machine.')
    A = '( t = T /\\ m = M )'
    l1 = w.s([], 'simpl', '( %s -> t = T )' % A)
    l2 = w.s([], 'simpr', '( %s -> m = M )' % A)
    st, new = w.congr(HRVAL('t', 'm'), {'t': 'T', 'm': 'M'}, A, {'t': l1, 'm': l2})
    assert new == val, new
    t = w.s([], 'elex', '( T e. V -> T e. _V )')
    m = w.s([], 'elex', '( M e. W -> M e. _V )')
    ta = w.s([t], 'adantr', '( %s -> T e. _V )' % ph)
    ma = w.s([m], 'adantl', '( %s -> M e. _V )' % ph)
    ce = w.s([], 'fvex', '%s e. _V' % CFG('T'))
    pe = w.s([ce], 'pwex', '~P %s e. _V' % CFG('T'))
    n0 = w.s([], 'nn0ex', 'NN0 e. _V')
    x1 = w.s([pe, n0], 'xpex', '( ~P %s X. NN0 ) e. _V' % CFG('T'))
    x2 = w.s([pe, x1], 'xpex', '%s e. _V' % PWX('T'))
    ie = w.s([x2], 'inex2', '%s e. _V' % val)
    se = w.s([ie], 'a1i', '( %s -> %s e. _V )' % (ph, val))
    df = w.s([], 'df-tm2hr', 'TM2Hoare = ( t e. _V , m e. _V |-> %s )' % HRVAL('t', 'm'))
    ov = w.s([st, df], 'ovmpoga',
             '( ( T e. _V /\\ M e. _V /\\ %s e. _V ) -> ( T TM2Hoare M ) = %s )' % (val, val))
    w.qed([ta, ma, se, ov], 'syl3anc', '( %s -> ( T TM2Hoare M ) = %s )' % (ph, val))
    return w.run()


    if want('tm2hrval'): tm2hrval()


def tm2hrbr():
    lab = 'tm2hrbr'
    ph = '( ( T e. V /\\ M e. W ) /\\ ( C e. X /\\ D e. Y /\\ N e. Z ) )'
    OP = OPAB('T', 'M')
    PW = PWX('T')
    OPN = '<. C , <. D , N >. >.'
    bodyCY = BODY('T', 'M', 'C', '( 1st ` y )', '( 2nd ` y )')
    bodyCP = BODY('T', 'M', 'C', '( 1st ` <. D , N >. )', '( 2nd ` <. D , N >. )')
    bodyF = BODY('T', 'M', 'C', 'D', 'N')
    w = W(lab, 'The Hoare triple of the machine layer unfolded: the typing it '
               'carries and the run condition on every configuration of the '
               'precondition class.')
    # opelopabg hypotheses
    h1, b1 = w.wcongr(BODY('T', 'M', 'c', '( 1st ` y )', '( 2nd ` y )'), {'c': 'C'},
                      'c = C', {'c': w.s([], 'id', '( c = C -> c = C )')})
    assert b1 == bodyCY, b1
    h2, b2 = w.wcongr(bodyCY, {'y': '<. D , N >.'}, 'y = <. D , N >.',
                      {'y': w.s([], 'id', '( y = <. D , N >. -> y = <. D , N >. )')})
    assert b2 == bodyCP, b2
    cx = w.s([], 'simpr1', '( %s -> C e. X )' % ph)
    dy = w.s([], 'simpr2', '( %s -> D e. Y )' % ph)
    nz = w.s([], 'simpr3', '( %s -> N e. Z )' % ph)
    pex = w.s([], 'opex', '<. D , N >. e. _V')
    pexa = w.s([pex], 'a1i', '( %s -> <. D , N >. e. _V )' % ph)
    op = w.s([h1, h2], 'opelopabg',
             '( ( C e. X /\\ <. D , N >. e. _V ) -> ( %s e. %s <-> %s ) )' % (OPN, OP, bodyCP))
    op1 = w.s([cx, pexa, op], 'syl2anc', '( %s -> ( %s e. %s <-> %s ) )' % (ph, OPN, OP, bodyCP))
    # evaluate the projections of <. D , N >.
    setmap = {'D': w.s([dy], 'elexd', '( %s -> D e. _V )' % ph),
              'N': w.s([nz], 'elexd', '( %s -> N e. _V )' % ph)}
    ev, res = evaluate(w, ph, bodyCP, setmap, wff=True)
    assert res == bodyF, res
    op2 = w.s([op1, ev], 'bitrd', '( %s -> ( %s e. %s <-> %s ) )' % (ph, OPN, OP, bodyF))
    # the typing factor
    x1 = w.s([], 'opelxp', '( %s e. %s <-> ( C e. ~P %s /\\ <. D , N >. e. ( ~P %s X. NN0 ) ) )'
             % (OPN, PW, CFG('T'), CFG('T')))
    x1a = w.s([x1], 'a1i', '( %s -> ( %s e. %s <-> ( C e. ~P %s /\\ <. D , N >. e. ( ~P %s X. NN0 ) ) ) )'
              % (ph, OPN, PW, CFG('T'), CFG('T')))
    x2 = w.s([], 'opelxp', '( <. D , N >. e. ( ~P %s X. NN0 ) <-> ( D e. ~P %s /\\ N e. NN0 ) )'
             % (CFG('T'), CFG('T')))
    x2a = w.s([x2], 'a1i', '( %s -> ( <. D , N >. e. ( ~P %s X. NN0 ) <-> ( D e. ~P %s /\\ N e. NN0 ) ) )'
              % (ph, CFG('T'), CFG('T')))
    pc = w.s([cx, w.inst('elpwg')], 'syl', '( %s -> ( C e. ~P %s <-> C C_ %s ) )' % (ph, CFG('T'), CFG('T')))
    pd = w.s([dy, w.inst('elpwg')], 'syl', '( %s -> ( D e. ~P %s <-> D C_ %s ) )' % (ph, CFG('T'), CFG('T')))
    pd2 = w.s([pd], 'anbi1d', '( %s -> ( ( D e. ~P %s /\\ N e. NN0 ) <-> ( D C_ %s /\\ N e. NN0 ) ) )'
              % (ph, CFG('T'), CFG('T')))
    x3 = w.s([x2a, pd2], 'bitrd', '( %s -> ( <. D , N >. e. ( ~P %s X. NN0 ) <-> ( D C_ %s /\\ N e. NN0 ) ) )'
             % (ph, CFG('T'), CFG('T')))
    x4 = w.s([pc, x3], 'anbi12d',
             '( %s -> ( ( C e. ~P %s /\\ <. D , N >. e. ( ~P %s X. NN0 ) ) <-> ( C C_ %s /\\ ( D C_ %s /\\ N e. NN0 ) ) ) )'
             % (ph, CFG('T'), CFG('T'), CFG('T'), CFG('T')))
    x5 = w.s([x1a, x4], 'bitrd',
             '( %s -> ( %s e. %s <-> ( C C_ %s /\\ ( D C_ %s /\\ N e. NN0 ) ) ) )'
             % (ph, OPN, PW, CFG('T'), CFG('T')))
    a3 = w.s([], '3anass', '( %s <-> ( C C_ %s /\\ ( D C_ %s /\\ N e. NN0 ) ) )'
             % (TYP('C', 'D', 'N', 'T'), CFG('T'), CFG('T')))
    a3a = w.s([a3], 'a1i', '( %s -> ( %s <-> ( C C_ %s /\\ ( D C_ %s /\\ N e. NN0 ) ) ) )'
              % (ph, TYP('C', 'D', 'N', 'T'), CFG('T'), CFG('T')))
    x6 = w.s([x5, a3a], 'bitr4d', '( %s -> ( %s e. %s <-> %s ) )' % (ph, OPN, PW, TYP('C', 'D', 'N', 'T')))
    # glue
    ei = w.s([], 'elin', '( %s e. ( %s i^i %s ) <-> ( %s e. %s /\\ %s e. %s ) )' % (OPN, OP, PW, OPN, OP, OPN, PW))
    eia = w.s([ei], 'a1i', '( %s -> ( %s e. ( %s i^i %s ) <-> ( %s e. %s /\\ %s e. %s ) ) )'
              % (ph, OPN, OP, PW, OPN, OP, OPN, PW))
    bb = w.s([op2, x6], 'anbi12d',
             '( %s -> ( ( %s e. %s /\\ %s e. %s ) <-> ( %s /\\ %s ) ) )'
             % (ph, OPN, OP, OPN, PW, bodyF, TYP('C', 'D', 'N', 'T')))
    cm = w.s([], 'ancom', '( ( %s /\\ %s ) <-> ( %s /\\ %s ) )'
             % (bodyF, TYP('C', 'D', 'N', 'T'), TYP('C', 'D', 'N', 'T'), bodyF))
    cma = w.s([cm], 'a1i', '( %s -> ( ( %s /\\ %s ) <-> ( %s /\\ %s ) ) )'
              % (ph, bodyF, TYP('C', 'D', 'N', 'T'), TYP('C', 'D', 'N', 'T'), bodyF))
    g1 = w.s([eia, bb], 'bitrd', '( %s -> ( %s e. ( %s i^i %s ) <-> ( %s /\\ %s ) ) )'
             % (ph, OPN, OP, PW, bodyF, TYP('C', 'D', 'N', 'T')))
    g2 = w.s([g1, cma], 'bitrd', '( %s -> ( %s e. ( %s i^i %s ) <-> ( %s /\\ %s ) ) )'
             % (ph, OPN, OP, PW, TYP('C', 'D', 'N', 'T'), bodyF))
    # the br
    db = w.s([], 'df-br', '( %s <-> %s e. ( T TM2Hoare M ) )' % (HR('C', 'T', 'M', 'D', 'N'), OPN))
    dba = w.s([db], 'a1i', '( %s -> ( %s <-> %s e. ( T TM2Hoare M ) ) )' % (ph, HR('C', 'T', 'M', 'D', 'N'), OPN))
    vl = w.s([], 'simpl', '( %s -> ( T e. V /\\ M e. W ) )' % ph)
    val = w.s([vl, w.inst('tm2hrval')], 'syl', '( %s -> ( T TM2Hoare M ) = ( %s i^i %s ) )' % (ph, OP, PW))
    el = w.s([val], 'eleq2d', '( %s -> ( %s e. ( T TM2Hoare M ) <-> %s e. ( %s i^i %s ) ) )' % (ph, OPN, OPN, OP, PW))
    g3 = w.s([dba, el], 'bitrd', '( %s -> ( %s <-> %s e. ( %s i^i %s ) ) )' % (ph, HR('C', 'T', 'M', 'D', 'N'), OPN, OP, PW))
    w.qed([g3, g2], 'bitrd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )'
          % (ph, HR('C', 'T', 'M', 'D', 'N'), TYP('C', 'D', 'N', 'T'), bodyF))
    return w.run()


    if want('tm2hrbr'): tm2hrbr()
