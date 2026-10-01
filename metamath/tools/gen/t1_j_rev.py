"""T1: the machine model's test program `revmach` re-derived as an
instantiation of the fragment calculus, for the cost comparison."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

TA = '( A |_| 1o )'
GREV = '{ <. (/) , A >. , <. 1o , A >. }'
TREV = '<. <. %s , 1o >. , %s >.' % (GREV, TA)
POPF = '( 2nd |` ( %s X. %s ) )' % (TA, TA)
BRF = '( v e. %s |-> if ( v = ( inr ` (/) ) , (/) , 1o ) )' % TA
PUSHF = '( v e. %s |-> if ( v = ( inr ` (/) ) , Z , ( 2nd ` v ) ) )' % TA
GOTOF = '( %s X. { (/) } )' % TA
LOADF = '( %s X. { ( inr ` (/) ) } )' % TA
STMTREV = POP('(/)', POPF, BRANCH(BRF, PUSH('1o', PUSHF, GOTO(GOTOF)), LOAD(LOADF, HALT)))
MREV = '{ <. (/) , %s >. }' % STMTREV
MACH = '<. <. %s , <. (/) , 1o >. >. , <. <. (/) , ( inr ` (/) ) >. , %s >. >.' % (TREV, MREV)
PHREV = '( %s e. V /\\ %s : 1o --> ( TM2Stmt ` %s ) )' % (TREV, MREV, TREV)
TL = lambda x: '( %s substr <. 1 , ( # ` %s ) >. )' % (x, x)
STK2 = lambda u, ww: '{ <. (/) , %s >. , <. 1o , %s >. }' % (u, ww)
CLREV = lambda u, ww: '( { ( inl ` (/) ) } X. ( %s X. { %s } ) )' % (TA, STK2(u, ww))
JREV = ('( p e. _V |-> ( { ( inl ` (/) ) } X. ( %s X. { { <. (/) , ( 1st ` p ) >. , '
        '<. 1o , ( 2nd ` p ) >. } } ) ) )' % TA)


def revprog():
    lab = 'revprog'
    ph = '( A e. V /\\ Z e. A )'
    w = W(lab, 'The program of the reverse machine is a function from its one '
               'label to the statements.')
    st = w.s([], 'revstm', '( %s -> %s e. ( TM2Stmt ` %s ) )' % (ph, STMTREV, TREV))
    z0 = w.s([], '0ex', '(/) e. _V')
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. _V )' % ph)
    sv = w.s([], 'opex', '%s e. _V' % STMTREV)
    sva = w.s([sv], 'a1i', '( %s -> %s e. _V )' % (ph, STMTREV))
    bi = w.s([z0a, sva, w.inst('fsng')], 'syl2anc',
             '( %s -> ( %s : { (/) } --> { %s } <-> %s = %s ) )' % (ph, MREV, STMTREV, MREV, MREV))
    eqi = w.s([], 'eqid', '%s = %s' % (MREV, MREV))
    eqia = w.s([eqi], 'a1i', '( %s -> %s = %s )' % (ph, MREV, MREV))
    f1 = w.s([bi, eqia], 'mpbird', '( %s -> %s : { (/) } --> { %s } )' % (ph, MREV, STMTREV))
    d1 = w.s([], 'df1o2', '1o = { (/) }')
    d1a = w.s([d1], 'a1i', '( %s -> 1o = { (/) } )' % ph)
    d1c = w.s([d1a], 'eqcomd', '( %s -> { (/) } = 1o )' % ph)
    f2b = w.s([d1c], 'feq2d', '( %s -> ( %s : { (/) } --> { %s } <-> %s : 1o --> { %s } ) )'
              % (ph, MREV, STMTREV, MREV, STMTREV))
    f2 = w.s([f2b, f1], 'mpbid', '( %s -> %s : 1o --> { %s } )' % (ph, MREV, STMTREV))
    ss = w.s([st], 'snssd', '( %s -> { %s } C_ ( TM2Stmt ` %s ) )' % (ph, STMTREV, TREV))
    w.qed([f2, ss, w.inst('fss')], 'syl2anc', '( %s -> %s : 1o --> ( TM2Stmt ` %s ) )' % (ph, MREV, TREV))
    return w.run()


def revt2():
    lab = 'revt2'
    ph = 'A e. V'
    w = W(lab, 'The internal states of the reverse machine.')
    av = w.s([], 'id', '( %s -> A e. V )' % ph)
    p1 = w.s([], 'opex', '<. %s , 1o >. e. _V' % GREV)
    p1a = w.s([p1], 'a1i', '( %s -> <. %s , 1o >. e. _V )' % (ph, GREV))
    o1 = w.s([], '1oex', '1o e. _V')
    o1a = w.s([o1], 'a1i', '( %s -> 1o e. _V )' % ph)
    d1 = w.s([av, o1a, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (ph, TA))
    w.qed([p1a, d1, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (ph, TREV, TA))
    return w.run()


def revtl():
    lab = 'revtl'
    w = W(lab, 'The labels of the reverse machine.')
    ph = 'A e. V'
    av = w.s([], 'id', '( %s -> A e. V )' % ph)
    p1 = w.s([], 'opex', '<. %s , 1o >. e. _V' % GREV)
    p1a = w.s([p1], 'a1i', '( %s -> <. %s , 1o >. e. _V )' % (ph, GREV))
    o1 = w.s([], '1oex', '1o e. _V')
    o1a = w.s([o1], 'a1i', '( %s -> 1o e. _V )' % ph)
    d1 = w.s([av, o1a, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (ph, TA))
    f1 = w.s([p1a, d1, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = <. %s , 1o >. )' % (ph, TREV, GREV))
    f2 = w.s([f1], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` <. %s , 1o >. ) )' % (ph, TREV, GREV))
    pe = w.s([], 'prex', '%s e. _V' % GREV)
    pea = w.s([pe], 'a1i', '( %s -> %s e. _V )' % (ph, GREV))
    f3 = w.s([pea, o1a, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , 1o >. ) = 1o )' % (ph, GREV))
    w.qed([f2, f3], 'eqtrd', '( %s -> ( 2nd ` ( 1st ` %s ) ) = 1o )' % (ph, TREV))
    return w.run()


SREV = '( 2nd ` %s )' % TREV
LREV = '( 2nd ` ( 1st ` %s ) )' % TREV
STKREV = '( TM2Stk ` %s )' % TREV
CFGREV = '( TM2Cfg ` %s )' % TREV
PHMREV = '( %s e. _V /\\ %s : %s --> ( TM2Stmt ` %s ) )' % (TREV, MREV, LREV, TREV)
CL2 = lambda u, ww: '( { ( inl ` (/) ) } X. ( %s X. { %s } ) )' % (SREV, STK2(u, ww))


def revbase(w, ph, av, zv):
    """the reverse machine's standing facts under ph"""
    az = w.s([av, zv], 'jca', '( %s -> ( A e. V /\\ Z e. A ) )' % ph)
    prog = w.s([az, w.inst('revprog')], 'syl', '( %s -> %s : 1o --> ( TM2Stmt ` %s ) )' % (ph, MREV, TREV))
    tex = w.s([], 'opex', '%s e. _V' % TREV)
    texa = w.s([tex], 'a1i', '( %s -> %s e. _V )' % (ph, TREV))
    t2 = w.s([av, w.inst('revt2')], 'syl', '( %s -> %s = %s )' % (ph, SREV, TA))
    tl = w.s([av, w.inst('revtl')], 'syl', '( %s -> %s = 1o )' % (ph, LREV))
    tlc = w.s([tl], 'eqcomd', '( %s -> 1o = %s )' % (ph, LREV))
    fe = w.s([tlc], 'feq2d', '( %s -> ( %s : 1o --> ( TM2Stmt ` %s ) <-> %s : %s --> ( TM2Stmt ` %s ) ) )'
             % (ph, MREV, TREV, MREV, LREV, TREV))
    progc = w.s([fe, prog], 'mpbid', '( %s -> %s : %s --> ( TM2Stmt ` %s ) )' % (ph, MREV, LREV, TREV))
    phm = w.s([texa, progc], 'jca', '( %s -> %s )' % (ph, PHMREV))
    z0 = w.s([], '0lt1o', '(/) e. 1o')
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. 1o )' % ph)
    alcl = w.s([z0a, tl], 'eleqtrrd', '( %s -> (/) e. %s )' % (ph, LREV))
    return dict(az=az, phm=phm, t2=t2, tl=tl, alcl=alcl, texa=texa)


def revstk(w, ph, av, U, WW, ucl, wcl):
    """( ph -> { <. (/) , U >. , <. 1o , WW >. } e. ( TM2Stk ` TREV ) )"""
    j = w.s([ucl, wcl], 'jca', '( %s -> ( %s e. Word A /\\ %s e. Word A ) )' % (ph, U, WW))
    return w.s([av, j, w.inst('ppstk')], 'syl2anc', '( %s -> %s e. %s )' % (ph, STK2(U, WW), STKREV))


def tm2rvst1():
    lab = 'tm2rvst1'
    ph = '( ( ( A e. V /\\ Z e. A ) /\\ ( x e. Word A /\\ s e. Word A ) ) /\\ x =/= (/) )'
    D1 = STK2('x', 's')
    AC = '( <" ( x ` 0 ) "> ++ s )'
    D2 = STK2(TL('x'), AC)
    NV = '( inl ` ( x ` 0 ) )'
    RES = '<. ( inl ` (/) ) , <. %s , %s >. >.' % (NV, D2)
    Dpost = CL2(TL('x'), AC)
    w = W(lab, 'One iteration of the reverse machine as a Hoare triple of the '
               'fragment calculus: the label pops a letter of the input, pushes '
               'it on the output and returns to itself.  The machine model '
               'proves the same step as ~ revstep1 ; the calculus needs nothing '
               'else for the whole run.')
    az = w.s([], 'simpll', '( %s -> ( A e. V /\\ Z e. A ) )' % ph)
    av = w.s([az], 'simpld', '( %s -> A e. V )' % ph)
    zv = w.s([az], 'simprd', '( %s -> Z e. A )' % ph)
    xs = w.s([], 'simplr', '( %s -> ( x e. Word A /\\ s e. Word A ) )' % ph)
    xw = w.s([xs], 'simpld', '( %s -> x e. Word A )' % ph)
    sw = w.s([xs], 'simprd', '( %s -> s e. Word A )' % ph)
    xn = w.s([], 'simpr', '( %s -> x =/= (/) )' % ph)
    b = revbase(w, ph, av, zv)
    tlw = w.s([xw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word A )' % (ph, TL('x')))
    x0 = w.s([xw, xn, w.inst('wrdfv0')], 'syl2anc', '( %s -> ( x ` 0 ) e. A )' % ph)
    s1c = w.s([x0], 's1cld', '( %s -> <" ( x ` 0 ) "> e. Word A )' % ph)
    acw = w.s([s1c, sw, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word A )' % (ph, AC))
    d1cl = revstk(w, ph, av, 'x', 's', xw, sw)
    d2cl = revstk(w, ph, av, TL('x'), AC, tlw, acw)
    # the postcondition is a class of configurations
    ssr = w.s([], 'ssid', '%s C_ %s' % (SREV, SREV))
    ssra = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (ph, SREV, SREV))
    sd2 = w.s([d2cl], 'snssd', '( %s -> { %s } C_ %s )' % (ph, D2, STKREV))
    x2 = w.s([ssra, sd2, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ ( %s X. %s ) )' % (ph, SREV, D2, SREV, STKREV))
    dps = w.s([b['texa'], b['alcl'], x2, w.inst('tm2hcfgss')], 'syl3anc',
              '( %s -> %s C_ %s )' % (ph, Dpost, CFGREV))
    def body(av2):
        def L_(st, f):
            return w.s([st], 'adantr', '( %s -> %s )' % (av2, f))
        avv = L_(av, 'A e. V')
        zvv = L_(zv, 'Z e. A')
        xww = L_(xw, 'x e. Word A')
        sww = L_(sw, 's e. Word A')
        xnn = L_(xn, 'x =/= (/)')
        t2a = L_(b['t2'], '%s = %s' % (SREV, TA))
        d1a = L_(d1cl, '%s e. %s' % (D1, STKREV))
        d2a = L_(d2cl, '%s e. %s' % (D2, STKREV))
        x0a = L_(x0, '( x ` 0 ) e. A')
        vv = w.s([], 'simpr', '( %s -> g e. %s )' % (av2, SREV))
        vta = w.s([vv, t2a], 'eleqtrd', '( %s -> g e. %s )' % (av2, TA))
        azz = w.s([avv, zvv], 'jca', '( %s -> ( A e. V /\\ Z e. A ) )' % av2)
        tri = w.s([xww, xnn, sww], '3jca', '( %s -> ( x e. Word A /\\ x =/= (/) /\\ s e. Word A ) )' % av2)
        st1 = w.s([azz, tri, vta, w.inst('revstep1')], 'syl3anc',
                  '( %s -> ( ( %s TM2step %s ) ` <. ( inl ` (/) ) , <. g , %s >. >. ) = ( inl ` %s ) )'
                  % (av2, TREV, MREV, D1, RES))
        texb = w.s([b['texa']], 'adantr', '( %s -> %s e. _V )' % (av2, TREV))
        mex = w.s([], 'snex', '%s e. _V' % MREV)
        mexa = w.s([mex], 'a1i', '( %s -> %s e. _V )' % (av2, MREV))
        tm = w.s([texb, mexa], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (av2, TREV, MREV))
        alb = w.s([b['alcl']], 'adantr', '( %s -> (/) e. %s )' % (av2, LREV))
        pr = w.s([vv, d1a], 'opelxpd', '( %s -> <. g , %s >. e. ( %s X. %s ) )' % (av2, D1, SREV, STKREV))
        aj = w.s([alb, pr], 'jca', '( %s -> ( (/) e. %s /\\ <. g , %s >. e. ( %s X. %s ) ) )'
                 % (av2, LREV, D1, SREV, STKREV))
        sa1 = w.s([tm, aj, w.inst('tm2hsa1')], 'syl2anc',
                  '( %s -> ( ( %s TM2step %s ) ` <. ( inl ` (/) ) , <. g , %s >. >. ) = ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) ) )'
                  % (av2, TREV, MREV, D1, MREV, TREV, D1))
        eq1 = w.s([sa1, st1], 'eqtr3d',
                  '( %s -> ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) ) = ( inl ` %s ) )'
                  % (av2, MREV, TREV, D1, RES))
        ov = w.s([], 'ovex', '( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) e. _V' % (MREV, TREV, D1))
        ova = w.s([ov], 'a1i', '( %s -> ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) e. _V )' % (av2, MREV, TREV, D1))
        rex = w.s([], 'opex', '%s e. _V' % RES)
        rexa = w.s([rex], 'a1i', '( %s -> %s e. _V )' % (av2, RES))
        inj = w.s([ova, rexa, w.inst('inlinj')], 'syl2anc',
                  '( %s -> ( ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) ) = ( inl ` %s ) <-> ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) = %s ) )'
                  % (av2, MREV, TREV, D1, RES, MREV, TREV, D1, RES))
        eq = w.s([inj, eq1], 'mpbid',
                 '( %s -> ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) = %s )' % (av2, MREV, TREV, D1, RES))
        dj = w.s([x0a, w.inst('djulcl')], 'syl', '( %s -> %s e. %s )' % (av2, NV, TA))
        nvcl = w.s([dj, t2a], 'eleqtrrd', '( %s -> %s e. %s )' % (av2, NV, SREV))
        # the result is in the postcondition
        z0 = w.s([], '0lt1o', '(/) e. 1o')
        il = w.s([z0, w.inst('djulcl')], 'ax-mp', '( inl ` (/) ) e. ( 1o |_| 1o )')
        sn1 = w.s([], 'fvex', '( inl ` (/) ) e. _V')
        sn2 = w.s([sn1, w.inst('snidg')], 'ax-mp', '( inl ` (/) ) e. { ( inl ` (/) ) }')
        sn2a = w.s([sn2], 'a1i', '( %s -> ( inl ` (/) ) e. { ( inl ` (/) ) } )' % av2)
        d2v = w.s([d2a], 'elexd', '( %s -> %s e. _V )' % (av2, D2))
        sd = w.s([d2v, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (av2, D2, D2))
        p2 = w.s([nvcl, sd], 'opelxpd', '( %s -> <. %s , %s >. e. ( %s X. { %s } ) )' % (av2, NV, D2, SREV, D2))
        rescl = w.s([sn2a, p2], 'opelxpd', '( %s -> %s e. %s )' % (av2, RES, Dpost))
        return eq, RES, rescl
    hstepP(w, ph, TREV, MREV, '(/)', D1, Dpost, b['phm'], b['alcl'], dps, d1cl, body,
           phmtxt=PHMREV, v='g', a='h', t='k', qed=True)
    return w.run()


JREV2 = ('( p e. _V |-> ( { ( inl ` (/) ) } X. ( %s X. { { <. (/) , ( 1st ` p ) >. , '
         '<. 1o , ( 2nd ` p ) >. } } ) ) )' % SREV)


def cl2ex(w, ante, U, WW):
    a = w.s([], 'snex', '{ ( inl ` (/) ) } e. _V')
    b = w.s([], 'fvex', '%s e. _V' % SREV)
    c = w.s([], 'snex', '{ %s } e. _V' % STK2(U, WW))
    d = w.s([b, c], 'xpex', '( %s X. { %s } ) e. _V' % (SREV, STK2(U, WW)))
    e = w.s([a, d], 'xpex', '%s e. _V' % CL2(U, WW))
    return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, CL2(U, WW)))


def jrev(w, ante, U, WW, ucl, wcl):
    """( ante -> ( JREV2 ` <. U , WW >. ) = CL2(U,WW) )"""
    aq = '( %s /\\ p = <. %s , %s >. )' % (ante, U, WW)
    lp = w.s([], 'simpr', '( %s -> p = <. %s , %s >. )' % (aq, U, WW))
    body = '( { ( inl ` (/) ) } X. ( %s X. { { <. (/) , ( 1st ` p ) >. , <. 1o , ( 2nd ` p ) >. } } ) )' % SREV
    st, mid = W.congr(w, body, {'p': '<. %s , %s >.' % (U, WW)}, aq, {'p': lp})
    uv = w.s([ucl], 'elexd', '( %s -> %s e. _V )' % (ante, U))
    wv = w.s([wcl], 'elexd', '( %s -> %s e. _V )' % (ante, WW))
    uva = w.s([uv], 'adantr', '( %s -> %s e. _V )' % (aq, U))
    wva = w.s([wv], 'adantr', '( %s -> %s e. _V )' % (aq, WW))
    p1 = w.s([uva, wva, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (aq, U, WW, U))
    p2 = w.s([uva, wva, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (aq, U, WW, WW))
    ev, res = W.congr(w, mid, {}, aq, {},
                      rules={'( 1st ` <. %s , %s >. )' % (U, WW): (U, p1),
                             '( 2nd ` <. %s , %s >. )' % (U, WW): (WW, p2)})
    assert res == CL2(U, WW), res
    h2 = w.s([st, ev], 'eqtrd', '( %s -> %s = %s )' % (aq, body, CL2(U, WW)))
    eqi = w.s([], 'eqid', '%s = %s' % (JREV2, JREV2))
    opv = w.s([], 'opex', '<. %s , %s >. e. _V' % (U, WW))
    opva = w.s([opv], 'a1i', '( %s -> <. %s , %s >. e. _V )' % (ante, U, WW))
    cex = cl2ex(w, ante, U, WW)
    return w.s([eqi, h2, opva, cex], 'fvmptd2', '( %s -> ( %s ` <. %s , %s >. ) = %s )'
               % (ante, JREV2, U, WW, CL2(U, WW)))


def tm2rvloop():
    lab = 'tm2rvloop'
    ph = '( ( A e. V /\\ Z e. A ) /\\ W e. Word A )'
    phx = '( ( %s /\\ ( x e. Word A /\\ s e. Word A ) ) /\\ x =/= (/) )' % ph
    AC = '( <" ( x ` 0 ) "> ++ s )'
    HRx = HR('( %s ` <. x , s >. )' % JREV2, TREV, MREV, '( %s ` <. %s , %s >. )' % (JREV2, TL('x'), AC), '1')
    HYPJ = 'A. x e. Word A A. s e. Word A ( x =/= (/) -> %s )' % HRx
    ZCJ = 'A. s e. Word A ( %s ` <. (/) , s >. ) C_ %s' % (JREV2, CFGREV)
    w = W(lab, 'The whole run of the reverse machine before it halts, as an '
               'instantiation of ~ tm2hwrd2 .  The machine model spends '
               '~ revcfg , ~ revos , ~ revstepf , ~ revit and ~ revrun on this; '
               'the calculus spends one instantiation.')
    # the iteration hypothesis
    j1 = w.s([], 'simplll', '( %s -> ( A e. V /\\ Z e. A ) )' % phx)
    az1 = w.s([j1], 'simpld', '( %s -> A e. V )' % phx)
    zz1 = w.s([j1], 'simprd', '( %s -> Z e. A )' % phx)
    j2 = w.s([], 'simplr', '( %s -> ( x e. Word A /\\ s e. Word A ) )' % phx)
    xw1 = w.s([j2], 'simpld', '( %s -> x e. Word A )' % phx)
    sw1 = w.s([j2], 'simprd', '( %s -> s e. Word A )' % phx)
    xn1 = w.s([], 'simpr', '( %s -> x =/= (/) )' % phx)
    j3 = w.s([j1, j2], 'jca', '( %s -> ( ( A e. V /\\ Z e. A ) /\\ ( x e. Word A /\\ s e. Word A ) ) )' % phx)
    j4 = w.s([j3, xn1], 'jca',
             '( %s -> ( ( ( A e. V /\\ Z e. A ) /\\ ( x e. Word A /\\ s e. Word A ) ) /\\ x =/= (/) ) )' % phx)
    one = w.s([j4, w.inst('tm2rvst1')], 'syl', '( %s -> %s )'
              % (phx, HR(CL2('x', 's'), TREV, MREV, CL2(TL('x'), AC), '1')))
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word A )' % (phx, TL('x')))
    x01 = w.s([xw1, xn1, w.inst('wrdfv0')], 'syl2anc', '( %s -> ( x ` 0 ) e. A )' % phx)
    s1c1 = w.s([x01], 's1cld', '( %s -> <" ( x ` 0 ) "> e. Word A )' % phx)
    acw1 = w.s([s1c1, sw1, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word A )' % (phx, AC))
    jx = jrev(w, phx, 'x', 's', xw1, sw1)
    jt = jrev(w, phx, TL('x'), AC, tlw1, acw1)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` <. %s , %s >. ) , 1 >. = <. %s , 1 >. )'
             % (phx, JREV2, TL('x'), AC, CL2(TL('x'), AC)))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (phx, HR(CL2('x', 's'), TREV, MREV, '( %s ` <. %s , %s >. )' % (JREV2, TL('x'), AC), '1'),
                HR(CL2('x', 's'), TREV, MREV, CL2(TL('x'), AC), '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )'
             % (phx, HR(CL2('x', 's'), TREV, MREV, '( %s ` <. %s , %s >. )' % (JREV2, TL('x'), AC), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (phx, HRx, HR(CL2('x', 's'), TREV, MREV, '( %s ` <. %s , %s >. )' % (JREV2, TL('x'), AC), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (phx, HRx))
    ex1 = w.s([o2], 'ex', '( ( %s /\\ ( x e. Word A /\\ s e. Word A ) ) -> ( x =/= (/) -> %s ) )' % (ph, HRx))
    ex2 = w.s([ex1], 'anassrs', '( ( ( %s /\\ x e. Word A ) /\\ s e. Word A ) -> ( x =/= (/) -> %s ) )' % (ph, HRx))
    ex3 = w.s([ex2], 'ralrimiva', '( ( %s /\\ x e. Word A ) -> A. s e. Word A ( x =/= (/) -> %s ) )' % (ph, HRx))
    hyp = w.s([ex3], 'ralrimiva', '( %s -> %s )' % (ph, HYPJ))
    # the empty-word members are classes of configurations
    av = w.s([], 'simpll', '( %s -> A e. V )' % ph)
    zv = w.s([], 'simplr', '( %s -> Z e. A )' % ph)
    ww = w.s([], 'simpr', '( %s -> W e. Word A )' % ph)
    b = revbase(w, ph, av, zv)
    phs = '( %s /\\ s e. Word A )' % ph
    avs = w.s([av], 'adantr', '( %s -> A e. V )' % phs)
    sws = w.s([], 'simpr', '( %s -> s e. Word A )' % phs)
    w0 = w.s([], 'wrd0', '(/) e. Word A')
    w0s = w.s([w0], 'a1i', '( %s -> (/) e. Word A )' % phs)
    jzs = jrev(w, phs, '(/)', 's', w0s, sws)
    dz = revstk(w, phs, avs, '(/)', 's', w0s, sws)
    ssr = w.s([], 'ssid', '%s C_ %s' % (SREV, SREV))
    ssrs = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (phs, SREV, SREV))
    sd = w.s([dz], 'snssd', '( %s -> { %s } C_ %s )' % (phs, STK2('(/)', 's'), STKREV))
    xs2 = w.s([ssrs, sd, w.inst('xpss12')], 'syl2anc',
              '( %s -> ( %s X. { %s } ) C_ ( %s X. %s ) )' % (phs, SREV, STK2('(/)', 's'), SREV, STKREV))
    texs = w.s([b['texa']], 'adantr', '( %s -> %s e. _V )' % (phs, TREV))
    als = w.s([b['alcl']], 'adantr', '( %s -> (/) e. %s )' % (phs, LREV))
    cls = w.s([texs, als, xs2, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (phs, CL2('(/)', 's'), CFGREV))
    clj = w.s([jzs, cls], 'eqsstrd', '( %s -> ( %s ` <. (/) , s >. ) C_ %s )' % (phs, JREV2, CFGREV))
    zc = w.s([clj], 'ralrimiva', '( %s -> %s )' % (ph, ZCJ))
    # tm2hwrd2
    n1 = w.s([], '1nn0', '1 e. NN0')
    n1a = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([n1a, zc], 'jca', '( %s -> ( 1 e. NN0 /\\ %s ) )' % (ph, ZCJ))
    ant = w.s([b['phm'], pj, hyp], '3jca', '( %s -> ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) )'
              % (ph, PHMREV, ZCJ, HYPJ))
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word A )' % ph)
    xy = w.s([ww, w0a], 'jca', '( %s -> ( W e. Word A /\\ (/) e. Word A ) )' % ph)
    ant2 = w.s([ant, xy], 'jca', '( %s -> ( ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) /\\ ( W e. Word A /\\ (/) e. Word A ) ) )'
               % (ph, PHMREV, ZCJ, HYPJ))
    RV = '( ( reverse ` W ) ++ (/) )'
    run = w.s([ant2, w.inst('tm2hwrd2')], 'syl', '( %s -> %s )'
              % (ph, HR('( %s ` <. W , (/) >. )' % JREV2, TREV, MREV,
                        '( %s ` <. (/) , %s >. )' % (JREV2, RV), '( ( # ` W ) x. 1 )')))
    # unfold
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word A )' % ph)
    rid = w.s([rvc, w.inst('ccatrid')], 'syl', '( %s -> %s = ( reverse ` W ) )' % (ph, RV))
    rvw = w.s([rid, rvc], 'eqeltrd', '( %s -> %s e. Word A )' % (ph, RV))
    jw = jrev(w, ph, 'W', '(/)', ww, w0a)
    jz = jrev(w, ph, '(/)', RV, w0a, rvw)
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    q1 = w.s([jz, m1], 'opeq12d',
             '( %s -> <. ( %s ` <. (/) , %s >. ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )'
             % (ph, JREV2, RV, CL2('(/)', RV)))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , (/) >. )' % JREV2, TREV, MREV, '( %s ` <. (/) , %s >. )' % (JREV2, RV), '( ( # ` W ) x. 1 )'),
                HR('( %s ` <. W , (/) >. )' % JREV2, TREV, MREV, CL2('(/)', RV), '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )'
             % (ph, HR('( %s ` <. W , (/) >. )' % JREV2, TREV, MREV, CL2('(/)', RV), '( # ` W )')))
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR('( %s ` <. W , (/) >. )' % JREV2, TREV, MREV, CL2('(/)', RV), '( # ` W )'),
                HR(CL2('W', '(/)'), TREV, MREV, CL2('(/)', RV), '( # ` W )')))
    r5 = w.s([q3, r4], 'mpbid', '( %s -> %s )' % (ph, HR(CL2('W', '(/)'), TREV, MREV, CL2('(/)', RV), '( # ` W )')))
    c3, n3 = W.congr(w, CL2('(/)', RV), {}, ph, {}, rules={RV: ('( reverse ` W )', rid)})
    assert n3 == CL2('(/)', '( reverse ` W )'), n3
    o3 = w.s([c3], 'opeq1d', '( %s -> <. %s , ( # ` W ) >. = <. %s , ( # ` W ) >. )'
             % (ph, CL2('(/)', RV), CL2('(/)', '( reverse ` W )')))
    b2 = w.s([o3], 'breq2d', '( %s -> ( %s <-> %s ) )'
             % (ph, HR(CL2('W', '(/)'), TREV, MREV, CL2('(/)', RV), '( # ` W )'),
                HR(CL2('W', '(/)'), TREV, MREV, CL2('(/)', '( reverse ` W )'), '( # ` W )')))
    w.qed([b2, r5], 'mpbid', '( %s -> %s )'
          % (ph, HR(CL2('W', '(/)'), TREV, MREV, CL2('(/)', '( reverse ` W )'), '( # ` W )')))
    return w.run()


def revcfgcl(w, ph, av, t2, texa, Lb, U, WW, ucl, wcl, inr=False):
    """( ph -> <. ( in? ` Lb ) , <. ( inr ` (/) ) , STK2(U,WW) >. >. e. ( TM2Cfg ` TREV ) )"""
    dst = revstk(w, ph, av, U, WW, ucl, wcl)
    z0 = w.s([], '0lt1o', '(/) e. 1o')
    dr = w.s([z0, w.inst('djurcl')], 'ax-mp', '( inr ` (/) ) e. %s' % TA)
    dra = w.s([dr], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (ph, TA))
    drs = w.s([dra, t2], 'eleqtrrd', '( %s -> ( inr ` (/) ) e. %s )' % (ph, SREV))
    pr = w.s([drs, dst], 'opelxpd', '( %s -> <. ( inr ` (/) ) , %s >. e. ( %s X. %s ) )'
             % (ph, STK2(U, WW), SREV, STKREV))
    lab = '( inr ` (/) )' if inr else '( inl ` %s )' % Lb
    ref = 'djurcl' if inr else 'djulcl'
    z1 = w.s([], '0lt1o', '(/) e. 1o')
    dl = w.s([z1, w.inst(ref)], 'ax-mp', '%s e. ( 1o |_| 1o )' % lab)
    dla = w.s([dl], 'a1i', '( %s -> %s e. ( 1o |_| 1o ) )' % (ph, lab))
    tl = w.s([av, w.inst('revtl')], 'syl', '( %s -> %s = 1o )' % (ph, LREV))
    tlc = w.s([tl], 'eqcomd', '( %s -> 1o = %s )' % (ph, LREV))
    dje = w.s([tlc, w.inst('djueq1')], 'syl', '( %s -> ( 1o |_| 1o ) = ( %s |_| 1o ) )' % (ph, LREV))
    dls = w.s([dla, dje], 'eleqtrd', '( %s -> %s e. ( %s |_| 1o ) )' % (ph, lab, LREV))
    cfp = w.s([dls, pr], 'opelxpd', '( %s -> <. %s , <. ( inr ` (/) ) , %s >. >. e. ( ( %s |_| 1o ) X. ( %s X. %s ) ) )'
              % (ph, lab, STK2(U, WW), LREV, SREV, STKREV))
    cv = w.s([texa, w.inst('tm2cfgval')], 'syl', '( %s -> %s = ( ( %s |_| 1o ) X. ( %s X. %s ) ) )'
             % (ph, CFGREV, LREV, SREV, STKREV))
    return w.s([cfp, cv], 'eleqtrrd', '( %s -> <. %s , <. ( inr ` (/) ) , %s >. >. e. %s )'
               % (ph, lab, STK2(U, WW), CFGREV))


def tm2rvhalt():
    lab = 'tm2rvhalt'
    ph = '( ( A e. V /\\ Z e. A ) /\\ U e. Word A )'
    D1 = STK2('(/)', 'U')
    HC = '<. ( inr ` (/) ) , <. ( inr ` (/) ) , %s >. >.' % D1
    w = W(lab, 'The halting step of the reverse machine as a Hoare triple: the '
               'label pops the empty input stack, the branch is false, the state '
               'is reset and the machine halts.  The machine model proves the '
               'same one step as ~ revstep0 .')
    az = w.s([], 'simpl', '( %s -> ( A e. V /\\ Z e. A ) )' % ph)
    av = w.s([az], 'simpld', '( %s -> A e. V )' % ph)
    zv = w.s([az], 'simprd', '( %s -> Z e. A )' % ph)
    uw = w.s([], 'simpr', '( %s -> U e. Word A )' % ph)
    b = revbase(w, ph, av, zv)
    w0 = w.s([], 'wrd0', '(/) e. Word A')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word A )' % ph)
    d1cl = revstk(w, ph, av, '(/)', 'U', w0a, uw)
    hccl = revcfgcl(w, ph, av, b['t2'], b['texa'], '(/)', '(/)', 'U', w0a, uw, inr=True)
    dps = w.s([hccl], 'snssd', '( %s -> { %s } C_ %s )' % (ph, HC, CFGREV))
    def body(av2):
        def L_(st, f):
            return w.s([st], 'adantr', '( %s -> %s )' % (av2, f))
        avv = L_(av, 'A e. V')
        zvv = L_(zv, 'Z e. A')
        uww = L_(uw, 'U e. Word A')
        t2a = L_(b['t2'], '%s = %s' % (SREV, TA))
        d1a = L_(d1cl, '%s e. %s' % (D1, STKREV))
        hca = L_(hccl, '%s e. %s' % (HC, CFGREV))
        gg = w.s([], 'simpr', '( %s -> g e. %s )' % (av2, SREV))
        gta = w.s([gg, t2a], 'eleqtrd', '( %s -> g e. %s )' % (av2, TA))
        azz = w.s([avv, zvv], 'jca', '( %s -> ( A e. V /\\ Z e. A ) )' % av2)
        st0 = w.s([azz, uww, gta, w.inst('revstep0')], 'syl3anc',
                  '( %s -> ( ( %s TM2step %s ) ` <. ( inl ` (/) ) , <. g , %s >. >. ) = ( inl ` %s ) )'
                  % (av2, TREV, MREV, D1, HC))
        texb = w.s([b['texa']], 'adantr', '( %s -> %s e. _V )' % (av2, TREV))
        mex = w.s([], 'snex', '%s e. _V' % MREV)
        mexa = w.s([mex], 'a1i', '( %s -> %s e. _V )' % (av2, MREV))
        tm = w.s([texb, mexa], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (av2, TREV, MREV))
        alb = w.s([b['alcl']], 'adantr', '( %s -> (/) e. %s )' % (av2, LREV))
        pr = w.s([gg, d1a], 'opelxpd', '( %s -> <. g , %s >. e. ( %s X. %s ) )' % (av2, D1, SREV, STKREV))
        aj = w.s([alb, pr], 'jca', '( %s -> ( (/) e. %s /\\ <. g , %s >. e. ( %s X. %s ) ) )'
                 % (av2, LREV, D1, SREV, STKREV))
        sa1 = w.s([tm, aj, w.inst('tm2hsa1')], 'syl2anc',
                  '( %s -> ( ( %s TM2step %s ) ` <. ( inl ` (/) ) , <. g , %s >. >. ) = ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) ) )'
                  % (av2, TREV, MREV, D1, MREV, TREV, D1))
        eq1 = w.s([sa1, st0], 'eqtr3d',
                  '( %s -> ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) ) = ( inl ` %s ) )'
                  % (av2, MREV, TREV, D1, HC))
        ov = w.s([], 'ovex', '( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) e. _V' % (MREV, TREV, D1))
        ova = w.s([ov], 'a1i', '( %s -> ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) e. _V )' % (av2, MREV, TREV, D1))
        hex = w.s([], 'opex', '%s e. _V' % HC)
        hexa = w.s([hex], 'a1i', '( %s -> %s e. _V )' % (av2, HC))
        inj = w.s([ova, hexa, w.inst('inlinj')], 'syl2anc',
                  '( %s -> ( ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) ) = ( inl ` %s ) <-> ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) = %s ) )'
                  % (av2, MREV, TREV, D1, HC, MREV, TREV, D1, HC))
        eq = w.s([inj, eq1], 'mpbid',
                 '( %s -> ( ( %s ` (/) ) ( TM2sa ` %s ) <. g , %s >. ) = %s )' % (av2, MREV, TREV, D1, HC))
        hv = w.s([hexa, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (av2, HC, HC))
        return eq, HC, hv
    hstepP(w, ph, TREV, MREV, '(/)', D1, '{ %s }' % HC, b['phm'], b['alcl'], dps, d1cl, body,
           phmtxt=PHMREV, v='g', a='h', t='k', qed=True)
    return w.run()


def tm2rvmach():
    lab = 'tm2rvmach'
    ph = '( ( A e. V /\\ Z e. A ) /\\ W e. Word A )'
    RW = '( reverse ` W )'
    IC = '<. ( inl ` (/) ) , <. ( inr ` (/) ) , %s >. >.' % STK2('W', '(/)')
    HC = '<. ( inr ` (/) ) , <. ( inr ` (/) ) , %s >. >.' % STK2('(/)', RW)
    N = '( ( # ` W ) + 1 )'
    w = W(lab, 'The reverse machine reverses its input in one step per letter '
               'plus one, derived from the fragment calculus: the '
               '` EvalsToInTime ` form of ~ revmach , whose conversion to '
               '` TM2OutputsInTime ` is the machine-specific bookkeeping of '
               '~ revinitc , ~ revhaltc and ~ tm2outtbr .  The calculus '
               'replaces ~ revcfg , ~ revos , ~ revstepf , ~ revit and '
               '~ revrun by ~ tm2rvst1 , ~ tm2rvloop and ~ tm2rvhalt .')
    az = w.s([], 'simpl', '( %s -> ( A e. V /\\ Z e. A ) )' % ph)
    av = w.s([az], 'simpld', '( %s -> A e. V )' % ph)
    zv = w.s([az], 'simprd', '( %s -> Z e. A )' % ph)
    ww = w.s([], 'simpr', '( %s -> W e. Word A )' % ph)
    b = revbase(w, ph, av, zv)
    w0 = w.s([], 'wrd0', '(/) e. Word A')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word A )' % ph)
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word A )' % (ph, RW))
    loop = w.s([], 'tm2rvloop', '( %s -> %s )' % (ph, HR(CL2('W', '(/)'), TREV, MREV, CL2('(/)', RW), '( # ` W )')))
    hj = w.s([az, rvc], 'jca', '( %s -> ( ( A e. V /\\ Z e. A ) /\\ %s e. Word A ) )' % (ph, RW))
    halt = w.s([hj, w.inst('tm2rvhalt')], 'syl', '( %s -> %s )'
               % (ph, HR(CL2('(/)', RW), TREV, MREV, '{ %s }' % HC, '1')))
    sq = w.s([b['phm'], loop, halt, w.inst('tm2hseq')], 'syl3anc', '( %s -> %s )'
             % (ph, HR(CL2('W', '(/)'), TREV, MREV, '{ %s }' % HC, N)))
    # shrink the precondition to the initial configuration
    ie = w.s([], 'fvex', '( inl ` (/) ) e. _V')
    ie2 = w.s([ie, w.inst('snidg')], 'ax-mp', '( inl ` (/) ) e. { ( inl ` (/) ) }')
    ie2a = w.s([ie2], 'a1i', '( %s -> ( inl ` (/) ) e. { ( inl ` (/) ) } )' % ph)
    z0 = w.s([], '0lt1o', '(/) e. 1o')
    dr = w.s([z0, w.inst('djurcl')], 'ax-mp', '( inr ` (/) ) e. %s' % TA)
    dra = w.s([dr], 'a1i', '( %s -> ( inr ` (/) ) e. %s )' % (ph, TA))
    drs = w.s([dra, b['t2']], 'eleqtrrd', '( %s -> ( inr ` (/) ) e. %s )' % (ph, SREV))
    dst = revstk(w, ph, av, 'W', '(/)', ww, w0a)
    dsv = w.s([dst], 'elexd', '( %s -> %s e. _V )' % (ph, STK2('W', '(/)')))
    dsn = w.s([dsv, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (ph, STK2('W', '(/)'), STK2('W', '(/)')))
    pr = w.s([drs, dsn], 'opelxpd', '( %s -> <. ( inr ` (/) ) , %s >. e. ( %s X. { %s } ) )'
             % (ph, STK2('W', '(/)'), SREV, STK2('W', '(/)')))
    icin = w.s([ie2a, pr], 'opelxpd', '( %s -> %s e. %s )' % (ph, IC, CL2('W', '(/)')))
    icss = w.s([icin], 'snssd', '( %s -> { %s } C_ %s )' % (ph, IC, CL2('W', '(/)')))
    j1 = w.s([b['phm'], sq], 'jca', '( %s -> ( %s /\\ %s ) )'
             % (ph, PHMREV, HR(CL2('W', '(/)'), TREV, MREV, '{ %s }' % HC, N)))
    j2 = w.s([j1, icss], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ { %s } C_ %s ) )'
             % (ph, PHMREV, HR(CL2('W', '(/)'), TREV, MREV, '{ %s }' % HC, N), IC, CL2('W', '(/)')))
    tri = w.s([j2, w.inst('tm2hssc')], 'syl', '( %s -> %s )'
              % (ph, HR('{ %s }' % IC, TREV, MREV, '{ %s }' % HC, N)))
    # the two configurations
    iccl = revcfgcl(w, ph, av, b['t2'], b['texa'], '(/)', 'W', '(/)', ww, w0a)
    hccl = revcfgcl(w, ph, av, b['t2'], b['texa'], '(/)', '(/)', RW, w0a, rvc, inr=True)
    k1 = w.s([iccl, hccl], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, IC, CFGREV, HC, CFGREV))
    k2 = w.s([b['phm'], k1], 'jca', '( %s -> ( %s /\\ ( %s e. %s /\\ %s e. %s ) ) )'
             % (ph, PHMREV, IC, CFGREV, HC, CFGREV))
    k3 = w.s([k2, tri], 'jca', '( %s -> ( ( %s /\\ ( %s e. %s /\\ %s e. %s ) ) /\\ %s ) )'
             % (ph, PHMREV, IC, CFGREV, HC, CFGREV, HR('{ %s }' % IC, TREV, MREV, '{ %s }' % HC, N)))
    w.qed([k3, w.inst('tm2hev')], 'syl',
          '( %s -> %s ( ( %s TM2step %s ) EvalsToInTime %s ) ( inl ` %s ) )' % (ph, IC, TREV, MREV, N, HC))
    return w.run()


def revmachc():
    lab = 'revmachc'
    ph = '( A e. V /\\ Z e. A /\\ W e. Word A )'
    RW = '( reverse ` W )'
    IC = '<. ( inl ` (/) ) , <. ( inr ` (/) ) , %s >. >.' % STK2('W', '(/)')
    HC = '<. ( inr ` (/) ) , <. ( inr ` (/) ) , %s >. >.' % STK2('(/)', RW)
    N = '( ( # ` W ) + 1 )'
    G4 = '( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % MACH
    K0 = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % MACH
    K1 = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % MACH
    STP = '( ( 1st ` ( 1st ` %s ) ) TM2step ( 2nd ` ( 2nd ` %s ) ) )' % (MACH, MACH)
    IFF = ('if ( ( inl ` %s ) = ( inr ` (/) ) , ( inr ` (/) ) , ( inl ` ( %s TM2halt ( 2nd ` ( inl ` %s ) ) ) ) )'
           % (RW, MACH, RW))
    w = W(lab, 'The reverse machine reverses its input within '
               '` ( # ` W ) + 1 ` steps, derived from the fragment calculus.  '
               'The same statement as ~ revmach , whose proof the calculus '
               'replaces from ~ revcfg on.')
    av = w.s([], 'simp1', '( %s -> A e. V )' % ph)
    zv = w.s([], 'simp2', '( %s -> Z e. A )' % ph)
    ww = w.s([], 'simp3', '( %s -> W e. Word A )' % ph)
    aex = w.s([av], 'elexd', '( %s -> A e. _V )' % ph)
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word A )' % (ph, RW))
    az = w.s([av, zv], 'jca', '( %s -> ( A e. V /\\ Z e. A ) )' % ph)
    azw = w.s([az, ww], 'jca', '( %s -> ( ( A e. V /\\ Z e. A ) /\\ W e. Word A ) )' % ph)
    ev = w.s([azw, w.inst('tm2rvmach')], 'syl',
             '( %s -> %s ( ( %s TM2step %s ) EvalsToInTime %s ) ( inl ` %s ) )' % (ph, IC, TREV, MREV, N, HC))
    setmap = {'A': aex}
    # the machine's projections
    e1, r1 = evaluate(w, ph, STP, setmap)
    assert r1 == '( %s TM2step %s )' % (TREV, MREV), r1
    e2, r2 = evaluate(w, ph, '( %s ` %s )' % (G4, K0), setmap)
    n10 = w.s([], '1n0', '1o =/= (/)')
    n01 = w.s([n10], 'necomi', '(/) =/= 1o')
    n01a = w.s([n01], 'a1i', '( %s -> (/) =/= 1o )' % ph)
    z0 = w.s([], '0ex', '(/) e. _V')
    z0a = w.s([z0], 'a1i', '( %s -> (/) e. _V )' % ph)
    o1 = w.s([], '1oex', '1o e. _V')
    o1a = w.s([o1], 'a1i', '( %s -> 1o e. _V )' % ph)
    g0 = w.s([z0a, aex, n01a, w.inst('fvpr1g')], 'syl3anc', '( %s -> ( %s ` (/) ) = A )' % (ph, GREV))
    g1 = w.s([o1a, aex, n01a, w.inst('fvpr2g')], 'syl3anc', '( %s -> ( %s ` 1o ) = A )' % (ph, GREV))
    k0 = w.s([e2, g0], 'eqtrd' if r2 == '( %s ` (/) )' % GREV else 'eqtrd',
             '( %s -> ( %s ` %s ) = A )' % (ph, G4, K0))
    e3, r3 = evaluate(w, ph, '( %s ` %s )' % (G4, K1), setmap)
    k1 = w.s([e3, g1], 'eqtrd', '( %s -> ( %s ` %s ) = A )' % (ph, G4, K1))
    # the antecedent of tm2outtbr
    mex = w.s([], 'opex', '%s e. _V' % MACH)
    mexa = w.s([mex], 'a1i', '( %s -> %s e. _V )' % (ph, MACH))
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    nn = w.s([hn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, N))
    wk0 = w.s([k0], 'eqcomd', '( %s -> A = ( %s ` %s ) )' % (ph, G4, K0))
    wq0 = w.s([wk0, w.inst('wrdeq')], 'syl', '( %s -> Word A = Word ( %s ` %s ) )' % (ph, G4, K0))
    wwk = w.s([ww, wq0], 'eleqtrd', '( %s -> W e. Word ( %s ` %s ) )' % (ph, G4, K0))
    wk1 = w.s([k1], 'eqcomd', '( %s -> A = ( %s ` %s ) )' % (ph, G4, K1))
    wq1 = w.s([wk1, w.inst('wrdeq')], 'syl', '( %s -> Word A = Word ( %s ` %s ) )' % (ph, G4, K1))
    dq1 = w.s([wq1, w.inst('djueq1')], 'syl', '( %s -> ( Word A |_| 1o ) = ( Word ( %s ` %s ) |_| 1o ) )' % (ph, G4, K1))
    dl = w.s([rvc, w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. ( Word A |_| 1o ) )' % (ph, RW))
    dlk = w.s([dl, dq1], 'eleqtrd', '( %s -> ( inl ` %s ) e. ( Word ( %s ` %s ) |_| 1o ) )' % (ph, RW, G4, K1))
    aj = w.s([wwk, dlk], 'jca', '( %s -> ( W e. Word ( %s ` %s ) /\\ ( inl ` %s ) e. ( Word ( %s ` %s ) |_| 1o ) ) )'
             % (ph, G4, K0, RW, G4, K1))
    bi = w.s([mexa, nn, aj, w.inst('tm2outtbr')], 'syl3anc',
             '( %s -> ( W ( %s TM2OutputsInTime %s ) ( inl ` %s ) <-> ( %s TM2init W ) ( %s EvalsToInTime %s ) %s ) )'
             % (ph, MACH, N, RW, MACH, STP, N, IFF))
    # the initial configuration
    aw = w.s([av, ww], 'jca', '( %s -> ( A e. V /\\ W e. Word A ) )' % ph)
    ic = w.s([aw, w.inst('revinitc')], 'syl', '( %s -> ( %s TM2init W ) = %s )' % (ph, MACH, IC))
    icc = w.s([ic], 'eqcomd', '( %s -> %s = ( %s TM2init W ) )' % (ph, IC, MACH))
    # the step relation
    e1c = w.s([e1], 'eqcomd', '( %s -> ( %s TM2step %s ) = %s )' % (ph, TREV, MREV, STP))
    rel = w.s([e1c], 'oveq1d', '( %s -> ( ( %s TM2step %s ) EvalsToInTime %s ) = ( %s EvalsToInTime %s ) )'
              % (ph, TREV, MREV, N, STP, N))
    # the halting configuration
    rvv = w.s([rvc], 'elexd', '( %s -> %s e. _V )' % (ph, RW))
    ne = w.s([rvv, z0a, w.inst('inlneinr')], 'syl2anc', '( %s -> ( inl ` %s ) =/= ( inr ` (/) ) )' % (ph, RW))
    neq = w.s([ne], 'neneqd', '( %s -> -. ( inl ` %s ) = ( inr ` (/) ) )' % (ph, RW))
    iff = w.s([neq], 'iffalsed', '( %s -> %s = ( inl ` ( %s TM2halt ( 2nd ` ( inl ` %s ) ) ) ) )' % (ph, IFF, MACH, RW))
    ilv = w.s([rvv, w.inst('inlval')], 'syl', '( %s -> ( inl ` %s ) = <. (/) , %s >. )' % (ph, RW, RW))
    il2 = w.s([ilv], 'fveq2d', '( %s -> ( 2nd ` ( inl ` %s ) ) = ( 2nd ` <. (/) , %s >. ) )' % (ph, RW, RW))
    il3 = w.s([z0a, rvv, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. (/) , %s >. ) = %s )' % (ph, RW, RW))
    il4 = w.s([il2, il3], 'eqtrd', '( %s -> ( 2nd ` ( inl ` %s ) ) = %s )' % (ph, RW, RW))
    hl1 = w.s([il4], 'oveq2d', '( %s -> ( %s TM2halt ( 2nd ` ( inl ` %s ) ) ) = ( %s TM2halt %s ) )' % (ph, MACH, RW, MACH, RW))
    arv = w.s([av, rvc], 'jca', '( %s -> ( A e. V /\\ %s e. Word A ) )' % (ph, RW))
    hl2 = w.s([arv, w.inst('revhaltc')], 'syl', '( %s -> ( %s TM2halt %s ) = %s )' % (ph, MACH, RW, HC))
    hl3 = w.s([hl1, hl2], 'eqtrd', '( %s -> ( %s TM2halt ( 2nd ` ( inl ` %s ) ) ) = %s )' % (ph, MACH, RW, HC))
    hl4 = w.s([hl3], 'fveq2d', '( %s -> ( inl ` ( %s TM2halt ( 2nd ` ( inl ` %s ) ) ) ) = ( inl ` %s ) )' % (ph, MACH, RW, HC))
    iff2 = w.s([iff, hl4], 'eqtrd', '( %s -> %s = ( inl ` %s ) )' % (ph, IFF, HC))
    iff3 = w.s([iff2], 'eqcomd', '( %s -> ( inl ` %s ) = %s )' % (ph, HC, IFF))
    cv = w.s([icc, rel, iff3], 'breq123d',
             '( %s -> ( %s ( ( %s TM2step %s ) EvalsToInTime %s ) ( inl ` %s ) <-> ( %s TM2init W ) ( %s EvalsToInTime %s ) %s ) )'
             % (ph, IC, TREV, MREV, N, HC, MACH, STP, N, IFF))
    rhs = w.s([cv, ev], 'mpbid',
              '( %s -> ( %s TM2init W ) ( %s EvalsToInTime %s ) %s )' % (ph, MACH, STP, N, IFF))
    w.qed([bi, rhs], 'mpbird', '( %s -> W ( %s TM2OutputsInTime %s ) ( inl ` %s ) )' % (ph, MACH, N, RW))
    return w.run()


if __name__ == '__main__':
    if want('revprog'): revprog()
    if want('revt2'): revt2()
    if want('revtl'): revtl()
    if want('tm2rvst1'): tm2rvst1()
    if want('tm2rvloop'): tm2rvloop()
    if want('tm2rvhalt'): tm2rvhalt()
    if want('tm2rvmach'): tm2rvmach()
    if want('revmachc'): revmachc()
