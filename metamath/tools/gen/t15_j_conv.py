"""T15 (j): from the Hoare triple of a run to TM2OutputsInTime at the concrete machine."""
import os, sys, json, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *
from t15_h_inst import TY, LB, RT, PG, AL, WS, FR, S0, MACH, MAIN, sets
import num
import lin
lin.FASTPATH = True
from lin import linarith

X0 = '( encNatGam ` N )'


def D0(dom='dom ( 1st ` ( 1st ` %s ) )' % TY, X=X0):
    return '( k e. %s |-> if ( k = 0 , %s , (/) ) )' % (dom, X)


def DO(dom='dom ( 1st ` ( 1st ` %s ) )' % TY, O='O'):
    return '( k e. %s |-> if ( k = 1 , %s , (/) ) )' % (dom, O)


def XC(lab='( ( %s ` 0 ) ` 0 )' % FR, dom=None):
    return '<. ( inl ` %s ) , <. %s , %s >. >.' % (lab, S0, D0() if dom is None else D0(dom))


def YC(dom=None, O='O'):
    return '<. ( inr ` (/) ) , <. %s , %s >. >.' % (S0, DO(O=O) if dom is None else DO(dom, O))


PROJ = [('( 1st ` ( 1st ` %s ) )' % MACH, TY), ('( 2nd ` ( 2nd ` %s ) )' % MACH, PG),
        ('( 1st ` ( 1st ` ( 2nd ` %s ) ) )' % MACH, MAIN), ('( 2nd ` ( 1st ` ( 2nd ` %s ) ) )' % MACH, S0),
        ('( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % MACH, 'TMGam'), ('( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % MACH, '0'),
        ('( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % MACH, '1')]


def t15mproj():
    w = W('t15mproj', 'The components of the concrete machine tuple.')
    g1, l1, st, gl = sets(w)
    body = 'if ( ( %s TMWalk ( x ` -u 1 ) ) e. ( TM2Stmt ` %s ) , ( %s TMWalk ( x ` -u 1 ) ) , <. 6 , (/) >. )' % (RT, TY, RT)
    pdf = w.s([], 'df-tmprog', '%s = ( x e. %s |-> %s )' % (PG, LB, body))
    pv = w.s([pdf, w.s([l1], 'mptex', '( x e. %s |-> %s ) e. _V' % (LB, body))], 'eqeltri', '%s e. _V' % PG)
    tv = w.s([w.s([], 'df-tmty', '%s = <. <. TMGam , %s >. , TMSt >.' % (TY, LB)), w.s([], 'opex', '<. <. TMGam , %s >. , TMSt >. e. _V' % LB)], 'eqeltri', '%s e. _V' % TY)
    A1 = '<. %s , <. 0 , 1 >. >.' % TY
    A2 = '<. <. %s , %s >. , %s >.' % (MAIN, S0, PG)
    mdf = w.s([], 'df-tmmach', '%s = <. %s , %s >.' % (MACH, A1, A2))
    a1x = w.s([], 'opex', '%s e. _V' % A1)
    a2x = w.s([], 'opex', '%s e. _V' % A2)
    c0 = w.s([], 'c0ex', '0 e. _V'); c1 = w.s([], '1ex', '1 e. _V')
    mx = w.s([], 'fvex', '%s e. _V' % MAIN)
    sx = w.s([], 'opex', '%s e. _V' % S0)
    ox = w.s([], 'opex', '<. 0 , 1 >. e. _V')
    msx = w.s([], 'opex', '<. %s , %s >. e. _V' % (MAIN, S0))
    f1 = w.s([mdf], 'fveq2i', '( 1st ` %s ) = ( 1st ` <. %s , %s >. )' % (MACH, A1, A2))
    f2 = w.s([a1x, a2x, w.inst('op1stg')], 'mp2an', '( 1st ` <. %s , %s >. ) = %s' % (A1, A2, A1))
    m1 = w.s([f1, f2], 'eqtri', '( 1st ` %s ) = %s' % (MACH, A1))
    g1_ = w.s([mdf], 'fveq2i', '( 2nd ` %s ) = ( 2nd ` <. %s , %s >. )' % (MACH, A1, A2))
    g2 = w.s([a1x, a2x, w.inst('op2ndg')], 'mp2an', '( 2nd ` <. %s , %s >. ) = %s' % (A1, A2, A2))
    m2 = w.s([g1_, g2], 'eqtri', '( 2nd ` %s ) = %s' % (MACH, A2))

    def proj(outer, inner_eq, inner_txt, lhs, a, b, ax, bx, which):
        e1 = w.s([inner_eq], 'fveq2i', '( %s ` %s ) = ( %s ` <. %s , %s >. )' % (which, lhs, which, a, b))
        e2 = w.s([ax, bx, w.inst('op1stg' if which == '1st' else 'op2ndg')], 'mp2an', '( %s ` <. %s , %s >. ) = %s' % (which, a, b, a if which == '1st' else b))
        return w.s([e1, e2], 'eqtri', '( %s ` %s ) = %s' % (which, lhs, a if which == '1st' else b))
    p1 = proj(None, m1, A1, '( 1st ` %s )' % MACH, TY, '<. 0 , 1 >.', tv, ox, '1st')
    p2 = proj(None, m2, A2, '( 2nd ` %s )' % MACH, '<. %s , %s >.' % (MAIN, S0), PG, msx, pv, '2nd')
    q1 = proj(None, m2, A2, '( 2nd ` %s )' % MACH, '<. %s , %s >.' % (MAIN, S0), PG, msx, pv, '1st')
    p3 = proj(None, q1, None, '( 1st ` ( 2nd ` %s ) )' % MACH, MAIN, S0, mx, sx, '1st')
    p4 = proj(None, q1, None, '( 1st ` ( 2nd ` %s ) )' % MACH, MAIN, S0, mx, sx, '2nd')
    q2 = proj(None, m1, A1, '( 1st ` %s )' % MACH, TY, '<. 0 , 1 >.', tv, ox, '2nd')
    p6 = proj(None, q2, None, '( 2nd ` ( 1st ` %s ) )' % MACH, '0', '1', c0, c1, '1st')
    p7 = proj(None, q2, None, '( 2nd ` ( 1st ` %s ) )' % MACH, '0', '1', c0, c1, '2nd')
    ty = w.s([], 't15typ', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    tg = w.s([ty], 'simp1i', '( 1st ` ( 1st ` %s ) ) = TMGam' % TY)
    p5a = w.s([p1], 'fveq2i', '( 1st ` ( 1st ` ( 1st ` %s ) ) ) = ( 1st ` %s )' % (MACH, TY))
    p5b = w.s([p5a], 'fveq2i', '( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) = ( 1st ` ( 1st ` %s ) )' % (MACH, TY))
    p5 = w.s([p5b, tg], 'eqtri', '( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) = TMGam' % MACH)
    j1 = w.s([p1, p2], 'pm3.2i', '( %s = %s /\\ %s = %s )' % (PROJ[0] + PROJ[1]))
    j2 = w.s([p3, p4], 'pm3.2i', '( %s = %s /\\ %s = %s )' % (PROJ[2] + PROJ[3]))
    j3 = w.s([p5, p6, p7], '3pm3.2i', '( %s = %s /\\ %s = %s /\\ %s = %s )' % (PROJ[4] + PROJ[5] + PROJ[6]))
    w.qed([j1, j2, j3], '3pm3.2i', '( ( %s = %s /\\ %s = %s ) /\\ ( %s = %s /\\ %s = %s ) /\\ ( %s = %s /\\ %s = %s /\\ %s = %s ) )' % tuple(x for p in PROJ for x in p))
    return w


GENS = {'t15mproj': t15mproj}



def t15conv():
    w = W('t15conv', 'A run of the concrete program from the initial configuration of input N to the halted configuration with output O is TM2OutputsInTime.')
    CK = '( C e. NN0 /\\ K e. NN )'
    TRI = '{ %s } ( %s TM2Hoare %s ) <. { %s } , R >.' % (XC(), TY, PG, YC())
    ph = '( %s /\\ ( ( N e. NN0 /\\ Q e. NN0 /\\ O e. Word Gamma\' ) /\\ ( R <_ Q /\\ %s ) ) )' % (CK, TRI)
    S = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ph, f))
    ck = S([], 'simpl', CK)
    b = S([], 'simpr', '( ( N e. NN0 /\\ Q e. NN0 /\\ O e. Word Gamma\' ) /\\ ( R <_ Q /\\ %s ) )' % TRI)
    b1 = S([b], 'simpld', '( N e. NN0 /\\ Q e. NN0 /\\ O e. Word Gamma\' )')
    nn = S([b1], 'simp1d', 'N e. NN0'); qn = S([b1], 'simp2d', 'Q e. NN0'); ow = S([b1], 'simp3d', "O e. Word Gamma'")
    b2 = S([b], 'simprd', '( R <_ Q /\\ %s )' % TRI)
    rq = S([b2], 'simpld', 'R <_ Q'); tri = S([b2], 'simprd', TRI)
    L = '( 2nd ` ( 1st ` %s ) )' % TY
    ST = '( TM2Stmt ` %s )' % TY
    pg = S([ck, w.inst('t15prog')], 'syl', '%s : %s --> %s' % (PG, L, ST))
    tv = S([w.s([w.s([], 'df-tmty', '%s = <. <. TMGam , %s >. , TMSt >.' % (TY, LB)), w.s([], 'opex', '<. <. TMGam , %s >. , TMSt >. e. _V' % LB)], 'eqeltri', '%s e. _V' % TY)], 'a1i', '%s e. _V' % TY)
    j1 = S([tv, pg], 'jca', '( %s e. _V /\\ %s : %s --> %s )' % (TY, PG, L, ST))
    TRIQ = TRI.replace(', R >.', ', Q >.')
    t2 = S([S([j1, tri], 'jca', '( ( %s e. _V /\\ %s : %s --> %s ) /\\ %s )' % (TY, PG, L, ST, TRI)), S([qn, rq], 'jca', '( Q e. NN0 /\\ R <_ Q )'), w.inst('tm2hle')], 'syl2anc', TRIQ)
    lx = S([], 'fvexd', '%s e. _V' % L)
    pv = S([pg, lx, w.inst('fex')], 'syl2anc', '%s e. _V' % PG)
    ty = S([S([S([tv, pv], 'jca', '( %s e. _V /\\ %s e. _V )' % (TY, PG)), t2], 'jca', '( ( %s e. _V /\\ %s e. _V ) /\\ %s )' % (TY, PG, TRIQ)), w.inst('tm2hrtyp')], 'syl',
           '( { %s } C_ ( TM2Cfg ` %s ) /\\ { %s } C_ ( TM2Cfg ` %s ) /\\ Q e. NN0 )' % (XC(), TY, YC(), TY))
    CF = '( TM2Cfg ` %s )' % TY
    xs = S([ty], 'simp1d', '{ %s } C_ %s' % (XC(), CF)); ys = S([ty], 'simp2d', '{ %s } C_ %s' % (YC(), CF))
    xc = S([S([w.s([], 'opex', '%s e. _V' % XC())], 'a1i', '%s e. _V' % XC()), w.inst('snssg')], 'syl', '( %s e. %s <-> { %s } C_ %s )' % (XC(), CF, XC(), CF))
    xm = S([xs, xc], 'mpbird', '%s e. %s' % (XC(), CF))
    yc = S([S([w.s([], 'opex', '%s e. _V' % YC())], 'a1i', '%s e. _V' % YC()), w.inst('snssg')], 'syl', '( %s e. %s <-> { %s } C_ %s )' % (YC(), CF, YC(), CF))
    ym = S([ys, yc], 'mpbird', '%s e. %s' % (YC(), CF))
    ev = S([S([j1, S([xm, ym], 'jca', '( %s e. %s /\\ %s e. %s )' % (XC(), CF, YC(), CF))], 'jca', '( ( %s e. _V /\\ %s : %s --> %s ) /\\ ( %s e. %s /\\ %s e. %s ) )' % (TY, PG, L, ST, XC(), CF, YC(), CF)), t2, w.inst('tm2hev')], 'syl2anc',
           '%s ( ( %s TM2step %s ) EvalsToInTime Q ) ( inl ` %s )' % (XC(), TY, PG, YC()))
    C2 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (CK, f))
    # projections
    pj = w.s([], 't15mproj', '( ( %s = %s /\\ %s = %s ) /\\ ( %s = %s /\\ %s = %s ) /\\ ( %s = %s /\\ %s = %s /\\ %s = %s ) )' % tuple(x for p in PROJ for x in p))
    pa = w.s([pj], 'simp1i', '( %s = %s /\\ %s = %s )' % (PROJ[0] + PROJ[1]))
    pb = w.s([pj], 'simp2i', '( %s = %s /\\ %s = %s )' % (PROJ[2] + PROJ[3]))
    pcx = w.s([pj], 'simp3i', '( %s = %s /\\ %s = %s /\\ %s = %s )' % (PROJ[4] + PROJ[5] + PROJ[6]))
    peq = [w.s([pa], 'simpli', '%s = %s' % PROJ[0]), w.s([pa], 'simpri', '%s = %s' % PROJ[1]),
           w.s([pb], 'simpli', '%s = %s' % PROJ[2]), w.s([pb], 'simpri', '%s = %s' % PROJ[3]),
           w.s([pcx], 'simp1i', '%s = %s' % PROJ[4]), w.s([pcx], 'simp2i', '%s = %s' % PROJ[5]), w.s([pcx], 'simp3i', '%s = %s' % PROJ[6])]
    rules = {}
    for (a, b_), st in zip(PROJ, peq):
        rules[a] = (b_, C2([st], 'a1i', '%s = %s' % (a, b_)))
    tys = w.s([], 't15typ', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    tg = C2([w.s([tys], 'simp1i', '( 1st ` ( 1st ` %s ) ) = TMGam' % TY)], 'a1i', '( 1st ` ( 1st ` %s ) ) = TMGam' % TY)
    # ( ( FR ` 0 ) ` 0 ) = MAIN
    fb = open(os.path.join(ROOT, 'scratch', 't15defs.txt')).read() if False else None
    FRB = '( i e. NN0 |-> if ( i = 2 , ( TMpnF ( (/) ++ <" 2 "> ) ; 1 6 ( TMLab ` ( ( (/) ++ <" 3 "> ) ++ <" 0 "> ) ) ) , if ( i = 8 , ( TMFsrch ( (/) ++ <" 8 "> ) C K ) , ( TMLab ` ( (/) ++ <" i "> ) ) ) ) )'
    fdf = C2([w.s([], 'df-tmfroot', '%s = %s' % (FR, FRB))], 'a1i', '%s = %s' % (FR, FRB))
    pi = '( %s /\\ i = 0 )' % CK
    ie = w.s([], 'simpr', '( %s -> i = 0 )' % pi)
    chain = FRB[len('( i e. NN0 |-> '):-2]
    r1 = chain[len('if ( i = 2 , ( TMpnF ( (/) ++ <" 2 "> ) ; 1 6 ( TMLab ` ( ( (/) ++ <" 3 "> ) ++ <" 0 "> ) ) ) , '):-2]
    r2 = '( TMLab ` ( (/) ++ <" i "> ) )'
    n2 = w.s([w.s([], 'ax-mp', '') if False else w.s([w.s([], '2ne0', '2 =/= 0')], 'necomi', '0 =/= 2')], 'neii', '-. 0 = 2')
    n8 = w.s([w.s([w.s([], '8re', '8 e. RR'), w.s([], '8pos', '0 < 8')], 'gt0ne0ii', '8 =/= 0')], 'necomi', '0 =/= 8')
    n8 = w.s([n8], 'neii', '-. 0 = 8')
    c2 = w.s([w.s([n2], 'a1i', '( %s -> -. 0 = 2 )' % pi), w.s([ie, w.inst('eqeq1')], 'syl', '( %s -> ( i = 2 <-> 0 = 2 ) )' % pi)], 'mtbird', '( %s -> -. i = 2 )' % pi)
    c8 = w.s([w.s([n8], 'a1i', '( %s -> -. 0 = 8 )' % pi), w.s([ie, w.inst('eqeq1')], 'syl', '( %s -> ( i = 8 <-> 0 = 8 ) )' % pi)], 'mtbird', '( %s -> -. i = 8 )' % pi)
    s1 = w.s([c2], 'iffalsed', '( %s -> %s = %s )' % (pi, chain, r1))
    s2 = w.s([c8], 'iffalsed', '( %s -> %s = %s )' % (pi, r1, r2))
    s3 = w.s([w.s([w.s([w.s([ie], 's1eqd', '( %s -> <" i "> = <" 0 "> )' % pi)], 'oveq2d', '( %s -> ( (/) ++ <" i "> ) = ( (/) ++ <" 0 "> ) )' % pi)], 'fveq2d',
                  '( %s -> ( TMLab ` ( (/) ++ <" i "> ) ) = ( TMLab ` ( (/) ++ <" 0 "> ) ) )' % pi)], 'id', '') if False else None
    s3 = w.s([w.s([w.s([ie], 's1eqd', '( %s -> <" i "> = <" 0 "> )' % pi)], 'oveq2d', '( %s -> ( (/) ++ <" i "> ) = ( (/) ++ <" 0 "> ) )' % pi)], 'fveq2d',
             '( %s -> ( TMLab ` ( (/) ++ <" i "> ) ) = ( TMLab ` ( (/) ++ <" 0 "> ) ) )' % pi)
    h2 = w.s([w.s([s1, s2], 'eqtrd', '( %s -> %s = %s )' % (pi, chain, r2)), s3], 'eqtrd', '( %s -> %s = ( TMLab ` ( (/) ++ <" 0 "> ) ) )' % (pi, chain))
    z0 = C2([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0')
    fe = C2([], 'fvexd', '( TMLab ` ( (/) ++ <" 0 "> ) ) e. _V')
    f0 = C2([fdf, h2, z0, fe], 'fvmptd', '( %s ` 0 ) = ( TMLab ` ( (/) ++ <" 0 "> ) )' % FR)
    f00 = C2([f0], 'fveq1d', '( ( %s ` 0 ) ` 0 ) = ( ( TMLab ` ( (/) ++ <" 0 "> ) ) ` 0 )' % FR)
    w0 = C2([w.s([w.s([], 'wrd0', '(/) e. Word NN0'), w.s([], '0nn0', '0 e. NN0'), w.inst('ccatws1cl')], 'mp2an', '( (/) ++ <" 0 "> ) e. Word NN0')], 'a1i', '( (/) ++ <" 0 "> ) e. Word NN0')
    l1 = w.s([w.s([w.s([], 'wrd0', '(/) e. Word NN0'), w.inst('ccatws1len')], 'ax-mp', '( # ` ( (/) ++ <" 0 "> ) ) = ( ( # ` (/) ) + 1 )'),
              w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'oveq1i', '( ( # ` (/) ) + 1 ) = ( 0 + 1 )'), w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'eqtri', '( ( # ` (/) ) + 1 ) = 1')], 'eqtri', '( # ` ( (/) ++ <" 0 "> ) ) = 1')
    l2 = w.s([l1, num.le_nat(w, 1, 30, strict=True)], 'eqbrtri', '( # ` ( (/) ++ <" 0 "> ) ) < ; 3 0')
    ap = C2([w0, C2([l2], 'a1i', '( # ` ( (/) ++ <" 0 "> ) ) < ; 3 0'), z0, w.inst('tmlabap')], 'syl3anc', '( ( TMLab ` ( (/) ++ <" 0 "> ) ) ` 0 ) = %s' % MAIN)
    fm = C2([f00, ap], 'eqtrd', '( ( %s ` 0 ) ` 0 ) = %s' % (FR, MAIN))
    # canonical forms
    X0m = '( k e. dom TMGam |-> if ( k = 0 , %s , (/) ) )' % X0
    W0 = '<. ( inl ` %s ) , <. %s , %s >. >.' % (MAIN, S0, X0m)
    ex1, v1 = cong_m(w, XC(), CK, {'( ( %s ` 0 ) ` 0 )' % FR: (MAIN, fm), '( 1st ` ( 1st ` %s ) )' % TY: ('TMGam', tg)})
    assert v1 == W0, v1
    mv = S([ck, w.inst('t15mfin')], 'syl', '%s e. FinTM2' % MACH)
    mvv = S([mv], 'elexd', '%s e. _V' % MACH)
    x0v = S([], 'fvexd', '%s e. _V' % X0)
    INITV = '<. ( inl ` ( 1st ` ( 1st ` ( 2nd ` %s ) ) ) ) , <. ( 2nd ` ( 1st ` ( 2nd ` %s ) ) ) , ( k e. dom ( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) |-> if ( k = ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) , %s , (/) ) ) >. >.' % (MACH, MACH, MACH, MACH, X0)
    iv = S([mvv, x0v, w.inst('tm2initval')], 'syl2anc', '( %s TM2init %s ) = %s' % (MACH, X0, INITV))
    ei0, vi = cong_m(w, INITV, CK, rules)
    ei = S([ei0], 'adantr', '%s = %s' % (INITV, vi))
    assert vi == W0, vi
    ex1 = S([ex1], 'adantr', '%s = %s' % (XC(), v1))
    E1 = S([iv, ei, ex1], '3eqtr4d', '( %s TM2init %s ) = %s' % (MACH, X0, XC()))
    STEPF = '( ( 1st ` ( 1st ` %s ) ) TM2step ( 2nd ` ( 2nd ` %s ) ) )' % (MACH, MACH)
    E20, v2 = cong_m(w, STEPF, CK, rules)
    E2 = S([E20], 'adantr', '%s = %s' % (STEPF, v2))
    assert v2 == '( %s TM2step %s )' % (TY, PG), v2
    IFY = 'if ( ( inl ` O ) = ( inr ` (/) ) , ( inr ` (/) ) , ( inl ` ( %s TM2halt ( 2nd ` ( inl ` O ) ) ) ) )' % MACH
    ovv = S([ow], 'elexd', 'O e. _V')
    ne = S([ovv, S([w.s([], '0ex', '(/) e. _V')], 'a1i', '(/) e. _V'), w.inst('inlneinr')], 'syl2anc', '( inl ` O ) =/= ( inr ` (/) )')
    i1 = S([S([ne], 'neneqd', '-. ( inl ` O ) = ( inr ` (/) )')], 'iffalsed', '%s = ( inl ` ( %s TM2halt ( 2nd ` ( inl ` O ) ) ) )' % (IFY, MACH))
    il = S([ovv, w.inst('inlval')], 'syl', '( inl ` O ) = <. (/) , O >.')
    i2 = S([S([il], 'fveq2d', '( 2nd ` ( inl ` O ) ) = ( 2nd ` <. (/) , O >. )'), S([S([w.s([], '0ex', '(/) e. _V')], 'a1i', '(/) e. _V'), ovv, w.inst('op2ndg')], 'syl2anc', '( 2nd ` <. (/) , O >. ) = O')], 'eqtrd', '( 2nd ` ( inl ` O ) ) = O')
    HV = '<. ( inr ` (/) ) , <. ( 2nd ` ( 1st ` ( 2nd ` %s ) ) ) , ( k e. dom ( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) |-> if ( k = ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) , O , (/) ) ) >. >.' % (MACH, MACH, MACH)
    hv = S([mvv, ovv, w.inst('tm2haltval')], 'syl2anc', '( %s TM2halt O ) = %s' % (MACH, HV))
    i3 = S([i2], 'oveq2d', '( %s TM2halt ( 2nd ` ( inl ` O ) ) ) = ( %s TM2halt O )' % (MACH, MACH))
    eh0, vh = cong_m(w, HV, CK, rules)
    eh = S([eh0], 'adantr', '%s = %s' % (HV, vh))
    ey0, vy = cong_m(w, YC(), CK, {'( 1st ` ( 1st ` %s ) )' % TY: ('TMGam', tg)})
    assert vh == vy, (vh, vy)
    ey = S([ey0], 'adantr', '%s = %s' % (YC(), vy))
    i4 = S([i3, hv, eh], '3eqtrd', '( %s TM2halt ( 2nd ` ( inl ` O ) ) ) = %s' % (MACH, vh))
    i5 = S([i4, ey], 'eqtr4d', '( %s TM2halt ( 2nd ` ( inl ` O ) ) ) = %s' % (MACH, YC()))
    E3 = S([i1, S([i5], 'fveq2d', '( inl ` ( %s TM2halt ( 2nd ` ( inl ` O ) ) ) ) = ( inl ` %s )' % (MACH, YC()))], 'eqtrd', '%s = ( inl ` %s )' % (IFY, YC()))
    E2b = S([E2], 'oveq1d', '( %s EvalsToInTime Q ) = ( ( %s TM2step %s ) EvalsToInTime Q )' % (STEPF, TY, PG))
    bq = S([E1, E2b, E3], 'breq123d', '( ( %s TM2init %s ) ( %s EvalsToInTime Q ) %s <-> %s ( ( %s TM2step %s ) EvalsToInTime Q ) ( inl ` %s ) )' % (MACH, X0, STEPF, IFY, XC(), TY, PG, YC()))
    rhs = S([ev, bq], 'mpbird', '( %s TM2init %s ) ( %s EvalsToInTime Q ) %s' % (MACH, X0, STEPF, IFY))
    # typing for tm2outtbr
    G0 = '( ( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) ` ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) )' % (MACH, MACH)
    G1_ = '( ( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) ` ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) )' % (MACH, MACH)
    g00, gv0 = cong_m(w, G0, CK, rules)
    g0 = S([g00], 'adantr', '%s = %s' % (G0, gv0))
    g10, gv1 = cong_m(w, G1_, CK, rules)
    g1_ = S([g10], 'adantr', '%s = %s' % (G1_, gv1))

    def gam(k):
        n = int(k)
        a = num.nn0(w, n); bb = w.s([], '8nn', '8 e. NN'); c = num.le_nat(w, n, 8, strict=True)
        e = w.s([], 'elfzo0', '( %s e. ( 0 ..^ 8 ) <-> ( %s e. NN0 /\\ 8 e. NN /\\ %s < 8 ) )' % (k, k, k))
        f = w.s([a, bb, c, e], 'mpbir3an', '%s e. ( 0 ..^ 8 )' % k)
        return S([w.s([f, w.inst('tmgamfv')], 'ax-mp', "( TMGam ` %s ) = Gamma'" % k)], 'a1i', "( TMGam ` %s ) = Gamma'" % k)
    gg0 = S([g0, gam('0')], 'eqtrd', "%s = Gamma'" % G0)
    gg1 = S([g1_, gam('1')], 'eqtrd', "%s = Gamma'" % G1_)
    xg = S([nn, w.inst('encnatgamcl')], 'syl', "%s e. Word Gamma'" % X0)
    xw = S([xg, S([gg0, w.inst('wrdeq')], 'syl', "Word %s = Word Gamma'" % G0)], 'eleqtrrd', 'Word %s' % G0) if False else None
    xw = S([xg, S([gg0, w.inst('wrdeq')], 'syl', "Word %s = Word Gamma'" % G0)], 'eleqtrrd', '%s e. Word %s' % (X0, G0))
    oy = S([ow, w.inst('djulcl')], 'syl', "( inl ` O ) e. ( Word Gamma' |_| 1o )")
    dq = S([S([gg1, w.inst('wrdeq')], 'syl', "Word %s = Word Gamma'" % G1_), w.inst('djueq1')], 'syl', "( Word %s |_| 1o ) = ( Word Gamma' |_| 1o )" % G1_)
    yw = S([oy, dq], 'eleqtrrd', '( inl ` O ) e. ( Word %s |_| 1o )' % G1_)
    ob = S([mvv, qn, S([xw, yw], 'jca', '( %s e. Word %s /\\ ( inl ` O ) e. ( Word %s |_| 1o ) )' % (X0, G0, G1_)), w.inst('tm2outtbr')], 'syl3anc',
           '( %s ( %s TM2OutputsInTime Q ) ( inl ` O ) <-> ( %s TM2init %s ) ( %s EvalsToInTime Q ) %s )' % (X0, MACH, MACH, X0, STEPF, IFY))
    w.qed([rhs, ob], 'mpbird', '( %s -> %s ( %s TM2OutputsInTime Q ) ( inl ` O ) )' % (ph, X0, MACH))
    return w


GENS['t15conv'] = t15conv



import t15_g_pre as GP
SCN = '( ( C ScTM K ) ` N )'
GETD = 'if ( ( 1st ` ( %s Search N ) ) = ( inr ` (/) ) , <. 0 , (/) >. , ( 2nd ` ( 1st ` ( %s Search N ) ) ) )' % (SCN, SCN)
ENC = '( ( 1st ` %s ) encodeOutput ( 2nd ` %s ) )' % (GETD, GETD)
BPRE = '( ( 7 x. ( # ` ( encodeNat ` N ) ) ) + ; 7 0 )'
EL = '( TMLab ` (/) )'
CTXC = '( ( %s e. _V /\\ %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) ) /\\ ( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` %s ) = TMSt ) )' % (TY, PG, TY, TY, TY, TY)
SUBM = {'T': TY, 'M': PG, 'P': FR, 'E': EL, 'V': '_V'}


class SubW:
    def __init__(self, w, m):
        self.w, self.m = w, m
        self.lines = w.lines
        self.memo = {}

    def s(self, h, r, f, name=None):
        return self.w.s(h, r, subst_text(f, self.m), name)

    def inst(self, r, name=None):
        return self.w.inst(r, name)

    def wcongr(self, *a, **k):
        return self.w.wcongr(*a, **k)


def run_common(w, ph, ck, nn):
    X = GP.Pre(SubW(w, {'T': TY, 'M': PG, 'V': '_V'}), ph)
    S = X.s
    tys = w.s([], 't15typ', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    tv = S([w.s([w.s([], 'df-tmty', '%s = <. <. TMGam , %s >. , TMSt >.' % (TY, LB)), w.s([], 'opex', '<. <. TMGam , %s >. , TMSt >. e. _V' % LB)], 'eqeltri', '%s e. _V' % TY)], 'a1i', '%s e. _V' % TY)
    pg = S([ck, w.inst('t15prog')], 'syl', '%s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s )' % (PG, TY, TY))
    tg = S([w.s([tys], 'simp1i', '( 1st ` ( 1st ` %s ) ) = TMGam' % TY)], 'a1i', '( 1st ` ( 1st ` %s ) ) = TMGam' % TY)
    ts = S([w.s([tys], 'simp3i', '( 2nd ` %s ) = TMSt' % TY)], 'a1i', '( 2nd ` %s ) = TMSt' % TY)
    cx = S([S([tv, pg], 'jca', '( %s e. _V /\\ %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) )' % (TY, PG, TY, TY)), S([tg, ts], 'jca', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY))], 'jca', CTXC)
    X.ctx(cx)
    inst = S([ck, w.inst('t15inst')], 'syl', 'TMIroot C K %s %s %s %s' % (TY, PG, FR, EL))
    return X, cx, inst, tys


def finish(w, X, ph, t, f, nn, Dout, dos, Otext, name):
    """shrink the pre class to the initial configuration, the post to the halted one; qed"""
    S = X.s
    C, Pp, N = GP.parse_tri(f)
    D0 = XC().split(' , <. ' + S0 + ' , ', 1)[1][:-6]
    xcf = XC()
    lab = '( ( %s ` 0 ) ` 0 )' % FR
    i1 = S([S([], 'fvexd', '( inl ` %s ) e. _V' % lab), w.inst('snidg')], 'syl', '( inl ` %s ) e. { ( inl ` %s ) }' % (lab, lab))
    tys = w.s([], 't15typ', '( ( 1st ` ( 1st ` %s ) ) = TMGam /\\ ( 2nd ` ( 1st ` %s ) ) = %s /\\ ( 2nd ` %s ) = TMSt )' % (TY, TY, LB, TY))
    import t15_e_kind
    k = t15_e_kind.Kind.__new__(t15_e_kind.Kind); k.w = w; k.memo = {}
    s0t = k.closed_st(S0)
    s0s = S([X.d(s0t, '%s e. TMSt' % S0), X.ts], 'eleqtrrd', '%s e. ( 2nd ` %s )' % (S0, TY))
    d0v = S([S([], 'mptexd' if False else 'fvexd', '') if False else None] if False else [], 'fvexd', '') if False else None
    dmx = w.s([], 'fvex', '( 1st ` ( 1st ` %s ) ) e. _V' % TY)
    dd = w.s([dmx], 'dmex', 'dom ( 1st ` ( 1st ` %s ) ) e. _V' % TY)
    d0x = X.d(w.s([dd], 'mptex', '%s e. _V' % D0), '%s e. _V' % D0)
    i2 = S([d0x, w.inst('snidg')], 'syl', '%s e. { %s }' % (D0, D0))
    i3 = S([s0s, i2, w.inst('opelxpi')], 'syl2anc', '<. %s , %s >. e. ( ( 2nd ` %s ) X. { %s } )' % (S0, D0, TY, D0))
    i4 = S([i1, i3, w.inst('opelxpi')], 'syl2anc', '%s e. %s' % (xcf, C))
    ss = S([i4], 'snssd', '{ %s } C_ %s' % (xcf, C))
    t2 = S([S([X.tvm, t], 'jca', '( ( %s e. _V /\\ %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) ) /\\ %s )' % (TY, PG, TY, TY, f)), ss, w.inst('tm2hssc')], 'syl2anc', GP.TRI('{ %s }' % xcf, Pp, N).replace('( T TM2Hoare M )', '( %s TM2Hoare %s )' % (TY, PG)))
    f2 = GP.TRI('{ %s }' % xcf, Pp, N).replace('( T TM2Hoare M )', '( %s TM2Hoare %s )' % (TY, PG))
    YCt = '<. ( inr ` (/) ) , <. %s , %s >. >.' % (S0, Dout)
    e1 = w.s([], 'xpsn', '( { %s } X. { %s } ) = { <. %s , %s >. }' % (S0, Dout, S0, Dout))
    e2 = w.s([e1], 'xpeq2i', '( { ( inr ` (/) ) } X. ( { %s } X. { %s } ) ) = ( { ( inr ` (/) ) } X. { <. %s , %s >. } )' % (S0, Dout, S0, Dout))
    e3 = w.s([], 'xpsn', '( { ( inr ` (/) ) } X. { <. %s , %s >. } ) = { %s }' % (S0, Dout, YCt))
    e4 = w.s([e2, e3], 'eqtri', '%s = { %s }' % (Pp, YCt))
    tq, fq = GP.transport(X, t2, f2.replace('( %s TM2Hoare %s )' % (TY, PG), '( T TM2Hoare M )') if False else f2, S([e4], 'a1i', '%s = { %s }' % (Pp, YCt)), '{ %s }' % YCt) if False else (None, None)
    # transport by hand (the machine is concrete)
    peq = S([e4], 'a1i', '%s = { %s }' % (Pp, YCt))
    sd = S([peq], 'eqimssd', '%s C_ { %s }' % (Pp, YCt))
    pv = S([S([X.tvm], 'simprd', '%s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s )' % (PG, TY, TY)), S([], 'fvexd', '( 2nd ` ( 1st ` %s ) ) e. _V' % TY), w.inst('fex')], 'syl2anc', '%s e. _V' % PG)
    ty = S([S([S([X.tv, pv], 'jca', '( %s e. _V /\\ %s e. _V )' % (TY, PG)), t2], 'jca', '( ( %s e. _V /\\ %s e. _V ) /\\ %s )' % (TY, PG, f2)), w.inst('tm2hrtyp')], 'syl',
           '( { %s } C_ ( TM2Cfg ` %s ) /\\ %s C_ ( TM2Cfg ` %s ) /\\ %s e. NN0 )' % (xcf, TY, Pp, TY, N))
    y2 = S([peq, S([ty], 'simp2d', '%s C_ ( TM2Cfg ` %s )' % (Pp, TY))], 'eqsstrrd', '{ %s } C_ ( TM2Cfg ` %s )' % (YCt, TY))
    f3 = '{ %s } ( %s TM2Hoare %s ) <. { %s } , %s >.' % (xcf, TY, PG, YCt, N)
    w.qed([S([X.tvm, t2], 'jca', '( ( %s e. _V /\\ %s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s ) ) /\\ %s )' % (TY, PG, TY, TY, f2)),
           S([sd, y2], 'jca', '( %s C_ { %s } /\\ { %s } C_ ( TM2Cfg ` %s ) )' % (Pp, YCt, YCt, TY)), w.inst('tm2hssd')], 'syl2anc', '( %s -> %s )' % (ph, f3))


def t15runb():
    w = W('t15runb', 'The run of the concrete machine on an input n >= 16: prefix, search, halt.')
    ph = '( ( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN ) /\\ N e. ( ZZ>= ` ; 1 6 ) )'
    c0 = w.s([], 'simpll', '( %s -> ( C e. NN0 /\\ 1 <_ C ) )' % ph)
    cn = w.s([c0], 'simpld', '( %s -> C e. NN0 )' % ph)
    kn = w.s([], 'simplr', '( %s -> K e. NN )' % ph)
    nu = w.s([], 'simpr', '( %s -> N e. ( ZZ>= ` ; 1 6 ) )' % ph)
    ck = w.s([cn, kn], 'jca', '( %s -> ( C e. NN0 /\\ K e. NN ) )' % ph)
    nn = w.s([w.s([num.nn0(w, 16)], 'a1i', '( %s -> ; 1 6 e. NN0 )' % ph), nu, w.inst('eluznn0')], 'syl2anc', '( %s -> N e. NN0 )' % ph)
    le = w.s([nu, w.inst('eluzle')], 'syl', '( %s -> ; 1 6 <_ N )' % ph)
    X, cx, inst, tys = run_common(w, ph, ck, nn)
    L = {CTXC: cx, 'TMIroot C K %s %s %s %s' % (TY, PG, FR, EL): inst, 'N e. NN0': nn, '; 1 6 <_ N': le}
    ta, fa = use(w, ph, 't15preb', SUBM, L)
    pc = GP.unfold(w, ph, 'TMIroot', {'T': TY, 'M': PG, 'P': FR, 'E': EL}, inst)
    sc = w.s([c0, kn, nu, w.inst('sctm16')], 'syl3anc', '( %s -> ( %s e. Scales /\\ 1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) )' % (ph, SCN, SCN))
    L['TMIsrch C K %s %s ( %s ` 8 ) ( %s ` 9 )' % (TY, PG, FR, FR)] = pc['TMIsrch C K %s %s ( %s ` 8 ) ( %s ` 9 )' % (TY, PG, FR, FR)]
    L['( C e. NN0 /\\ K e. NN /\\ N e. NN0 )'] = w.s([cn, kn, nn], '3jca', '( %s -> ( C e. NN0 /\\ K e. NN /\\ N e. NN0 ) )' % ph)
    L['1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) )' % SCN] = w.s([sc], 'simprd', '( %s -> 1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % (ph, SCN))
    tb, fb = use(w, ph, 'tmisrch', {'T': TY, 'M': PG, 'P': '( %s ` 8 )' % FR, 'E': '( %s ` 9 )' % FR, 'V': '_V'}, L)
    Dout = '( k e. dom ( 1st ` ( 1st ` %s ) ) |-> if ( k = 1 , %s , (/) ) )' % (TY, ENC)
    gd = w.s([w.s([sc], 'simpld', '( %s -> %s e. Scales )' % (ph, SCN)), nn, w.inst('srchgetd')], 'syl2anc', '( %s -> %s e. ( NN0 X. Word NN0 ) )' % (ph, GETD))
    g1 = w.s([gd, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` %s ) e. NN0 )' % (ph, GETD))
    g2 = w.s([gd, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. Word NN0 )' % (ph, GETD))
    eg = w.s([g1, g2, w.inst('encoutcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, ENC))
    dos = X.initstk('1', ENC, eg)
    L['%s e. ( TM2Stk ` %s )' % (Dout, TY)] = dos
    tc, fc = use(w, ph, 't15halt', {'T': TY, 'M': PG, 'P': FR, 'E': EL, 'V': '_V', 'D': Dout}, L)
    tab, fab = GP.seq(X, ta, fa.replace('( %s TM2Hoare %s )' % (TY, PG), '( T TM2Hoare M )'), tb, fb.replace('( %s TM2Hoare %s )' % (TY, PG), '( T TM2Hoare M )')) if False else (None, None)
    tab, fab = seqc(X, ta, fa, tb, fb)
    tall, fall = seqc(X, tab, fab, tc, fc)
    finish(w, X, ph, tall, fall, nn, Dout, dos, ENC, 't15runb')
    return w


def seqc(X, ta, fa, tb, fb):
    rep = '( %s TM2Hoare %s )' % (TY, PG)
    Ca, Da, Na = GP.parse_tri(fa.replace(rep, '( T TM2Hoare M )'))
    Cb, Db, Nb = GP.parse_tri(fb.replace(rep, '( T TM2Hoare M )'))
    assert Da == Cb, (Da, Cb)
    f = '%s %s <. %s , ( %s + %s ) >.' % (Ca, rep, Db, Na, Nb)
    return X.s([X.tvm, ta, tb, X.w.inst('tm2hseq')], 'syl3anc', f), f


def t15runs():
    w = W('t15runs', 'The run of the concrete machine on an input n < 16: prefix, failAll, halt.')
    ph = '( ( C e. NN0 /\\ K e. NN ) /\\ ( N e. NN0 /\\ N < ; 1 6 ) )'
    ck = w.s([], 'simpl', '( %s -> ( C e. NN0 /\\ K e. NN ) )' % ph)
    nn = w.s([], 'simprl', '( %s -> N e. NN0 )' % ph)
    lt = w.s([], 'simprr', '( %s -> N < ; 1 6 )' % ph)
    X, cx, inst, tys = run_common(w, ph, ck, nn)
    L = {CTXC: cx, 'TMIroot C K %s %s %s %s' % (TY, PG, FR, EL): inst, 'N e. NN0': nn, 'N < ; 1 6': lt}
    ta, fa = use(w, ph, 't15pres', SUBM, L)
    Dout = '( k e. dom ( 1st ` ( 1st ` %s ) ) |-> if ( k = 1 , <" 4 "> , (/) ) )' % TY
    g4 = X.d(X.c("<\" 4 \"> e. Word Gamma'", 'ax-mp', [X.c("4 e. Gamma'", 'gamma4'), w.inst('s1cl')]), "<\" 4 \"> e. Word Gamma'")
    dos = X.initstk('1', '<" 4 ">', g4)
    L['%s e. ( TM2Stk ` %s )' % (Dout, TY)] = dos
    tc, fc = use(w, ph, 't15halt', {'T': TY, 'M': PG, 'P': FR, 'E': EL, 'V': '_V', 'D': Dout}, L)
    tall, fall = seqc(X, ta, fa, tc, fc)
    finish(w, X, ph, tall, fall, nn, Dout, dos, '<" 4 ">', 't15runs')
    return w


GENS['t15runb'] = t15runb
GENS['t15runs'] = t15runs



def t15sbcl():
    w = W('t15sbcl', 'The step bound of the search (Lean: searchBound) is a natural number (from the typing of its triple).')
    ph = '( ( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN ) /\\ N e. ( ZZ>= ` ; 1 6 ) )'
    c0 = w.s([], 'simpll', '( %s -> ( C e. NN0 /\\ 1 <_ C ) )' % ph)
    cn = w.s([c0], 'simpld', '( %s -> C e. NN0 )' % ph)
    kn = w.s([], 'simplr', '( %s -> K e. NN )' % ph)
    nu = w.s([], 'simpr', '( %s -> N e. ( ZZ>= ` ; 1 6 ) )' % ph)
    ck = w.s([cn, kn], 'jca', '( %s -> ( C e. NN0 /\\ K e. NN ) )' % ph)
    nn = w.s([w.s([num.nn0(w, 16)], 'a1i', '( %s -> ; 1 6 e. NN0 )' % ph), nu, w.inst('eluznn0')], 'syl2anc', '( %s -> N e. NN0 )' % ph)
    X, cx, inst, tys = run_common(w, ph, ck, nn)
    pc = GP.unfold(w, ph, 'TMIroot', {'T': TY, 'M': PG, 'P': FR, 'E': EL}, inst)
    sc = w.s([c0, kn, nu, w.inst('sctm16')], 'syl3anc', '( %s -> ( %s e. Scales /\\ 1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) ) ) )' % (ph, SCN, SCN))
    L = {CTXC: cx, 'TMIsrch C K %s %s ( %s ` 8 ) ( %s ` 9 )' % (TY, PG, FR, FR): pc['TMIsrch C K %s %s ( %s ` 8 ) ( %s ` 9 )' % (TY, PG, FR, FR)],
         '( C e. NN0 /\\ K e. NN /\\ N e. NN0 )': w.s([cn, kn, nn], '3jca', '( %s -> ( C e. NN0 /\\ K e. NN /\\ N e. NN0 ) )' % ph),
         '1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) )' % SCN: w.s([sc], 'simprd', '( %s -> 1 <_ ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % (ph, SCN))}
    tb, fb = use(w, ph, 'tmisrch', {'T': TY, 'M': PG, 'P': '( %s ` 8 )' % FR, 'E': '( %s ` 9 )' % FR, 'V': '_V'}, L)
    C_, P_, N_ = GP.parse_tri(fb.replace('( %s TM2Hoare %s )' % (TY, PG), '( T TM2Hoare M )'))
    pv = X.s([X.s([X.tvm], 'simprd', '%s : ( 2nd ` ( 1st ` %s ) ) --> ( TM2Stmt ` %s )' % (PG, TY, TY)), X.s([], 'fvexd', '( 2nd ` ( 1st ` %s ) ) e. _V' % TY), w.inst('fex')], 'syl2anc', '%s e. _V' % PG)
    ty = X.s([X.s([X.s([X.tv, pv], 'jca', '( %s e. _V /\\ %s e. _V )' % (TY, PG)), tb], 'jca', '( ( %s e. _V /\\ %s e. _V ) /\\ %s )' % (TY, PG, fb)), w.inst('tm2hrtyp')], 'syl',
             '( %s C_ ( TM2Cfg ` %s ) /\\ %s C_ ( TM2Cfg ` %s ) /\\ %s e. NN0 )' % (C_, TY, P_, TY, N_))
    w.qed([ty], 'simp3d', '( %s -> %s e. NN0 )' % (ph, N_))
    return w


GENS['t15sbcl'] = t15sbcl

if __name__ == '__main__':
    for lab in sys.argv[1:]:
        GENS[lab]().run()
