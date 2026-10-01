"""Sortie A4a, batch 10: the cost of poolGo and poolAlg (step 3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

CSV = '( <" P "> ++ V )'
WN = '( Word NN0 X. NN0 )'
B2 = '( 2o X. NN0 )'
PG = lambda s: '( ( ( X PoolGo Z ) ` K ) ` %s )' % s
G1 = lambda s: '( 1st ` %s )' % PG(s)
G2 = lambda s: '( 2nd ` %s )' % PG(s)
P1 = '( ( P x. K ) + 1 )'
IPP = '( IsPrimeTD ` %s )' % P1
I1 = '( 1st ` %s )' % IPP
I2 = '( 2nd ` %s )' % IPP
COND = '( %s <_ X /\\ Z < %s )' % (P1, P1)
SX = SQ('X')
OUT = '( X e. NN0 /\\ Z e. NN0 /\\ K e. NN0 )'

# ======================================================================= poolGo cost
PHI = '( %s -> %s <_ ( ( # ` s ) x. ( %s + 2 ) ) )' % (OUT, G2('s'), SX)
def _b(w, goal):
    xn = w.s([], 'simp1', '( %s -> X e. NN0 )' % OUT)
    zn = w.s([], 'simp2', '( %s -> Z e. NN0 )' % OUT)
    kn = w.s([], 'simp3', '( %s -> K e. NN0 )' % OUT)
    v = w.s([w.s([xn, zn], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % OUT), kn, w.inst('poolgo0')], 'syl2anc',
            '( %s -> %s = <. (/) , 0 >. )' % (OUT, PG('(/)')))
    zv = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % OUT)
    cv = w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % OUT)
    p2 = projeq(w, OUT, PG('(/)'), v, '(/)', '0', zv, cv, 2)
    hn = w.s([w.s([w.s([], 'wrd0', '(/) e. Word NN0'), w.inst('lencl')], 'ax-mp', '( # ` (/) ) e. NN0')], 'a1i', '( %s -> ( # ` (/) ) e. NN0 )' % OUT)
    sq = w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (OUT, SX))
    s2 = w.s([sq, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % OUT)], 'nn0addcld', '( %s -> ( %s + 2 ) e. NN0 )' % (OUT, SX))
    pr = w.s([hn, s2], 'nn0mulcld', '( %s -> ( ( # ` (/) ) x. ( %s + 2 ) ) e. NN0 )' % (OUT, SX))
    w.qed([p2, w.s([pr], 'nn0ge0d', '( %s -> 0 <_ ( ( # ` (/) ) x. ( %s + 2 ) ) )' % (OUT, SX))], 'eqbrtrd', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ %s )' % (A, OUT)
    THEN = '<. if ( %s = 1o , ( <" %s "> ++ %s ) , %s ) , ( ( %s + %s ) + 1 ) >.' % (I1, P1, G1('V'), G1('V'), G2('V'), I2)
    ELSE = '<. %s , ( %s + 1 ) >.' % (G1('V'), G2('V'))
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    xn = w.s([], 'simpr1', '( %s -> X e. NN0 )' % A2)
    zn = w.s([], 'simpr2', '( %s -> Z e. NN0 )' % A2)
    kn = w.s([], 'simpr3', '( %s -> K e. NN0 )' % A2)
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), w.s([xn, zn, kn], '3jca', '( %s -> %s )' % (A2, OUT))], 'mpd',
              '( %s -> %s <_ ( ( # ` V ) x. ( %s + 2 ) ) )' % (A2, G2('V'), SX))
    p1n = w.s([w.s([pn, kn], 'nn0mulcld', '( %s -> ( P x. K ) e. NN0 )' % A2), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (A2, P1))
    gcl = w.s([w.s([w.s([xn, zn], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % A2), kn], 'jca',
                   '( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % A2), vs], 'jca',
              '( %s -> ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) /\\ V e. Word NN0 ) )' % A2)
    gcl2 = w.s([gcl, w.inst('poolgocl')], 'syl', '( %s -> %s e. %s )' % (A2, PG('V'), WN))
    g1, g2 = paircl(w, A2, PG('V'), gcl2, 'Word NN0', 'NN0')
    icl = w.s([p1n, w.inst('isprimetdcl')], 'syl', '( %s -> %s e. %s )' % (A2, IPP, B2))
    i1c, i2c = paircl(w, A2, IPP, icl, '2o', 'NN0')
    cs = w.s([w.s([w.s([w.s([xn, zn], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % A2), kn], 'jca',
                       '( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % A2), pn], 'jca',
                  '( %s -> ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) /\\ P e. NN0 ) )' % A2), vs], 'jca',
               '( %s -> ( ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) /\\ P e. NN0 ) /\\ V e. Word NN0 ) )' % A2)
    val = w.s([cs, w.inst('poolgocs')], 'syl', '( %s -> %s = if ( %s , %s , %s ) )' % (A2, PG(CSV), COND, THEN, ELSE))
    vt, vf = ifproj(w, A2, PG(CSV), val, COND, THEN, ELSE)
    T = '( %s /\\ %s )' % (A2, COND)
    F_ = '( %s /\\ -. %s )' % (A2, COND)
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    lenn = w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A2)
    sqn = w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A2, SX))
    RHS = '( ( ( # ` V ) + 1 ) x. ( %s + 2 ) )' % SX
    # case: the candidate is in range
    w1 = w.s([w.s([g1], 'adantr', '( %s -> %s e. Word NN0 )' % (T, G1('V'))), w.s([i1c], 'adantr', '( %s -> %s e. 2o )' % (T, I1))], 'jca',
             '( %s -> ( %s e. Word NN0 /\\ %s e. 2o ) )' % (T, G1('V'), I1))
    s1t = w.s([w.s([w.s([p1n], 'adantr', '( %s -> %s e. NN0 )' % (T, P1)), w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (T, P1)),
               w.s([g1], 'adantr', '( %s -> %s e. Word NN0 )' % (T, G1('V'))), w.inst('ccatcl')], 'syl2anc',
              '( %s -> ( <" %s "> ++ %s ) e. Word NN0 )' % (T, P1, G1('V')))
    xat = w.s([s1t, w.s([g1], 'adantr', '( %s -> %s e. Word NN0 )' % (T, G1('V')))], 'ifcld',
              '( %s -> if ( %s = 1o , ( <" %s "> ++ %s ) , %s ) e. Word NN0 )' % (T, I1, P1, G1('V'), G1('V')))
    xbt = w.s([w.s([w.s([g2], 'adantr', '( %s -> %s e. NN0 )' % (T, G2('V'))), w.s([i2c], 'adantr', '( %s -> %s e. NN0 )' % (T, I2))], 'nn0addcld',
                   '( %s -> ( %s + %s ) e. NN0 )' % (T, G2('V'), I2)), w.inst('peano2nn0')], 'syl',
              '( %s -> ( ( %s + %s ) + 1 ) e. NN0 )' % (T, G2('V'), I2))
    p2t = projeq(w, T, PG(CSV), vt, 'if ( %s = 1o , ( <" %s "> ++ %s ) , %s )' % (I1, P1, G1('V'), G1('V')),
                 '( ( %s + %s ) + 1 )' % (G2('V'), I2), xat, xbt, 2)
    ic = w.s([w.s([p1n], 'adantr', '( %s -> %s e. NN0 )' % (T, P1)), w.inst('isprimetdcost')], 'syl', '( %s -> %s <_ ( %s + 1 ) )' % (T, I2, SQ(P1)))
    sqm = w.s([w.s([w.s([w.s([p1n], 'adantr', '( %s -> %s e. NN0 )' % (T, P1)), w.s([xn], 'adantr', '( %s -> X e. NN0 )' % T)], 'jca',
                        '( %s -> ( %s e. NN0 /\\ X e. NN0 ) )' % (T, P1)),
                   w.s([w.s([], 'simpr', '( %s -> %s )' % (T, COND))], 'simpld', '( %s -> %s <_ X )' % (T, P1))], 'jca',
                  '( %s -> ( ( %s e. NN0 /\\ X e. NN0 ) /\\ %s <_ X ) )' % (T, P1, P1)), w.inst('nsqrtmo')], 'syl',
              '( %s -> %s <_ %s )' % (T, SQ(P1), SX))
    lenr = w.s([w.s([lenn], 'adantr', '( %s -> ( # ` V ) e. NN0 )' % T)], 'nn0red', '( %s -> ( # ` V ) e. RR )' % T)
    sxr = w.s([w.s([sqn], 'adantr', '( %s -> %s e. NN0 )' % (T, SX))], 'nn0red', '( %s -> %s e. RR )' % (T, SX))
    spr = w.s([w.s([w.s([p1n], 'adantr', '( %s -> %s e. NN0 )' % (T, P1)), w.inst('nsqrtcl')], 'syl',
                    '( %s -> %s e. NN0 )' % (T, SQ(P1)))], 'nn0red', '( %s -> %s e. RR )' % (T, SQ(P1)))
    g2r = w.s([w.s([g2], 'adantr', '( %s -> %s e. NN0 )' % (T, G2('V')))], 'nn0red', '( %s -> %s e. RR )' % (T, G2('V')))
    i2r = w.s([w.s([i2c], 'adantr', '( %s -> %s e. NN0 )' % (T, I2))], 'nn0red', '( %s -> %s e. RR )' % (T, I2))
    lit = lin.nlinarith(w, T, [ic, sqm, w.s([ihs], 'adantr', '( %s -> %s <_ ( ( # ` V ) x. ( %s + 2 ) ) )' % (T, G2('V'), SX))],
                        '( ( %s + %s ) + 1 ) <_ %s' % (G2('V'), I2, RHS),
                        leaves={'( # ` V )': lenr, SX: sxr, SQ(P1): spr, G2('V'): g2r, I2: i2r})
    rrt, _ = rweq(w, T, '( ( # ` %s ) x. ( %s + 2 ) )' % (CSV, SX), '( # ` %s )' % CSV, '( ( # ` V ) + 1 )',
                  w.s([lc], 'adantr', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (T, CSV)))
    ct = w.s([w.s([p2t, lit], 'eqbrtrd', '( %s -> %s <_ %s )' % (T, G2(CSV), RHS)), rrt], 'breqtrrd',
             '( %s -> %s <_ ( ( # ` %s ) x. ( %s + 2 ) ) )' % (T, G2(CSV), CSV, SX))
    # case: out of range
    xbf = w.s([w.s([g2], 'adantr', '( %s -> %s e. NN0 )' % (F_, G2('V'))), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (F_, G2('V')))
    p2f = projeq(w, F_, PG(CSV), vf, G1('V'), '( %s + 1 )' % G2('V'), w.s([g1], 'adantr', '( %s -> %s e. Word NN0 )' % (F_, G1('V'))), xbf, 2)
    lenrf = w.s([w.s([lenn], 'adantr', '( %s -> ( # ` V ) e. NN0 )' % F_)], 'nn0red', '( %s -> ( # ` V ) e. RR )' % F_)
    sxrf = w.s([w.s([sqn], 'adantr', '( %s -> %s e. NN0 )' % (F_, SX))], 'nn0red', '( %s -> %s e. RR )' % (F_, SX))
    g2rf = w.s([w.s([g2], 'adantr', '( %s -> %s e. NN0 )' % (F_, G2('V')))], 'nn0red', '( %s -> %s e. RR )' % (F_, G2('V')))
    sq0 = w.s([w.s([sqn], 'adantr', '( %s -> %s e. NN0 )' % (F_, SX))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (F_, SX))
    l0 = w.s([w.s([lenn], 'adantr', '( %s -> ( # ` V ) e. NN0 )' % F_)], 'nn0ge0d', '( %s -> 0 <_ ( # ` V ) )' % F_)
    lif = lin.nlinarith(w, F_, [w.s([ihs], 'adantr', '( %s -> %s <_ ( ( # ` V ) x. ( %s + 2 ) ) )' % (F_, G2('V'), SX)), sq0, l0],
                        '( %s + 1 ) <_ %s' % (G2('V'), RHS), leaves={'( # ` V )': lenrf, SX: sxrf, G2('V'): g2rf})
    rrf, _ = rweq(w, F_, '( ( # ` %s ) x. ( %s + 2 ) )' % (CSV, SX), '( # ` %s )' % CSV, '( ( # ` V ) + 1 )',
                  w.s([lc], 'adantr', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (F_, CSV)))
    cf = w.s([w.s([p2f, lif], 'eqbrtrd', '( %s -> %s <_ %s )' % (F_, G2(CSV), RHS)), rrf], 'breqtrrd',
             '( %s -> %s <_ ( ( # ` %s ) x. ( %s + 2 ) ) )' % (F_, G2(CSV), CSV, SX))
    w.qed([w.s([ct, cf], 'pm2.61dan', '( %s -> %s <_ ( ( # ` %s ) x. ( %s + 2 ) ) )' % (A2, G2(CSV), CSV, SX))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( ( %s /\\ S e. Word NN0 ) )' % OUT
    T = '( %s /\\ S e. Word NN0 )' % OUT
    w.qed([w.s([w.s([], 'simpr', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([], 'simpl', '( %s -> %s )' % (T, OUT))], 'mpd', '( %s -> %s <_ ( ( # ` S ) x. ( %s + 2 ) ) )' % (T, G2('S'), SX))
family(run, 'poolgocost', PHI, _b, _s, finish=_f, desc='The cost of the pool loop (Lean: poolGo_cost).', only=only)

# ======================================================================= poolAlg cost
if not only or 'poolalgcost' in only:
    w = W('poolalgcost', 'The cost of the step-3 pool (Lean: poolAlg_cost).')
    T = '( ( W e. Word NN0 /\\ X e. NN0 ) /\\ ( Z e. NN0 /\\ K e. NN0 ) )'
    DS = '( 1st ` ( DivisorsOf ` W ) )'
    PA = '( ( ( W PoolAlg X ) ` Z ) ` K )'
    PGD = '( ( ( X PoolGo Z ) ` K ) ` %s )' % DS
    ws = w.s([], 'simpll', '( %s -> W e. Word NN0 )' % T)
    xn = w.s([], 'simplr', '( %s -> X e. NN0 )' % T)
    zn = w.s([], 'simprl', '( %s -> Z e. NN0 )' % T)
    kn = w.s([], 'simprr', '( %s -> K e. NN0 )' % T)
    v = w.s([w.s([w.s([w.s([ws, xn], 'jca', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % T), zn], 'jca',
                      '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % T), kn], 'jca',
                 '( %s -> ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % T), w.inst('poolalgval')], 'syl',
            '( %s -> %s = <. ( 1st ` %s ) , ( ( 2nd ` ( DivisorsOf ` W ) ) + ( 2nd ` %s ) ) >. )' % (T, PA, PGD, PGD))
    dcl = w.s([ws, w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` W ) e. %s )' % (T, WN))
    d1, d2 = paircl(w, T, '( DivisorsOf ` W )', dcl, 'Word NN0', 'NN0')
    gcl = w.s([w.s([w.s([w.s([xn, zn], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % T), kn], 'jca',
                        '( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % T), d1], 'jca',
                   '( %s -> ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) /\\ %s e. Word NN0 ) )' % (T, DS)), w.inst('poolgocl')], 'syl',
              '( %s -> %s e. %s )' % (T, PGD, WN))
    g1, g2 = paircl(w, T, PGD, gcl, 'Word NN0', 'NN0')
    sm = w.s([d2, g2], 'nn0addcld', '( %s -> ( ( 2nd ` ( DivisorsOf ` W ) ) + ( 2nd ` %s ) ) e. NN0 )' % (T, PGD))
    p2 = projeq(w, T, PA, v, '( 1st ` %s )' % PGD, '( ( 2nd ` ( DivisorsOf ` W ) ) + ( 2nd ` %s ) )' % PGD, g1, sm, 2)
    dc = w.s([ws, w.inst('divisorsofcost')], 'syl', '( %s -> ( 2nd ` ( DivisorsOf ` W ) ) <_ ( 2 ^ ( # ` W ) ) )' % T)
    gc = w.s([w.s([w.s([xn, zn, kn], '3jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 /\\ K e. NN0 ) )' % T), d1], 'jca',
                  '( %s -> ( ( X e. NN0 /\\ Z e. NN0 /\\ K e. NN0 ) /\\ %s e. Word NN0 ) )' % (T, DS)), w.inst('poolgocost')], 'syl',
             '( %s -> ( 2nd ` %s ) <_ ( ( # ` %s ) x. ( %s + 2 ) ) )' % (T, PGD, DS, SX))
    dl = w.s([ws, w.inst('divisorsoflen')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` W ) ) )' % (T, DS))
    gc2, _ = rweq(w, T, '( ( # ` %s ) x. ( %s + 2 ) )' % (DS, SX), '( # ` %s )' % DS, '( 2 ^ ( # ` W ) )', dl)
    gcb = w.s([gc, gc2], 'breqtrd', '( %s -> ( 2nd ` %s ) <_ ( ( 2 ^ ( # ` W ) ) x. ( %s + 2 ) ) )' % (T, PGD, SX))
    lenn = w.s([ws, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % T)
    pwn = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % T), lenn], 'nn0expcld', '( %s -> ( 2 ^ ( # ` W ) ) e. NN0 )' % T)
    pwr = w.s([pwn], 'nn0red', '( %s -> ( 2 ^ ( # ` W ) ) e. RR )' % T)
    sqn = w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (T, SX))
    sxr = w.s([sqn], 'nn0red', '( %s -> %s e. RR )' % (T, SX))
    d2r = w.s([d2], 'nn0red', '( %s -> ( 2nd ` ( DivisorsOf ` W ) ) e. RR )' % T)
    g2r = w.s([g2], 'nn0red', '( %s -> ( 2nd ` %s ) e. RR )' % (T, PGD))
    li = lin.nlinarith(w, T, [dc, gcb], '( ( 2nd ` ( DivisorsOf ` W ) ) + ( 2nd ` %s ) ) <_ ( ( 2 ^ ( # ` W ) ) x. ( %s + 3 ) )' % (PGD, SX),
                       leaves={'( 2 ^ ( # ` W ) )': pwr, SX: sxr, '( 2nd ` ( DivisorsOf ` W ) )': d2r, '( 2nd ` %s )' % PGD: g2r})
    w.qed([p2, li], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( ( 2 ^ ( # ` W ) ) x. ( %s + 3 ) ) )' % (T, PA, SX))
    run(w)
