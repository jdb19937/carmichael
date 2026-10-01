"""T11: the divisor arithmetic of ` divisorsOfF ` (PrimList.lean ` divisorsOf_mem_le ` , ` sum_geom_bound ` ).

  divisorsofle   every subset product of a list of numbers below ` 2 ^ b ` is at most ` 2 ^ ( # Q b ) `
  tmdvgeo        ` sum_ ( j < n ) ( ( 2 ^ j + 1 ) C + 2 ) + 2 <_ 2 ^ n ( 2 C + 2 ) ` (Lean ` sum_geom_bound ` )

    MM_DB=sorties/t11.mm python3 tools/gen/t11_c_darith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t5lib import Ctx

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


CSV = '( <" P "> ++ V )'
WN = '( Word NN0 X. NN0 )'
DOF = lambda s: '( DivisorsOf ` %s )' % s
D1 = lambda s: '( 1st ` %s )' % DOF(s)
EX = lambda s: '( 2 ^ ( ( # ` %s ) x. B ) )' % s
HB = lambda s: '( B e. NN0 /\\ A. p e. ran %s p < ( 2 ^ B ) )' % s
BODY = lambda s: 'A. x e. ran %s x <_ %s' % (D1(s), EX(s))
PHI_DL = '( %s -> %s )' % (HB('s'), BODY('s'))
STMTS = {}
STMTS['divisorsofle'] = '( ( S e. Word NN0 /\\ %s ) -> %s )' % (HB('S'), BODY('S'))


def _b_dl(w, goal):
    A = HB('(/)')
    bn = w.s([], 'simpl', '( %s -> B e. NN0 )' % A)
    r1 = w.s([w.s([w.s([], 'divisorsof0', '%s = <. <" 1 "> , 0 >.' % DOF('(/)'))], 'fveq2i', '%s = ( 1st ` <. <" 1 "> , 0 >. )' % D1('(/)')),
              w.s([w.s([w.s([], 's1cli', '<" 1 "> e. Word _V')], 'elexi', '<" 1 "> e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op1st',
                  '( 1st ` <. <" 1 "> , 0 >. ) = <" 1 ">')], 'eqtri', '%s = <" 1 ">' % D1('(/)'))
    r2 = w.s([w.s([r1], 'rneqi', 'ran %s = ran <" 1 ">' % D1('(/)')), w.s([w.s([], '1ex', '1 e. _V'), w.inst('s1rn')], 'ax-mp', 'ran <" 1 "> = { 1 }')],
             'eqtri', 'ran %s = { 1 }' % D1('(/)'))
    e0 = w.s([w.s([w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'oveq1i', '( ( # ` (/) ) x. B ) = ( 0 x. B )')], 'a1i',
                  '( %s -> ( ( # ` (/) ) x. B ) = ( 0 x. B ) )' % A),
              w.s([w.s([bn], 'nn0cnd', '( %s -> B e. CC )' % A)], 'mul02d', '( %s -> ( 0 x. B ) = 0 )' % A)], 'eqtrd',
             '( %s -> ( ( # ` (/) ) x. B ) = 0 )' % A)
    e1 = w.s([w.s([e0], 'oveq2d', '( %s -> %s = ( 2 ^ 0 ) )' % (A, EX('(/)'))),
              w.s([w.s([w.s([], '2cn', '2 e. CC'), w.inst('exp0')], 'ax-mp', '( 2 ^ 0 ) = 1')], 'a1i', '( %s -> ( 2 ^ 0 ) = 1 )' % A)], 'eqtrd',
             '( %s -> %s = 1 )' % (A, EX('(/)')))
    le = w.s([w.s([w.s([], '1re', '1 e. RR')], 'leidi', '1 <_ 1') if False else w.s([w.s([], '1le1', '1 <_ 1')], 'a1i', '( %s -> 1 <_ 1 )' % A), e1],
             'breqtrrd', '( %s -> 1 <_ %s )' % (A, EX('(/)')))
    rs = w.s([w.s([], 'breq1', '( x = 1 -> ( x <_ %s <-> 1 <_ %s ) )' % (EX('(/)'), EX('(/)')))], 'ralsng',
             '( 1 e. _V -> ( A. x e. { 1 } x <_ %s <-> 1 <_ %s ) )' % (EX('(/)'), EX('(/)')))
    rs2 = w.s([w.s([], '1ex', '1 e. _V'), rs], 'ax-mp', '( A. x e. { 1 } x <_ %s <-> 1 <_ %s )' % (EX('(/)'), EX('(/)')))
    rq = w.s([r2], 'raleqi', '( %s <-> A. x e. { 1 } x <_ %s )' % (BODY('(/)'), EX('(/)')))
    w.qed([w.s([le, w.s([rq, rs2], 'bitri', '( %s <-> 1 <_ %s )' % (BODY('(/)'), EX('(/)')))], 'sylibr', '( %s -> %s )' % (A, BODY('(/)')))],
          'id' if False else 'mpbir' if False else 'syl', goal) if False else \
        w.qed([le, w.s([rq, rs2], 'bitri', '( %s <-> 1 <_ %s )' % (BODY('(/)'), EX('(/)')))], 'sylibr', goal)


def _s_dl(w, A, ih, co):
    A2 = '( %s /\\ %s )' % (A, HB(CSV))
    s = w.s
    vs = s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    hb = s([], 'simpr', '( %s -> %s )' % (A2, HB(CSV)))
    bn = s([hb], 'simpld', '( %s -> B e. NN0 )' % A2)
    ralc = s([hb], 'simprd', '( %s -> A. p e. ran %s p < ( 2 ^ B ) )' % (A2, CSV))
    sp = s([pn, w.inst('s1cl')], 'syl', '( %s -> <" P "> e. Word NN0 )' % A2)
    rc0 = s([sp, vs, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran <" P "> u. ran V ) )' % (A2, CSV))
    pv = s([pn], 'elexd', '( %s -> P e. _V )' % A2)
    s1r = s([pv, w.inst('s1rn')], 'syl', '( %s -> ran <" P "> = { P } )' % A2)
    rc = s([rc0, s([s1r], 'uneq1d', '( %s -> ( ran <" P "> u. ran V ) = ( { P } u. ran V ) )' % A2)], 'eqtrd',
           '( %s -> ran %s = ( { P } u. ran V ) )' % (A2, CSV))
    sb = s([], 'breq1', '( p = P -> ( p < ( 2 ^ B ) <-> P < ( 2 ^ B ) ) )')
    eqv, _ = ralcons(w, A2, 'p', 'p < ( 2 ^ B )', 'P < ( 2 ^ B )', 'V', rc, pv, sb)
    both = s([eqv, ralc], 'mpbid', '( %s -> ( P < ( 2 ^ B ) /\\ A. p e. ran V p < ( 2 ^ B ) ) )' % A2)
    plt = s([both], 'simpld', '( %s -> P < ( 2 ^ B ) )' % A2)
    ralv = s([both], 'simprd', '( %s -> A. p e. ran V p < ( 2 ^ B ) )' % A2)
    ihs = s([s([], 'simpl3', '( %s -> %s )' % (A2, ih)), s([bn, ralv], 'jca', '( %s -> %s )' % (A2, HB('V')))], 'mpd', '( %s -> %s )' % (A2, BODY('V')))
    DV = D1('V')
    MV = '( P MulAll %s )' % DV
    MV1 = '( 1st ` %s )' % MV
    cs = s([pn, vs, w.inst('divisorsofcs')], 'syl2anc', '( %s -> %s = <. ( %s ++ %s ) , ( ( 2nd ` %s ) + ( 2nd ` %s ) ) >. )'
           % (A2, DOF(CSV), DV, MV1, DOF('V'), MV))
    cl = s([vs, w.inst('divisorsofcl')], 'syl', '( %s -> %s e. %s )' % (A2, DOF('V'), WN))
    a1, b1 = paircl(w, A2, DOF('V'), cl, 'Word NN0', 'NN0')
    clm = s([pn, a1, w.inst('mulallcl')], 'syl2anc', '( %s -> %s e. %s )' % (A2, MV, WN))
    a2, b2 = paircl(w, A2, MV, clm, 'Word NN0', 'NN0')
    xa = s([a1, a2, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. Word NN0 )' % (A2, DV, MV1))
    xb = s([b1, b2], 'nn0addcld', '( %s -> ( ( 2nd ` %s ) + ( 2nd ` %s ) ) e. NN0 )' % (A2, DOF('V'), MV))
    p1 = projeq(w, A2, DOF(CSV), cs, '( %s ++ %s )' % (DV, MV1), '( ( 2nd ` %s ) + ( 2nd ` %s ) )' % (DOF('V'), MV), xa, xb, 1)
    rr = s([s([p1], 'rneqd', '( %s -> ran %s = ran ( %s ++ %s ) )' % (A2, D1(CSV), DV, MV1)), s([a1, a2, w.inst('ccatrn')], 'syl2anc',
                                                                                               '( %s -> ran ( %s ++ %s ) = ( ran %s u. ran %s ) )' % (A2, DV, MV1, DV, MV1))],
           'eqtrd', '( %s -> ran %s = ( ran %s u. ran %s ) )' % (A2, D1(CSV), DV, MV1))
    # exponents
    nv = s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A2)
    lc = s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    cl_ = Closure(w, A2, {'B': ('NN0', bn)})
    cl_.leaf('( # ` V )', 'NN0', nv)
    ea = s([s([lc], 'oveq1d', '( %s -> ( ( # ` %s ) x. B ) = ( ( ( # ` V ) + 1 ) x. B ) )' % (A2, CSV)),
            lineq(w, A2, '( ( ( # ` V ) + 1 ) x. B )', '( ( ( # ` V ) x. B ) + B )', closure=cl_, products=True)], 'eqtrd',
           '( %s -> ( ( # ` %s ) x. B ) = ( ( ( # ` V ) x. B ) + B ) )' % (A2, CSV))
    EC = EX(CSV)
    EV = EX('V')
    P2 = '( 2 ^ B )'
    ec = s([s([ea], 'oveq2d', '( %s -> %s = ( 2 ^ ( ( ( # ` V ) x. B ) + B ) ) )' % (A2, EC)),
            s([closed_2cn(w, A2), cl_.mem('( ( # ` V ) x. B )', 'NN0'), bn], 'expaddd', '( %s -> ( 2 ^ ( ( ( # ` V ) x. B ) + B ) ) = ( %s x. %s ) )' % (A2, EV, P2))],
           'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A2, EC, EV, P2))
    evn = s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A2), cl_.mem('( ( # ` V ) x. B )', 'NN0')], 'nn0expcld', '( %s -> %s e. NN0 )' % (A2, EV))
    p2n = s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A2), bn], 'nn0expcld', '( %s -> %s e. NN0 )' % (A2, P2))
    ecn = s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A2), cl_.mem('( ( # ` %s ) x. B )' % CSV, 'NN0') if False else
             s([s([lc, s([nv, w.inst('peano2nn0')], 'syl', '( %s -> ( ( # ` V ) + 1 ) e. NN0 )' % A2)], 'eqeltrd', '( %s -> ( # ` %s ) e. NN0 )' % (A2, CSV)), bn],
               'nn0mulcld', '( %s -> ( ( # ` %s ) x. B ) e. NN0 )' % (A2, CSV))], 'nn0expcld', '( %s -> %s e. NN0 )' % (A2, EC))
    # EV <_ EC
    one = s([s([p2n], 'nn0red', '( %s -> %s e. RR )' % (A2, P2)), s([closed_2re(w, A2), bn, s([s([], '1le2', '1 <_ 2')], 'a1i', '( %s -> 1 <_ 2 )' % A2)], 'expge1d',
                                                                                          '( %s -> 1 <_ %s )' % (A2, P2))], 'id', '') if False else None
    p1le = s([closed_2re(w, A2), bn, s([s([], '1le2', '1 <_ 2')], 'a1i', '( %s -> 1 <_ 2 )' % A2)], 'expge1d', '( %s -> 1 <_ %s )' % (A2, P2))
    evr = s([evn], 'nn0red', '( %s -> %s e. RR )' % (A2, EV))
    p2r = s([p2n], 'nn0red', '( %s -> %s e. RR )' % (A2, P2))
    evle = s([evr, p2r, s([evn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (A2, EV)), p1le], 'lemulge11d', '( %s -> %s <_ ( %s x. %s ) )' % (A2, EV, EV, P2))
    evle2 = s([evle, ec], 'breqtrrd', '( %s -> %s <_ %s )' % (A2, EV, EC))
    # the element y
    RU = '( ran %s u. ran %s )' % (DV, MV1)
    pa = '( %s /\\ y e. ran %s )' % (A2, D1(CSV))
    L = lambda st: s([st], 'adantr', '( %s -> %s )' % (pa, concl_of(w, A2, st)))
    yin = s([s([], 'simpr', '( %s -> y e. ran %s )' % (pa, D1(CSV))), L(rr)], 'eleqtrd', '( %s -> y e. %s )' % (pa, RU))
    yor = s([yin, w.inst('elun')], 'sylib', '( %s -> ( y e. ran %s \\/ y e. ran %s ) )' % (pa, DV, MV1))
    # case 1
    c1 = '( %s /\\ y e. ran %s )' % (pa, DV)
    L1 = lambda st: s([st], 'adantr', '( %s -> %s )' % (c1, concl_of(w, pa, st)))
    rv1 = s([s([], 'breq1', '( x = y -> ( x <_ %s <-> y <_ %s ) )' % (EV, EV))], 'rspcv', '( y e. ran %s -> ( %s -> y <_ %s ) )' % (DV, BODY('V'), EV))
    y1 = s([s([], 'simpr', '( %s -> y e. ran %s )' % (c1, DV)), L1(L(ihs)), rv1], 'sylc', '( %s -> y <_ %s )' % (c1, EV))
    yr1 = s([s([s([s([L1(L(a1)), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (c1, DV, DV)), w.inst('frn')], 'syl',
                  '( %s -> ran %s C_ NN0 )' % (c1, DV)), s([], 'simpr', '( %s -> y e. ran %s )' % (c1, DV))], 'sseldd', '( %s -> y e. NN0 )' % c1)],
            'nn0red', '( %s -> y e. RR )' % c1)
    k1 = s([yr1, L1(L(evr)), s([L1(L(ecn))], 'nn0red', '( %s -> %s e. RR )' % (c1, EC)), y1, L1(L(evle2))], 'letrd', '( %s -> y <_ %s )' % (c1, EC))
    # case 2
    c2 = '( %s /\\ y e. ran %s )' % (pa, MV1)
    L2 = lambda st: s([st], 'adantr', '( %s -> %s )' % (c2, concl_of(w, pa, st)))
    y2in = s([], 'simpr', '( %s -> y e. ran %s )' % (c2, MV1))
    yn2 = s([s([s([s([L2(L(a2)), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (c2, MV1, MV1)), w.inst('frn')], 'syl',
                  '( %s -> ran %s C_ NN0 )' % (c2, MV1)), y2in], 'sseldd', '( %s -> y e. NN0 )' % c2)], 'id', '') if False else \
        s([s([s([L2(L(a2)), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (c2, MV1, MV1)), w.inst('frn')], 'syl',
             '( %s -> ran %s C_ NN0 )' % (c2, MV1)), y2in], 'sseldd', '( %s -> y e. NN0 )' % c2)
    me = s([s([L2(L(pn)), yn2], 'jca', '( %s -> ( P e. NN0 /\\ y e. NN0 ) )' % c2), L2(L(a1)), w.inst('mulallel')], 'syl2anc',
           '( %s -> ( y e. ran %s <-> E. d e. ran %s y = ( d x. P ) ) )' % (c2, MV1, DV))
    exd = s([me, y2in], 'mpbid', '( %s -> E. d e. ran %s y = ( d x. P ) )' % (c2, DV))
    pd = '( ( %s /\\ d e. ran %s ) /\\ y = ( d x. P ) )' % (c2, DV)
    Ld = lambda st: s([s([st], 'adantr', '( ( %s /\\ d e. ran %s ) -> %s )' % (c2, DV, concl_of(w, c2, st)))], 'adantr', '( %s -> %s )' % (pd, concl_of(w, c2, st)))
    din = s([], 'simplr', '( %s -> d e. ran %s )' % (pd, DV))
    rvd = s([s([], 'breq1', '( x = d -> ( x <_ %s <-> d <_ %s ) )' % (EV, EV))], 'rspcv', '( d e. ran %s -> ( %s -> d <_ %s ) )' % (DV, BODY('V'), EV))
    dle = s([din, Ld(L2(L(ihs))), rvd], 'sylc', '( %s -> d <_ %s )' % (pd, EV))
    dn = s([s([s([Ld(L2(L(a1))), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pd, DV, DV)), w.inst('frn')], 'syl',
              '( %s -> ran %s C_ NN0 )' % (pd, DV)), din], 'sseldd', '( %s -> d e. NN0 )' % pd)
    pr = s([Ld(L2(L(pn)))], 'nn0red', '( %s -> P e. RR )' % pd)
    ple = s([s([Ld(L2(L(plt)))], 'ltled' if False else 'ltled', '( %s -> P <_ %s )' % (pd, P2))], 'id', '') if False else \
        s([pr, s([Ld(L2(L(p2n)))], 'nn0red', '( %s -> %s e. RR )' % (pd, P2)), Ld(L2(L(plt)))], 'ltled', '( %s -> P <_ %s )' % (pd, P2))
    mul = s([s([dn], 'nn0red', '( %s -> d e. RR )' % pd), s([Ld(L2(L(evn)))], 'nn0red', '( %s -> %s e. RR )' % (pd, EV)), pr,
             s([Ld(L2(L(p2n)))], 'nn0red', '( %s -> %s e. RR )' % (pd, P2)), s([dn], 'nn0ge0d', '( %s -> 0 <_ d )' % pd),
             s([Ld(L2(L(pn)))], 'nn0ge0d', '( %s -> 0 <_ P )' % pd), dle, ple], 'lemul12ad', '( %s -> ( d x. P ) <_ ( %s x. %s ) )' % (pd, EV, P2))
    m2 = s([mul, Ld(L2(L(ec)))], 'breqtrrd', '( %s -> ( d x. P ) <_ %s )' % (pd, EC))
    yle = s([s([], 'simpr', '( %s -> y = ( d x. P ) )' % pd), m2], 'eqbrtrd', '( %s -> y <_ %s )' % (pd, EC))
    k2 = s([exd, s([s([yle], 'ex', '( ( %s /\\ d e. ran %s ) -> ( y = ( d x. P ) -> y <_ %s ) )' % (c2, DV, EC))], 'rexlimdva',
                   '( %s -> ( E. d e. ran %s y = ( d x. P ) -> y <_ %s ) )' % (c2, DV, EC))], 'mpd', '( %s -> y <_ %s )' % (c2, EC))
    ky = s([k1, k2, yor], 'mpjaodan', '( %s -> y <_ %s )' % (pa, EC))
    ry = s([ky], 'ralrimiva', '( %s -> A. y e. ran %s y <_ %s )' % (A2, D1(CSV), EC))
    cb = s([s([], 'breq1', '( y = x -> ( y <_ %s <-> x <_ %s ) )' % (EC, EC))], 'cbvralvw', '( A. y e. ran %s y <_ %s <-> %s )' % (D1(CSV), EC, BODY(CSV)))
    w.qed([s([ry, cb], 'sylib', '( %s -> %s )' % (A2, BODY(CSV)))], 'ex', '( %s -> %s )' % (A, co))


def closed_2cn(w, ph):
    return w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % ph)


def closed_2re(w, ph):
    return w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph)


def concl_of(w, ph, st):
    for l in w.lines:
        if l.startswith(st + ':'):
            f = l.split('|-', 1)[1].strip()
            assert f.startswith('( %s -> ' % ph), (f[:200], ph[:200])
            return f[len('( %s -> ' % ph):-2]
    raise KeyError(st)


def _f_dl(w, st, phit):
    T = '( S e. Word NN0 /\\ %s )' % HB('S')
    sw = w.s([], 'simpl', '( %s -> S e. Word NN0 )' % T)
    a = w.s([sw, w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit))
    w.qed([w.s([], 'simpr', '( %s -> %s )' % (T, HB('S'))), a], 'mpd', STMTS['divisorsofle'])


# ======================================================================= the geometric sum
YF = '( i e. NN0 |-> ( ( ( 2 ^ i ) + 1 ) x. C ) )'
SUMG = 'sum_ j e. ( 0 ..^ N ) ( ( %s ` j ) + 2 )' % YF
GB = '( ( 2 ^ N ) x. ( ( 2 x. C ) + 2 ) )'
STMTS['tmdvgeo'] = '( ( C e. NN0 /\\ N e. NN0 ) -> ( %s + 2 ) <_ %s )' % (SUMG, GB)


def tmdvgeo():
    lab = 'tmdvgeo'
    ph = '( C e. NN0 /\\ N e. NN0 )'
    w = W(lab, 'Lean\'s ` sum_geom_bound ` : ` sum_ ( j < n ) ( ( 2 ^ j + 1 ) C + 2 ) + 2 <_ 2 ^ n ( 2 C + 2 ) ` (~ geo2sum2 , '
               '~ tpl2pow ), with the per-entry charge of ` divisorsOfF ` as a map.')
    s = w.s
    cn = s([], 'simpl', '( %s -> C e. NN0 )' % ph)
    nn = s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    pj = '( %s /\\ j e. ( 0 ..^ N ) )' % ph
    jn = s([s([], 'simpr', '( %s -> j e. ( 0 ..^ N ) )' % pj), w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj)
    cj_ = s([cn], 'adantr', '( %s -> C e. NN0 )' % pj)
    V_ = '( ( ( 2 ^ j ) + 1 ) x. C )'
    hy = s([s([s([], 'oveq2', '( i = j -> ( 2 ^ i ) = ( 2 ^ j ) )')], 'oveq1d', '( i = j -> ( ( 2 ^ i ) + 1 ) = ( ( 2 ^ j ) + 1 ) )')], 'oveq1d',
           '( i = j -> ( ( ( 2 ^ i ) + 1 ) x. C ) = %s )' % V_)
    fv = s([jn, s([s([], 'ovex', '%s e. _V' % V_)], 'a1i', '( %s -> %s e. _V )' % (pj, V_)), hy, w.inst('fvmpt3') if False else None], 'id', '') if False else None
    fv = s([hy, s([s([], 'eqid', '%s = %s' % (YF, YF))], 'a1i', '( %s -> %s = %s )' % (pj, YF, YF)) if False else None, jn], 'id', '') if False else None
    fvm = s([hy, s([], 'eqid', '%s = %s' % (YF, YF)), s([], 'ovex', '%s e. _V' % V_)], 'fvmpt', '( j e. NN0 -> ( %s ` j ) = %s )' % (YF, V_))
    fvj = s([jn, fvm], 'syl', '( %s -> ( %s ` j ) = %s )' % (pj, YF, V_))
    P2J = '( 2 ^ j )'
    cl = Closure(w, pj, {'C': ('NN0', cj_)})
    p2jn = s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % pj), jn], 'nn0expcld', '( %s -> %s e. NN0 )' % (pj, P2J))
    cl.leaf(P2J, 'NN0', p2jn)
    al = lineq(w, pj, '( %s + 2 )' % V_, '( ( %s x. C ) + ( C + 2 ) )' % P2J, closure=cl, products=True)
    e1 = s([s([fvj], 'oveq1d', '( %s -> ( ( %s ` j ) + 2 ) = ( %s + 2 ) )' % (pj, YF, V_)), al], 'eqtrd',
           '( %s -> ( ( %s ` j ) + 2 ) = ( ( %s x. C ) + ( C + 2 ) ) )' % (pj, YF, P2J))
    S2 = 'sum_ j e. ( 0 ..^ N ) ( ( %s x. C ) + ( C + 2 ) )' % P2J
    s1 = s([e1], 'sumeq2dv', '( %s -> %s = %s )' % (ph, SUMG, S2))
    fin = s([s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % ph)
    t1c = cl.mem('( %s x. C )' % P2J, 'CC')
    t2c = cl.mem('( C + 2 )', 'CC')
    SA = 'sum_ j e. ( 0 ..^ N ) ( %s x. C )' % P2J
    SB = 'sum_ j e. ( 0 ..^ N ) ( C + 2 )'
    s2 = s([fin, t1c, t2c], 'fsumadd', '( %s -> %s = ( %s + %s ) )' % (ph, S2, SA, SB))
    p2c = cl.mem(P2J, 'CC')
    ccn = s([cn], 'nn0cnd', '( %s -> C e. CC )' % ph)
    s3 = s([fin, ccn, p2c], 'fsummulc1', '( %s -> ( sum_ j e. ( 0 ..^ N ) %s x. C ) = %s )' % (ph, P2J, SA))
    g2 = s([nn, w.inst('geo2sum2')], 'syl', '( %s -> sum_ j e. ( 0 ..^ N ) %s = ( ( 2 ^ N ) - 1 ) )' % (ph, P2J))
    s4 = s([s3, s([g2], 'oveq1d', '( %s -> ( sum_ j e. ( 0 ..^ N ) %s x. C ) = ( ( ( 2 ^ N ) - 1 ) x. C ) )' % (ph, P2J))], 'eqtr3d',
           '( %s -> %s = ( ( ( 2 ^ N ) - 1 ) x. C ) )' % (ph, SA))
    c2c = s([s([cn, s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph)], 'nn0addcld', '( %s -> ( C + 2 ) e. NN0 )' % ph)], 'nn0cnd',
            '( %s -> ( C + 2 ) e. CC )' % ph)
    s5 = s([fin, c2c, w.inst('fsumconst')], 'syl2anc', '( %s -> %s = ( ( # ` ( 0 ..^ N ) ) x. ( C + 2 ) ) )' % (ph, SB))
    s6 = s([s5, s([s([nn, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` ( 0 ..^ N ) ) = N )' % ph)], 'oveq1d',
                  '( %s -> ( ( # ` ( 0 ..^ N ) ) x. ( C + 2 ) ) = ( N x. ( C + 2 ) ) )' % ph)], 'eqtrd', '( %s -> %s = ( N x. ( C + 2 ) ) )' % (ph, SB))
    tot = s([s([s1, s2], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (ph, SUMG, SA, SB)), s([s4, s6], 'oveq12d',
                                                                                          '( %s -> ( %s + %s ) = ( ( ( ( 2 ^ N ) - 1 ) x. C ) + ( N x. ( C + 2 ) ) ) )' % (ph, SA, SB))],
            'eqtrd', '( %s -> %s = ( ( ( ( 2 ^ N ) - 1 ) x. C ) + ( N x. ( C + 2 ) ) ) )' % (ph, SUMG))
    c0 = Closure(w, ph, {'C': ('NN0', cn), 'N': ('NN0', nn)})
    P2N = '( 2 ^ N )'
    c0.leaf(P2N, 'NN0', s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), nn], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, P2N)))
    tp = s([nn, w.inst('tpl2pow')], 'syl', '( %s -> ( N + 1 ) <_ %s )' % (ph, P2N))
    m1 = s([c0.mem('( N + 1 )', 'RR'), c0.mem(P2N, 'RR'), c0.mem('( C + 2 )', 'RR'), c0.ge0('( C + 2 )') if hasattr(c0, 'ge0') else None, tp],
           'lemul1ad', '( %s -> ( ( N + 1 ) x. ( C + 2 ) ) <_ ( %s x. ( C + 2 ) ) )' % (ph, P2N))
    le = linarith(w, ph, [m1, c0.ge0('C')], '( ( ( ( %s - 1 ) x. C ) + ( N x. ( C + 2 ) ) ) + 2 ) <_ %s' % (P2N, GB), closure=c0,
                  atoms=['C', 'N', P2N], products=True)
    w.qed([s([tot], 'oveq1d', '( %s -> ( %s + 2 ) = ( ( ( ( %s - 1 ) x. C ) + ( N x. ( C + 2 ) ) ) + 2 ) )' % (ph, SUMG, P2N)), le], 'eqbrtrd',
          STMTS['tmdvgeo'])
    return w.run()


# ======================================================================= the accumulator of divisorsOfF
RW = '( reverse ` W )'
PJ = lambda j: '( %s prefix %s )' % (RW, j)
DJ = lambda j: '( 1st ` ( DivisorsOf ` ( reverse ` %s ) ) )' % PJ(j)
ACC = lambda j: '( reverse ` %s )' % DJ(j)
QJ = '( %s ` J )' % RW
MJ = '( 1st ` ( %s MulAll %s ) )' % (QJ, ACC('J'))
MM = '( ( ( # ` W ) x. N ) + 1 )'
HW = '( W e. Word NN0 /\\ N e. NN0 /\\ A. a e. ran W a < ( 2 ^ N ) )'
STMTS['tmdvacc'] = '( ( W e. Word NN0 /\\ J e. ( 0 ..^ ( # ` W ) ) ) -> %s = ( %s ++ %s ) )' % (ACC('( J + 1 )'), MJ, ACC('J'))
STMTS['tmdvlen'] = '( ( W e. Word NN0 /\\ J e. ( 0 ... ( # ` W ) ) ) -> ( # ` %s ) = ( 2 ^ J ) )' % ACC('J')
STMTS['tmdvbnd'] = '( ( %s /\\ J e. ( 0 ... ( # ` W ) ) ) -> A. a e. ran %s a < ( 2 ^ %s ) )' % (HW, ACC('J'), MM)
STMTS['tmdvmbd'] = ('( ( %s /\\ J e. ( 0 ..^ ( # ` W ) ) ) -> ( ( %s < ( 2 ^ N ) /\\ %s < ( 2 ^ %s ) ) /\\ A. a e. ran %s a < ( 2 ^ ( 2 x. %s ) ) ) )'
                    % (HW, QJ, QJ, MM, MJ, MM))


def dvw(w, ph, ww, j, jz):
    """( ph -> DJ( j ) e. Word NN0 ) , ( ph -> ( reverse ` PJ( j ) ) e. Word NN0 )"""
    s = w.s
    rw = s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RW))
    pw = s([rw, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PJ(j)))
    rp = s([pw, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word NN0 )' % (ph, PJ(j)))
    d = s([s([rp, w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` ( reverse ` %s ) ) e. %s )' % (ph, PJ(j), WN)), w.inst('xp1st')], 'syl',
          '( %s -> %s e. Word NN0 )' % (ph, DJ(j)))
    return d, rp, pw, rw


def tmdvacc():
    lab = 'tmdvacc'
    ph = '( W e. Word NN0 /\\ J e. ( 0 ..^ ( # ` W ) ) )'
    w = W(lab, 'The accumulator of ` divisorsOfF ` one element on (Lean ` divisorsOf_rev_take_succ ` ): the reversed subset products '
               'of the reversed first ` j + 1 ` elements of ` Q.reverse ` are the products by ` q = Q.reverse[j] ` of the old '
               'accumulator, followed by the old accumulator (~ divisorsofcs , ~ mulallrev ).')
    s = w.s
    ww = s([], 'simpl', '( %s -> W e. Word NN0 )' % ph)
    jj = s([], 'simpr', '( %s -> J e. ( 0 ..^ ( # ` W ) ) )' % ph)
    d0, rp0, pw0, rw = dvw(w, ph, ww, 'J', None)
    jr = s([jj, s([s([s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))], 'eqcomd',
                     '( %s -> ( # ` W ) = ( # ` %s ) )' % (ph, RW))], 'oveq2d', '( %s -> ( 0 ..^ ( # ` W ) ) = ( 0 ..^ ( # ` %s ) ) )' % (ph, RW))],
           'eleqtrd', '( %s -> J e. ( 0 ..^ ( # ` %s ) ) )' % (ph, RW))
    qn = s([rw, jr, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, QJ))
    pf = s([rw, jr, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ <" %s "> ) )' % (ph, PJ('( J + 1 )'), PJ('J'), QJ))
    sq = s([qn, w.inst('s1cl')], 'syl', '( %s -> <" %s "> e. Word NN0 )' % (ph, QJ))
    r1 = s([pw0, sq, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( ( reverse ` <" %s "> ) ++ ( reverse ` %s ) ) )'
           % (ph, PJ('J'), QJ, QJ, PJ('J')))
    V = '( reverse ` %s )' % PJ('J')
    CS_ = '( <" %s "> ++ %s )' % (QJ, V)
    r2 = s([s([pf], 'fveq2d', '( %s -> ( reverse ` %s ) = ( reverse ` ( %s ++ <" %s "> ) ) )' % (ph, PJ('( J + 1 )'), PJ('J'), QJ)),
            s([r1, s([s([s([], 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (QJ, QJ))], 'a1i', '( %s -> ( reverse ` <" %s "> ) = <" %s "> )' % (ph, QJ, QJ))],
                     'oveq1d', '( %s -> ( ( reverse ` <" %s "> ) ++ %s ) = %s )' % (ph, QJ, V, CS_))], 'eqtrd',
              '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = %s )' % (ph, PJ('J'), QJ, CS_))], 'eqtrd',
           '( %s -> ( reverse ` %s ) = %s )' % (ph, PJ('( J + 1 )'), CS_))
    DV = DJ('J')
    MQ = '( %s MulAll %s )' % (QJ, DV)
    cs = s([qn, rp0, w.inst('divisorsofcs')], 'syl2anc', '( %s -> ( DivisorsOf ` %s ) = <. ( %s ++ ( 1st ` %s ) ) , ( ( 2nd ` ( DivisorsOf ` %s ) ) + ( 2nd ` %s ) ) >. )'
           % (ph, CS_, DV, MQ, V, MQ))
    cl = s([rp0, w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` %s ) e. %s )' % (ph, V, WN))
    a1, b1 = paircl(w, ph, '( DivisorsOf ` %s )' % V, cl, 'Word NN0', 'NN0')
    clm = s([qn, a1, w.inst('mulallcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, MQ, WN))
    a2, b2 = paircl(w, ph, MQ, clm, 'Word NN0', 'NN0')
    xa = s([a1, a2, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ ( 1st ` %s ) ) e. Word NN0 )' % (ph, DV, MQ))
    xb = s([b1, b2], 'nn0addcld', '( %s -> ( ( 2nd ` ( DivisorsOf ` %s ) ) + ( 2nd ` %s ) ) e. NN0 )' % (ph, V, MQ))
    p1 = projeq(w, ph, '( DivisorsOf ` %s )' % CS_, cs, '( %s ++ ( 1st ` %s ) )' % (DV, MQ), '( ( 2nd ` ( DivisorsOf ` %s ) ) + ( 2nd ` %s ) )' % (V, MQ), xa, xb, 1)
    d1 = s([s([s([r2], 'fveq2d', '( %s -> ( DivisorsOf ` ( reverse ` %s ) ) = ( DivisorsOf ` %s ) )' % (ph, PJ('( J + 1 )'), CS_))], 'fveq2d',
              '( %s -> %s = ( 1st ` ( DivisorsOf ` %s ) ) )' % (ph, DJ('( J + 1 )'), CS_)), p1], 'eqtrd',
           '( %s -> %s = ( %s ++ ( 1st ` %s ) ) )' % (ph, DJ('( J + 1 )'), DV, MQ))
    rv = s([a1, a2, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ ( 1st ` %s ) ) ) = ( ( reverse ` ( 1st ` %s ) ) ++ ( reverse ` %s ) ) )'
           % (ph, DV, MQ, MQ, DV))
    mr = s([qn, a1, w.inst('mulallrev')], 'syl2anc', '( %s -> ( 1st ` ( %s MulAll ( reverse ` %s ) ) ) = ( reverse ` ( 1st ` %s ) ) )' % (ph, QJ, DV, MQ))
    e1 = s([s([d1], 'fveq2d', '( %s -> %s = ( reverse ` ( %s ++ ( 1st ` %s ) ) ) )' % (ph, ACC('( J + 1 )'), DV, MQ)), rv], 'eqtrd',
           '( %s -> %s = ( ( reverse ` ( 1st ` %s ) ) ++ ( reverse ` %s ) ) )' % (ph, ACC('( J + 1 )'), MQ, DV))
    w.qed([e1, s([mr], 'oveq1d', '( %s -> ( %s ++ %s ) = ( ( reverse ` ( 1st ` %s ) ) ++ %s ) )' % (ph, MJ, ACC('J'), MQ, ACC('J')))], 'eqtr4d',
          STMTS['tmdvacc'])
    return w.run()


def tmdvlen():
    lab = 'tmdvlen'
    ph = '( W e. Word NN0 /\\ J e. ( 0 ... ( # ` W ) ) )'
    w = W(lab, 'The accumulator of ` divisorsOfF ` after ` j ` elements has ` 2 ^ j ` entries (Lean ` divisorsOf_rev_take_length ` ).')
    s = w.s
    ww = s([], 'simpl', '( %s -> W e. Word NN0 )' % ph)
    jj = s([], 'simpr', '( %s -> J e. ( 0 ... ( # ` W ) ) )' % ph)
    d0, rp0, pw0, rw = dvw(w, ph, ww, 'J', None)
    jr = s([jj, s([s([s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))], 'eqcomd',
                     '( %s -> ( # ` W ) = ( # ` %s ) )' % (ph, RW))], 'oveq2d', '( %s -> ( 0 ... ( # ` W ) ) = ( 0 ... ( # ` %s ) ) )' % (ph, RW))],
           'eleqtrd', '( %s -> J e. ( 0 ... ( # ` %s ) ) )' % (ph, RW))
    l1 = s([d0, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ACC('J'), DJ('J')))
    l2 = s([rp0, w.inst('divisorsoflen')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` ( reverse ` %s ) ) ) )' % (ph, DJ('J'), PJ('J')))
    l3 = s([s([pw0, w.inst('revlen')], 'syl', '( %s -> ( # ` ( reverse ` %s ) ) = ( # ` %s ) )' % (ph, PJ('J'), PJ('J'))),
            s([rw, jr, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = J )' % (ph, PJ('J')))], 'eqtrd', '( %s -> ( # ` ( reverse ` %s ) ) = J )' % (ph, PJ('J')))
    w.qed([s([l1, l2], 'eqtrd', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` ( reverse ` %s ) ) ) )' % (ph, ACC('J'), PJ('J'))),
           s([l3], 'oveq2d', '( %s -> ( 2 ^ ( # ` ( reverse ` %s ) ) ) = ( 2 ^ J ) )' % (ph, PJ('J')))], 'eqtrd', STMTS['tmdvlen'])
    return w.run()


def ranpj(w, ph, ww, rw, jr, j):
    """( ph -> ran ( reverse ` PJ( j ) ) C_ ran W ) from jr : ( ph -> j e. ( 0 ... ( # ` RW ) ) )"""
    s = w.s
    pw = s([rw, w.inst('pfxcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PJ(j)))
    a = s([pw, w.inst('tm2lrnrev')], 'syl', '( %s -> ran ( reverse ` %s ) C_ ran %s )' % (ph, PJ(j), PJ(j)))
    rs = s([rw, jr, w.inst('pfxres')], 'syl2anc', '( %s -> %s = ( %s |` ( 0 ..^ %s ) ) )' % (ph, PJ(j), RW, j))
    b = s([s([rs], 'rneqd', '( %s -> ran %s = ran ( %s |` ( 0 ..^ %s ) ) )' % (ph, PJ(j), RW, j)),
           s([s([], 'rnresss', 'ran ( %s |` ( 0 ..^ %s ) ) C_ ran %s' % (RW, j, RW))], 'a1i', '( %s -> ran ( %s |` ( 0 ..^ %s ) ) C_ ran %s )' % (ph, RW, j, RW))],
          'eqsstrd', '( %s -> ran %s C_ ran %s )' % (ph, PJ(j), RW))
    c = s([ww, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran W )' % (ph, RW))
    return s([s([a, b], 'sstrd', '( %s -> ran ( reverse ` %s ) C_ ran %s )' % (ph, PJ(j), RW)), c], 'sstrd',
             '( %s -> ran ( reverse ` %s ) C_ ran W )' % (ph, PJ(j)))


def tmdvbnd():
    lab = 'tmdvbnd'
    ph = '( %s /\\ J e. ( 0 ... ( # ` W ) ) )' % HW
    w = W(lab, 'The accumulator of ` divisorsOfF ` has entries below ` 2 ^ ( # Q b + 1 ) ` (Lean ` divisorsOf_rev_take_mem_lt ` , '
               '~ divisorsofle ).')
    s = w.s
    c = Ctx(w, ph, (('W e. Word NN0', 'N e. NN0', 'A. a e. ran W a < ( 2 ^ N )'), 'J e. ( 0 ... ( # ` W ) )'))
    ww, nn, ral, jj = c['W e. Word NN0'], c['N e. NN0'], c['A. a e. ran W a < ( 2 ^ N )'], c['J e. ( 0 ... ( # ` W ) )']
    d0, rp0, pw0, rw = dvw(w, ph, ww, 'J', None)
    jr = s([jj, s([s([s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))], 'eqcomd',
                     '( %s -> ( # ` W ) = ( # ` %s ) )' % (ph, RW))], 'oveq2d', '( %s -> ( 0 ... ( # ` W ) ) = ( 0 ... ( # ` %s ) ) )' % (ph, RW))],
           'eleqtrd', '( %s -> J e. ( 0 ... ( # ` %s ) ) )' % (ph, RW))
    V = '( reverse ` %s )' % PJ('J')
    rs = ranpj(w, ph, ww, rw, jr, 'J')
    rv = s([rs, ral, w.inst('ssralv')], 'sylc', '( %s -> A. a e. ran %s a < ( 2 ^ N ) )' % (ph, V))
    cb = s([s([], 'breq1', '( a = p -> ( a < ( 2 ^ N ) <-> p < ( 2 ^ N ) ) )')], 'cbvralvw',
           '( A. a e. ran %s a < ( 2 ^ N ) <-> A. p e. ran %s p < ( 2 ^ N ) )' % (V, V))
    rvp = s([rv, cb], 'sylib', '( %s -> A. p e. ran %s p < ( 2 ^ N ) )' % (ph, V))
    EXJ = '( 2 ^ ( ( # ` %s ) x. N ) )' % V
    dl = s([rp0, s([nn, rvp], 'jca', '( %s -> ( N e. NN0 /\\ A. p e. ran %s p < ( 2 ^ N ) ) )' % (ph, V)), w.inst('divisorsofle')], 'syl2anc',
           '( %s -> A. x e. ran %s x <_ %s )' % (ph, DJ('J'), EXJ))
    # EXJ < 2 ^ MM
    lj = s([s([pw0, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, V, PJ('J'))),
            s([rw, jr, w.inst('pfxlen')], 'syl2anc', '( %s -> ( # ` %s ) = J )' % (ph, PJ('J')))], 'eqtrd', '( %s -> ( # ` %s ) = J )' % (ph, V))
    jn = s([jj, w.inst('elfznn0')], 'syl', '( %s -> J e. NN0 )' % ph)
    jl = s([jj, w.inst('elfzle2')], 'syl', '( %s -> J <_ ( # ` W ) )' % ph)
    from cl import Closure
    cl = Closure(w, ph, {'N': ('NN0', nn), 'J': ('NN0', jn)})
    cl.leaf('( # ` W )', 'NN0', s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph))
    jb = s([cl.mem('J', 'RR'), cl.mem('( # ` W )', 'RR'), cl.mem('N', 'RR'), cl.ge0('N'), jl], 'lemul1ad', '( %s -> ( J x. N ) <_ ( ( # ` W ) x. N ) )' % ph)
    lt = linarith(w, ph, [jb], '( J x. N ) < %s' % MM, closure=cl, products=True)
    e2 = s([s([s([s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph), cl.mem('( J x. N )', 'ZZ'), cl.mem(MM, 'ZZ')], '3jca',
              '( %s -> ( 2 e. RR /\\ ( J x. N ) e. ZZ /\\ %s e. ZZ ) )' % (ph, MM)),
            s([s([s([], '1lt2', '1 < 2')], 'a1i', '( %s -> 1 < 2 )' % ph), lt], 'jca', '( %s -> ( 1 < 2 /\\ ( J x. N ) < %s ) )' % (ph, MM)), w.inst('ltexp2a')],
           'syl2anc', '( %s -> ( 2 ^ ( J x. N ) ) < ( 2 ^ %s ) )' % (ph, MM))
    ex2 = s([s([lj], 'oveq1d', '( %s -> ( ( # ` %s ) x. N ) = ( J x. N ) )' % (ph, V))], 'oveq2d', '( %s -> %s = ( 2 ^ ( J x. N ) ) )' % (ph, EXJ))
    elt = s([ex2, e2], 'eqbrtrd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, EXJ, MM))
    # for p e. ran ACC
    pa = '( %s /\\ p e. ran %s )' % (ph, ACC('J'))
    L = lambda st: s([st], 'adantr', '( %s -> %s )' % (pa, concl_of(w, ph, st)))
    pin = s([L(s([d0, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran %s )' % (ph, ACC('J'), DJ('J')))), s([], 'simpr', '( %s -> p e. ran %s )' % (pa, ACC('J')))],
            'sseldd', '( %s -> p e. ran %s )' % (pa, DJ('J')))
    rsp = s([s([], 'breq1', '( x = p -> ( x <_ %s <-> p <_ %s ) )' % (EXJ, EXJ))], 'rspcv', '( p e. ran %s -> ( A. x e. ran %s x <_ %s -> p <_ %s ) )'
            % (DJ('J'), DJ('J'), EXJ, EXJ))
    ple = s([pin, L(dl), rsp], 'sylc', '( %s -> p <_ %s )' % (pa, EXJ))
    pnn = s([s([s([L(d0), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, DJ('J'), DJ('J'))), w.inst('frn')], 'syl',
               '( %s -> ran %s C_ NN0 )' % (pa, DJ('J'))), pin], 'sseldd', '( %s -> p e. NN0 )' % pa)
    exr = s([s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), cl.mem('( ( # ` %s ) x. N )' % V, 'NN0') if False else
                s([s([s([pw0, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, V)), w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, V)), nn],
                  'nn0mulcld', '( %s -> ( ( # ` %s ) x. N ) e. NN0 )' % (ph, V))], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, EXJ))], 'nn0red', '( %s -> %s e. RR )' % (ph, EXJ))
    mmr = s([s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), cl.mem(MM, 'NN0')], 'nn0expcld', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, MM))],
            'nn0red', '( %s -> ( 2 ^ %s ) e. RR )' % (ph, MM))
    plt = s([s([pnn], 'nn0red', '( %s -> p e. RR )' % pa), L(exr), L(mmr), ple, L(elt)], 'lelttrd', '( %s -> p < ( 2 ^ %s ) )' % (pa, MM))
    rp = s([plt], 'ralrimiva', '( %s -> A. p e. ran %s p < ( 2 ^ %s ) )' % (ph, ACC('J'), MM))
    cb2 = s([s([], 'breq1', '( p = a -> ( p < ( 2 ^ %s ) <-> a < ( 2 ^ %s ) ) )' % (MM, MM))], 'cbvralvw',
            '( A. p e. ran %s p < ( 2 ^ %s ) <-> A. a e. ran %s a < ( 2 ^ %s ) )' % (ACC('J'), MM, ACC('J'), MM))
    w.qed([rp, cb2], 'sylib', STMTS['tmdvbnd'])
    return w.run()


def tmdvmbd():
    lab = 'tmdvmbd'
    ph = '( %s /\\ J e. ( 0 ..^ ( # ` W ) ) )' % HW
    w = W(lab, 'The multiplier ` q = Q.reverse[j] ` of one ` divisorsOfF ` element is below ` 2 ^ b ` and ` 2 ^ ( # Q b + 1 ) ` , and '
               'the products ` mulAll q acc ` are below ` 2 ^ ( 2 ( # Q b + 1 ) ) ` (Lean ` divBody_runs ` , ` mulAll_mem_lt ` ).')
    s = w.s
    c = Ctx(w, ph, (('W e. Word NN0', 'N e. NN0', 'A. a e. ran W a < ( 2 ^ N )'), 'J e. ( 0 ..^ ( # ` W ) )'))
    ww, nn, ral, jj = c['W e. Word NN0'], c['N e. NN0'], c['A. a e. ran W a < ( 2 ^ N )'], c['J e. ( 0 ..^ ( # ` W ) )']
    rw = s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RW))
    jr = s([jj, s([s([s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))], 'eqcomd',
                     '( %s -> ( # ` W ) = ( # ` %s ) )' % (ph, RW))], 'oveq2d', '( %s -> ( 0 ..^ ( # ` W ) ) = ( 0 ..^ ( # ` %s ) ) )' % (ph, RW))],
           'eleqtrd', '( %s -> J e. ( 0 ..^ ( # ` %s ) ) )' % (ph, RW))
    qr = s([s([s([rw, w.inst('wrdfn')], 'syl', '( %s -> %s Fn ( 0 ..^ ( # ` %s ) ) )' % (ph, RW, RW)), jr, w.inst('fnfvelrn')], 'syl2anc',
              '( %s -> %s e. ran %s )' % (ph, QJ, RW)), s([ww, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran W )' % (ph, RW))], 'id', '') if False else None
    qin = s([s([ww, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran W )' % (ph, RW)),
             s([s([rw, w.inst('wrdfn')], 'syl', '( %s -> %s Fn ( 0 ..^ ( # ` %s ) ) )' % (ph, RW, RW)), jr, w.inst('fnfvelrn')], 'syl2anc',
               '( %s -> %s e. ran %s )' % (ph, QJ, RW))], 'sseldd', '( %s -> %s e. ran W )' % (ph, QJ))
    qlt = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ N ) <-> %s < ( 2 ^ N ) ) )' % (QJ, QJ)), qin, ral], 'rspcdva' if False else 'rspcv', '') if False else None
    rv = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ N ) <-> %s < ( 2 ^ N ) ) )' % (QJ, QJ))], 'rspcv',
           '( %s e. ran W -> ( A. a e. ran W a < ( 2 ^ N ) -> %s < ( 2 ^ N ) ) )' % (QJ, QJ))
    qlt = s([qin, ral, rv], 'sylc', '( %s -> %s < ( 2 ^ N ) )' % (ph, QJ))
    from cl import Closure
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> J e. NN0 )' % ph)
    cl = Closure(w, ph, {'N': ('NN0', nn), 'J': ('NN0', jn)})
    cl.leaf('( # ` W )', 'NN0', s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph))
    jlt = s([jj, w.inst('elfzolt2')], 'syl', '( %s -> J < ( # ` W ) )' % ph)
    j1l = s([jlt, s([cl.mem('J', 'ZZ'), cl.mem('( # ` W )', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( J < ( # ` W ) <-> ( J + 1 ) <_ ( # ` W ) ) )' % ph)],
            'mpbid', '( %s -> ( J + 1 ) <_ ( # ` W ) )' % ph)
    w1 = linarith(w, ph, [j1l, cl.ge0('J')], '1 <_ ( # ` W )', closure=cl)
    nm = s([s([s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % ph), cl.mem('( # ` W )', 'RR'), cl.mem('N', 'RR'), cl.ge0('N'), w1], 'lemul1ad',
           '( %s -> ( 1 x. N ) <_ ( ( # ` W ) x. N ) )' % ph)
    nle = linarith(w, ph, [nm], 'N <_ %s' % MM, closure=cl, products=True)
    uz = s([s([cl.mem('N', 'ZZ'), cl.mem(MM, 'ZZ'), nle], '3jca', '( %s -> ( N e. ZZ /\\ %s e. ZZ /\\ N <_ %s ) )' % (ph, MM, MM)), w.inst('eluz2')], 'sylibr',
           '( %s -> %s e. ( ZZ>= ` N ) )' % (ph, MM))
    p2le = s([s([s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph), s([s([], '1le2', '1 <_ 2')], 'a1i', '( %s -> 1 <_ 2 )' % ph), uz, w.inst('leexp2a')],
             'syl3anc', '( %s -> ( 2 ^ N ) <_ ( 2 ^ %s ) )' % (ph, MM))
    qn = s([rw, jr, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, QJ))
    p2n = s([s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), nn], 'nn0expcld', '( %s -> ( 2 ^ N ) e. NN0 )' % ph)], 'nn0red',
            '( %s -> ( 2 ^ N ) e. RR )' % ph)
    pmn = s([s([s([s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph), cl.mem(MM, 'NN0')], 'nn0expcld', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, MM))],
            'nn0red', '( %s -> ( 2 ^ %s ) e. RR )' % (ph, MM))
    qlm = s([s([qn], 'nn0red', '( %s -> %s e. RR )' % (ph, QJ)), p2n, pmn, qlt, p2le], 'ltletrd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, QJ, MM))
    # the products
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> J e. ( 0 ... ( # ` W ) ) )' % ph)
    ab = s([s([s([ww, nn, ral], '3jca', '( %s -> %s )' % (ph, HW)), jz], 'jca', '( %s -> ( %s /\\ J e. ( 0 ... ( # ` W ) ) ) )' % (ph, HW)), w.inst('tmdvbnd')],
           'syl', '( %s -> A. a e. ran %s a < ( 2 ^ %s ) )' % (ph, ACC('J'), MM))
    d0, rp0, pw0, _ = dvw(w, ph, ww, 'J', None)
    accw = s([d0, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, ACC('J')))
    P2 = '( 2 ^ %s )' % MM
    Q2 = '( 2 ^ ( 2 x. %s ) )' % MM
    pa = '( %s /\\ p e. ran %s )' % (ph, MJ)
    L = lambda st: s([st], 'adantr', '( %s -> %s )' % (pa, concl_of(w, ph, st)))
    pin = s([], 'simpr', '( %s -> p e. ran %s )' % (pa, MJ))
    mjw = s([s([qn, accw, w.inst('mulallcl')], 'syl2anc', '( %s -> ( %s MulAll %s ) e. %s )' % (ph, QJ, ACC('J'), WN)), w.inst('xp1st')], 'syl',
            '( %s -> %s e. Word NN0 )' % (ph, MJ))
    pn = s([s([s([L(mjw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, MJ, MJ)), w.inst('frn')], 'syl',
              '( %s -> ran %s C_ NN0 )' % (pa, MJ)), pin], 'sseldd', '( %s -> p e. NN0 )' % pa)
    el = s([s([L(qn), pn], 'jca', '( %s -> ( %s e. NN0 /\\ p e. NN0 ) )' % (pa, QJ)), L(accw), w.inst('mulallel')], 'syl2anc',
           '( %s -> ( p e. ran %s <-> E. d e. ran %s p = ( d x. %s ) ) )' % (pa, MJ, ACC('J'), QJ))
    ex = s([el, pin], 'mpbid', '( %s -> E. d e. ran %s p = ( d x. %s ) )' % (pa, ACC('J'), QJ))
    pd = '( ( %s /\\ d e. ran %s ) /\\ p = ( d x. %s ) )' % (pa, ACC('J'), QJ)
    Ld = lambda st: s([s([st], 'adantr', '( ( %s /\\ d e. ran %s ) -> %s )' % (pa, ACC('J'), concl_of(w, pa, st)))], 'adantr', '( %s -> %s )' % (pd, concl_of(w, pa, st)))
    din = s([], 'simplr', '( %s -> d e. ran %s )' % (pd, ACC('J')))
    rvd = s([s([], 'breq1', '( a = d -> ( a < %s <-> d < %s ) )' % (P2, P2))], 'rspcv', '( d e. ran %s -> ( A. a e. ran %s a < %s -> d < %s ) )' % (ACC('J'), ACC('J'), P2, P2))
    dlt = s([din, Ld(L(ab)), rvd], 'sylc', '( %s -> d < %s )' % (pd, P2))
    dn = s([s([s([Ld(L(accw)), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pd, ACC('J'), ACC('J'))), w.inst('frn')], 'syl',
              '( %s -> ran %s C_ NN0 )' % (pd, ACC('J'))), din], 'sseldd', '( %s -> d e. NN0 )' % pd)
    pr = s([Ld(L(pmn))], 'id', '( %s -> %s e. RR )' % (pd, P2)) if False else Ld(L(pmn))
    m = s([s([dn], 'nn0red', '( %s -> d e. RR )' % pd), pr, s([Ld(L(qn))], 'nn0red', '( %s -> %s e. RR )' % (pd, QJ)), pr,
           s([dn], 'nn0ge0d', '( %s -> 0 <_ d )' % pd), s([Ld(L(qn))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (pd, QJ)), dlt, Ld(L(qlm))],
          'ltmul12ad', '( %s -> ( d x. %s ) < ( %s x. %s ) )' % (pd, QJ, P2, P2))
    mmn = Ld(L(cl.mem(MM, 'NN0')))
    tw = s([s([mmn], 'nn0cnd', '( %s -> %s e. CC )' % (pd, MM))], '2timesd', '( %s -> ( 2 x. %s ) = ( %s + %s ) )' % (pd, MM, MM, MM))
    ea = s([s([s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % pd), mmn, mmn], 'expaddd', '( %s -> ( 2 ^ ( %s + %s ) ) = ( %s x. %s ) )' % (pd, MM, MM, P2, P2))
    e2 = s([s([tw], 'oveq2d', '( %s -> %s = ( 2 ^ ( %s + %s ) ) )' % (pd, Q2, MM, MM)), ea], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (pd, Q2, P2, P2))
    lt = s([s([], 'simpr', '( %s -> p = ( d x. %s ) )' % (pd, QJ)), s([m, e2], 'breqtrrd', '( %s -> ( d x. %s ) < %s )' % (pd, QJ, Q2))], 'eqbrtrd',
           '( %s -> p < %s )' % (pd, Q2))
    r2 = s([ex, s([s([lt], 'ex', '( ( %s /\\ d e. ran %s ) -> ( p = ( d x. %s ) -> p < %s ) )' % (pa, ACC('J'), QJ, Q2))], 'rexlimdva',
                  '( %s -> ( E. d e. ran %s p = ( d x. %s ) -> p < %s ) )' % (pa, ACC('J'), QJ, Q2))], 'mpd', '( %s -> p < %s )' % (pa, Q2))
    rp = s([r2], 'ralrimiva', '( %s -> A. p e. ran %s p < %s )' % (ph, MJ, Q2))
    cb = s([s([], 'breq1', '( p = a -> ( p < %s <-> a < %s ) )' % (Q2, Q2))], 'cbvralvw', '( A. p e. ran %s p < %s <-> A. a e. ran %s a < %s )' % (MJ, Q2, MJ, Q2))
    ra = s([rp, cb], 'sylib', '( %s -> A. a e. ran %s a < %s )' % (ph, MJ, Q2))
    w.qed([s([qlt, qlm], 'jca', '( %s -> ( %s < ( 2 ^ N ) /\\ %s < %s ) )' % (ph, QJ, QJ, P2)), ra], 'jca', STMTS['tmdvmbd'])
    return w.run()


if __name__ == '__main__':
    family(run, 'divisorsofle', PHI_DL, _b_dl, _s_dl, finish=_f_dl,
           desc='A subset product of a list of numbers below ` 2 ^ b ` is at most ` 2 ^ ( # Q b ) ` (Lean ` divisorsOf_mem_le ` ).',
           only=only or ['-'])
    for _l in ('tmdvgeo', 'tmdvacc', 'tmdvlen', 'tmdvbnd', 'tmdvmbd'):
        if _l in only:
            globals()[_l]()
