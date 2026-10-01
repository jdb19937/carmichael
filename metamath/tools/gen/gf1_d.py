"""Sortie GF1, section D: G1 (gf1ga, gf1g10, gf1g1v, gf1g1h, gf1g1b).
MM_DB=sorties/gf1.mm MM_ENGINE=mmatch python3 tools/gen/gf1_d.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from gf1lib import *
from mvlib import ringeq
import gf1_c
from gf1_c import hol_ph_s, hol_phl_s, avgsub

only = sys.argv[1:]
gf1_c.only = only


def gen_ga():
    w = W('gf1ga', '` abs _G ( Z + 1 ) <_ 4896 exp ( - abs Im Z ) ` on ` -1/50 <_ Re Z <_ 0 ` ( ~ z5dgam for ` abs Im Z >_ 1/2 ` , ~ z6gam1632 below): the Gamma input of Lemma 6.2, replacing GammaStrip\'s I8(a) and I8(b) there.')
    X0, CONC = split_imp(S['gf1ga'])
    d = mk(w, X0)
    one = a1(w, X0, 'ax-1cn', '1 e. CC')
    zc = proj(w, X0, 'Z e. CC')
    r1 = proj(w, X0, '-u ( 1 / ; 5 0 ) <_ ( Re ` Z )'); r2 = proj(w, X0, '( Re ` Z ) <_ 0')
    V = '( Z + 1 )'
    vc = d('addcld', [zc, one], '%s e. CC' % V)
    rv = d('eqtrd', [d('syl2anc', [zc, one, w.inst('readd')], '( Re ` %s ) = ( ( Re ` Z ) + ( Re ` 1 ) )' % V),
                     d('oveq2d', [a1(w, X0, 're1', '( Re ` 1 ) = 1')], '( ( Re ` Z ) + ( Re ` 1 ) ) = ( ( Re ` Z ) + 1 )')], '( Re ` %s ) = ( ( Re ` Z ) + 1 )' % V)
    izr = d('imcld', [zc], '( Im ` Z ) e. RR')
    izc = d('recnd', [izr], '( Im ` Z ) e. CC')
    iv0 = d('eqtrd', [d('syl2anc', [zc, one, w.inst('imadd')], '( Im ` %s ) = ( ( Im ` Z ) + ( Im ` 1 ) )' % V),
                      d('oveq2d', [a1(w, X0, 'im1', '( Im ` 1 ) = 0')], '( ( Im ` Z ) + ( Im ` 1 ) ) = ( ( Im ` Z ) + 0 )')], '( Im ` %s ) = ( ( Im ` Z ) + 0 )' % V)
    iv = d('eqtrd', [iv0, d('addridd', [izc], '( ( Im ` Z ) + 0 ) = ( Im ` Z )')], '( Im ` %s ) = ( Im ` Z )' % V)
    AT = '( abs ` ( Im ` Z ) )'
    ATV = '( abs ` ( Im ` %s ) )' % V
    aiv = d('fveq2d', [iv], '%s = %s' % (ATV, AT))
    rz = d('recld', [zc], '( Re ` Z ) e. RR')
    rvr = d('recld', [vc], '( Re ` %s ) e. RR' % V)
    cl = Closure(w, X0, {'( Re ` Z )': rz, '( Re ` %s )' % V: rvr})
    cl.atom('( Re ` %s )' % V)
    v0 = lin.linarith(w, X0, [rv, r1], '0 < ( Re ` %s )' % V, closure=cl)
    v0l = lin.linarith(w, X0, [rv, r1], '0 <_ ( Re ` %s )' % V, closure=cl)
    v1 = lin.linarith(w, X0, [rv, r2], '( Re ` %s ) <_ 1' % V, closure=cl)
    vh = lin.linarith(w, X0, [rv, r1], '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % V, closure=cl)
    v3 = lin.linarith(w, X0, [rv, r2], '( Re ` %s ) <_ 3' % V, closure=cl)
    vd = d('syl', [d('jca', [vc, v0], '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (V, V)), w.inst('zrenn')], '%s e. ( CC \\ ( ZZ \\ NN ) )' % V)
    GV = '( abs ` ( _G ` %s ) )' % V
    gvr = d('abscld', [d('syl', [vd, w.inst('gamcl')], '( _G ` %s ) e. CC' % V)], '%s e. RR' % GV)
    atr = d('abscld', [izc], '%s e. RR' % AT)
    E = '( exp ` -u %s )' % AT
    nat = d('renegcld', [atr], '-u %s e. RR' % AT)
    er = d('reefcld', [nat], '%s e. RR' % E)
    e0 = d('ltled', [a1(w, X0, '0re', '0 e. RR'), er, d('syl', [nat, w.inst('efgt0')], '0 < %s' % E)], '0 <_ %s' % E)
    K = '( ; ; ; 4 8 9 6 x. %s )' % E
    # branch 1: 1/2 <_ |Im Z|, z5dgam
    X1 = '( %s /\\ ( 1 / 2 ) <_ %s )' % (X0, AT)
    d1 = mk(w, X1); L1 = lambda st: lift(w, st, X1)
    hv = d1('breqtrrd', [w.s([], 'simpr', '( %s -> ( 1 / 2 ) <_ %s )' % (X1, AT)), L1(aiv)], '( 1 / 2 ) <_ %s' % ATV)
    g = d1('syl', [d1('jca', [L1(vc), d1('3jca', [L1(v0l), L1(v1), hv], '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 /\\ ( 1 / 2 ) <_ %s )' % (V, V, ATV))],
                      '( %s e. CC /\\ ( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 /\\ ( 1 / 2 ) <_ %s ) )' % (V, V, V, ATV)), w.inst('z5dgam')],
           '%s <_ ( ; 6 0 x. ( exp ` -u %s ) )' % (GV, ATV))
    g2 = d1('breqtrd', [g, d1('oveq2d', [d1('fveq2d', [d1('negeqd', [L1(aiv)], '-u %s = -u %s' % (ATV, AT))], '( exp ` -u %s ) = %s' % (ATV, E))],
                             '( ; 6 0 x. ( exp ` -u %s ) ) = ( ; 6 0 x. %s )' % (ATV, E))], '%s <_ ( ; 6 0 x. %s )' % (GV, E))
    c1 = Closure(w, X1, {E: L1(er), GV: L1(gvr)})
    c1.atom(E); c1.atom(GV)
    b1 = lin.linarith(w, X1, [g2, L1(e0)], '%s <_ %s' % (GV, K), closure=c1)
    # branch 2: |Im Z| < 1/2, z6gam1632
    X2 = '( %s /\\ %s < ( 1 / 2 ) )' % (X0, AT)
    d2 = mk(w, X2); L2 = lambda st: lift(w, st, X2)
    P2 = '( 2 ^c -u ( %s / 2 ) )' % ATV
    GB = '( ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( ; ; ; 1 6 3 2 x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) ) )'
    GBV = '( ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 ) -> %s <_ ( ; ; ; 1 6 3 2 x. %s ) )' % (V, V, GV, P2)
    sv = w.s([], 'fveq2', '( d = %s -> ( Re ` d ) = ( Re ` %s ) )' % (V, V))
    sv1 = w.s([sv], 'breq2d', '( d = %s -> ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` d ) <-> ( 1 / ; ; 1 0 0 ) <_ ( Re ` %s ) ) )' % (V, V))
    sv2 = w.s([sv], 'breq1d', '( d = %s -> ( ( Re ` d ) <_ 3 <-> ( Re ` %s ) <_ 3 ) )' % (V, V))
    sv3 = w.s([sv1, sv2], 'anbi12d', '( d = %s -> ( ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 ) <-> ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 ) ) )' % (V, V, V))
    sg = w.s([w.s([], 'fveq2', '( d = %s -> ( _G ` d ) = ( _G ` %s ) )' % (V, V))], 'fveq2d', '( d = %s -> ( abs ` ( _G ` d ) ) = %s )' % (V, GV))
    si = w.s([w.s([w.s([w.s([], 'fveq2', '( d = %s -> ( Im ` d ) = ( Im ` %s ) )' % (V, V))], 'fveq2d', '( d = %s -> ( abs ` ( Im ` d ) ) = %s )' % (V, ATV))],
                   'oveq1d', '( d = %s -> ( ( abs ` ( Im ` d ) ) / 2 ) = ( %s / 2 ) )' % (V, ATV))], 'negeqd', '( d = %s -> -u ( ( abs ` ( Im ` d ) ) / 2 ) = -u ( %s / 2 ) )' % (V, ATV))
    sp = w.s([si], 'oveq2d', '( d = %s -> ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) = %s )' % (V, P2))
    sk = w.s([sp], 'oveq2d', '( d = %s -> ( ; ; ; 1 6 3 2 x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) ) = ( ; ; ; 1 6 3 2 x. %s ) )' % (V, P2))
    sb = w.s([sg, sk], 'breq12d', '( d = %s -> ( ( abs ` ( _G ` d ) ) <_ ( ; ; ; 1 6 3 2 x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) ) <-> %s <_ ( ; ; ; 1 6 3 2 x. %s ) ) )' % (V, GV, P2))
    s4 = w.s([sv3, sb], 'imbi12d', '( d = %s -> ( %s <-> %s ) )' % (V, GB, GBV))
    rs = w.s([s4], 'rspcv', '( %s e. CC -> ( A. d e. CC %s -> %s ) )' % (V, GB, GBV))
    z16 = a1(w, X2, 'z6gam1632', 'A. d e. CC %s' % GB)
    gbv = d2('mpd', [z16, d2('syl', [L2(vc), rs], '( A. d e. CC %s -> %s )' % (GB, GBV))], GBV)
    gb2 = d2('mpd', [d2('jca', [L2(vh), L2(v3)], '( ( 1 / ; ; 1 0 0 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (V, V)), gbv], '%s <_ ( ; ; ; 1 6 3 2 x. %s )' % (GV, P2))
    # 2 ^c -u ( |Im V| / 2 ) <_ 1
    atvr = d2('abscld', [d2('imcld', [L2(vc)], '( Im ` %s ) e. RR' % V) if False else d2('recnd', [d2('imcld', [L2(vc)], '( Im ` %s ) e. RR' % V)], '( Im ` %s ) e. CC' % V)], '%s e. RR' % ATV)
    atv0 = d2('absge0d', [d2('recnd', [d2('imcld', [L2(vc)], '( Im ` %s ) e. RR' % V)], '( Im ` %s ) e. CC' % V)], '0 <_ %s' % ATV)
    hx = d2('rehalfcld', [atvr], '( %s / 2 ) e. RR' % ATV)
    nhx = d2('renegcld', [hx], '-u ( %s / 2 ) e. RR' % ATV)
    ch = Closure(w, X2, {ATV: atvr})
    le0 = lin.linarith(w, X2, [atv0], '-u ( %s / 2 ) <_ 0' % ATV, closure=ch)
    cxl = d2('mpbid', [le0, d2('syl2anc', [d2('jca', [a1(w, X2, '2re', '2 e. RR'), a1(w, X2, '1lt2', '1 < 2')], '( 2 e. RR /\\ 1 < 2 )'),
                                          d2('jca', [nhx, a1(w, X2, '0re', '0 e. RR')], '( -u ( %s / 2 ) e. RR /\\ 0 e. RR )' % ATV), w.inst('cxple')],
                                  '( -u ( %s / 2 ) <_ 0 <-> %s <_ ( 2 ^c 0 ) )' % (ATV, P2))], '%s <_ ( 2 ^c 0 )' % P2)
    cx1 = d2('breqtrd', [cxl, a1(w, X2, 'ax-mp', '( 2 ^c 0 ) = 1', [w.s([], '2cn', '2 e. CC'), w.inst('cxp0')])], '%s <_ 1' % P2)
    p2r = d2('rpred', [d2('rpcxpcld', [a1(w, X2, '2rp', '2 e. RR+'), nhx], '%s e. RR+' % P2)], '%s e. RR' % P2)
    # exp ( - |Im Z| ) >_ 1/3
    ee = '( exp ` 1 )'
    em = d2('breq1i' if False else 'mpbir', [], '') if False else None
    ec = a1(w, X2, 'efcan', '( %s x. ( exp ` -u 1 ) ) = 1' % ee, [w.s([], 'ax-1cn', '1 e. CC'), w.inst('efcan')]) if False else \
        a1(w, X2, 'ax-mp', '( %s x. ( exp ` -u 1 ) ) = 1' % ee, [w.s([], 'ax-1cn', '1 e. CC'), w.inst('efcan')])
    e3 = a1(w, X2, 'eqbrtrri', '%s < 3' % ee, [w.s([], 'df-e', '_e = %s' % ee), w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')])
    em1 = '( exp ` -u 1 )'
    em1r = d2('reefcld', [a1(w, X2, 'neg1rr', '-u 1 e. RR')], '%s e. RR' % em1)
    em10 = d2('ltled', [a1(w, X2, '0re', '0 e. RR'), em1r, a1(w, X2, 'ax-mp', '0 < %s' % em1, [w.s([], 'neg1rr', '-u 1 e. RR'), w.inst('efgt0')])], '0 <_ %s' % em1)
    eer = d2('reefcld', [a1(w, X2, '1re', '1 e. RR')], '%s e. RR' % ee)
    cle = Closure(w, X2, {ee: eer, em1: em1r})
    cle.atom(ee); cle.atom(em1)
    third = lin.nlinarith(w, X2, [ec, e3, em10], '( 1 / 3 ) <_ %s' % em1, closure=cle)
    cla = Closure(w, X2, {AT: L2(atr)})
    lat = lin.linarith(w, X2, [w.s([], 'simpr', '( %s -> %s < ( 1 / 2 ) )' % (X2, AT))], '-u 1 <_ -u %s' % AT, closure=cla)
    eml = d2('mpbid', [lat, d2('syl2anc', [a1(w, X2, 'neg1rr', '-u 1 e. RR'), L2(nat), w.inst('efle')], '( -u 1 <_ -u %s <-> %s <_ %s )' % (AT, em1, E))], '%s <_ %s' % (em1, E))
    c2 = Closure(w, X2, {E: L2(er), GV: L2(gvr), P2: p2r, em1: em1r})
    for a_ in [E, GV, P2, em1]:
        c2.atom(a_)
    b2 = lin.nlinarith(w, X2, [gb2, cx1, third, eml, d2('ltled', [a1(w, X2, '0re', '0 e. RR'), p2r, d2('rpgt0d', [d2('rpcxpcld', [a1(w, X2, '2rp', '2 e. RR+'), nhx], '%s e. RR+' % P2)], '0 < %s' % P2)], '0 <_ %s' % P2)],
                       '%s <_ %s' % (GV, K), closure=c2)
    tri = d('syl2anc', [a1(w, X0, 'halfre', '( 1 / 2 ) e. RR'), atr, w.inst('lelttric')], '( ( 1 / 2 ) <_ %s \\/ %s < ( 1 / 2 ) )' % (AT, AT))
    fin = d('mpjaodan', [b1, b2, tri], CONC)
    w.qed([fin], 'idi', S['gf1ga'])
    return run(w, only)


def kqsub(w, x, y):
    """( x = y -> KQ(A, B, L, x) = KQ(A, B, L, y) )"""
    BA = '( B - A )'
    p1 = w.s([phsub(w, 'L', x, y)], 'oveq1d', '( %s = %s -> ( %s / L ) = ( %s / L ) )' % (x, y, PH('L', x), PH('L', y)))
    e1 = w.s([w.s([], 'oveq2', '( %s = %s -> ( A x. %s ) = ( A x. %s ) )' % (x, y, x, y))], 'fveq2d', '( %s = %s -> ( exp ` ( A x. %s ) ) = ( exp ` ( A x. %s ) ) )' % (x, y, x, y))
    e2 = w.s([e1, phsub(w, BA, x, y)], 'oveq12d', '( %s = %s -> ( ( exp ` ( A x. %s ) ) x. %s ) = ( ( exp ` ( A x. %s ) ) x. %s ) )' % (x, y, x, PH(BA, x), y, PH(BA, y)))
    return w.s([p1, e2], 'oveq12d', '( %s = %s -> %s = %s )' % (x, y, KQ('A', 'B', 'L', x), KQ('A', 'B', 'L', y)))


def gen_g10():
    w = W('gf1g10', '` G1 ( 0 ) = B - A ` (Lean ` G1_zero ` : ` G1 0 = log X - log M0 ` ).')
    X0, CONC = split_imp(S['gf1g10'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); br = proj(w, X0, 'B e. RR'); lp = proj(w, X0, 'L e. RR+')
    ac = d('recnd', [ar], 'A e. CC'); bc = d('recnd', [br], 'B e. CC'); lc = d('rpcnd', [lp], 'L e. CC'); ln0 = d('rpne0d', [lp], 'L =/= 0')
    BA = '( B - A )'
    g1 = d('eqtrd', [d('fveq2d', [a1(w, X0, '0p1e1', '( 0 + 1 ) = 1')], '( _G ` ( 0 + 1 ) ) = ( _G ` 1 )'), a1(w, X0, 'gam1', '( _G ` 1 ) = 1')], '( _G ` ( 0 + 1 ) ) = 1')
    t0 = a1(w, X0, 'eqid', '0 = 0')
    pl = d('iftrued', [t0], '%s = L' % PH('L', '0'))
    pd = d('iftrued', [t0], '%s = %s' % (PH(BA, '0'), BA))
    q = d('eqtrd', [d('oveq1d', [pl], '( %s / L ) = ( L / L )' % PH('L', '0')), d('dividd', [lc, ln0], '( L / L ) = 1')], '( %s / L ) = 1' % PH('L', '0'))
    ea = d('eqtrd', [d('fveq2d', [d('mul01d', [ac], '( A x. 0 ) = 0')], '( exp ` ( A x. 0 ) ) = ( exp ` 0 )'), a1(w, X0, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( A x. 0 ) ) = 1')
    e2 = d('oveq12d', [ea, pd], '( ( exp ` ( A x. 0 ) ) x. %s ) = ( 1 x. %s )' % (PH(BA, '0'), BA))
    kq = d('oveq12d', [q, e2], '%s = ( 1 x. ( 1 x. %s ) )' % (KQ('A', 'B', 'L', '0'), BA))
    all_ = d('oveq12d', [g1, kq], '%s = ( 1 x. ( 1 x. ( 1 x. %s ) ) )' % (G1('A', 'B', 'L', '0'), BA))
    bac = d('subcld', [bc, ac], '%s e. CC' % BA)
    cl = Closure(w, X0, {BA: ('CC', bac)})
    cl.atom(BA)
    r = ringeq(w, X0, '( 1 x. ( 1 x. ( 1 x. %s ) ) )' % BA, BA, cl)
    fin = d('eqtrd', [all_, r], CONC)
    w.qed([fin], 'idi', S['gf1g10'])
    return run(w, only)


def gen_g1v():
    w = W('gf1g1v', 'Off ` 0 ` , ` G1 ( W ) = _G ( W ) Kker ( W ) ` (Lean ` G1_eq_of_ne ` ; ~ gamp1 , ~ gf1kq ).')
    X0, CONC = split_imp(S['gf1g1v'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); br = proj(w, X0, 'B e. RR'); lp = proj(w, X0, 'L e. RR+'); wc = proj(w, X0, 'W e. CC')
    wd = d('syl', [d('jca', [wc, d('jca', [proj(w, X0, '-u 1 < ( Re ` W )'), proj(w, X0, 'W =/= 0')], '( -u 1 < ( Re ` W ) /\\ W =/= 0 )')],
                     '( W e. CC /\\ ( -u 1 < ( Re ` W ) /\\ W =/= 0 ) )'), w.inst('z6rdg')], 'W e. ( CC \\ ( ZZ \\ NN ) )')
    gp = d('syl', [wd, w.inst('gamp1')], '( _G ` ( W + 1 ) ) = ( ( _G ` W ) x. W )')
    gc = d('syl', [wd, w.inst('gamcl')], '( _G ` W ) e. CC')
    kq = d('syl', [d('3jca', [d('jca', [ar, br], '( A e. RR /\\ B e. RR )'), lp, wc], '( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ /\\ W e. CC )'), w.inst('gf1kq')],
           split_imp(S['gf1kq'])[1])
    KQv = KQ('A', 'B', 'L', 'W'); Kv = KK('A', 'B', 'L', 'W')
    kqc = d('simpld', [kq], '%s e. CC' % KQv)
    ke = d('simprd', [kq], '%s = ( W x. %s )' % (Kv, KQv))
    s1 = d('oveq1d', [gp], '%s = ( ( ( _G ` W ) x. W ) x. %s )' % (G1('A', 'B', 'L', 'W'), KQv))
    s2 = d('mulassd', [gc, wc, kqc], '( ( ( _G ` W ) x. W ) x. %s ) = ( ( _G ` W ) x. ( W x. %s ) )' % (KQv, KQv))
    s3 = d('oveq2d', [d('eqcomd', [ke], '( W x. %s ) = %s' % (KQv, Kv))], '( ( _G ` W ) x. ( W x. %s ) ) = ( ( _G ` W ) x. %s )' % (KQv, Kv))
    fin = chain(w, X0, [G1('A', 'B', 'L', 'W'), '( ( ( _G ` W ) x. W ) x. %s )' % KQv, '( ( _G ` W ) x. ( W x. %s ) )' % KQv, '( ( _G ` W ) x. %s )' % Kv], [s1, s2, s3])
    w.qed([fin], 'idi', S['gf1g1v'])
    return run(w, only)


HP0 = "( `' Re \" ( 0 (,) +oo ) )"


def gen_g1h():
    w = W('gf1g1h', '` G1 ` is holomorphic on ` Re w > -1 ` , including ` w = 0 ` (Lean ` differentiableAt_G1 ` ; ~ z6gamhol shifted by ~ z6hshift , the entire ` KQ ` from ~ gf1ph ).')
    X0, CONC = split_imp(S['gf1g1h'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); br = proj(w, X0, 'B e. RR'); lp = proj(w, X0, 'L e. RR+')
    ac = d('recnd', [ar], 'A e. CC'); bc = d('recnd', [br], 'B e. CC'); lc = d('rpcnd', [lp], 'L e. CC'); ln0 = d('rpne0d', [lp], 'L =/= 0')
    BA = '( B - A )'
    bac = d('subcld', [bc, ac], '%s e. CC' % BA)
    # KQ entire
    h1 = hol_phl_s(w, X0, 'L', lc, ln0)
    h2 = w.s([ac, w.inst('gf1eh')], 'syl', '( %s -> %s )' % (X0, HOL('( s e. CC |-> ( exp ` ( A x. s ) ) )', 'CC')))
    h3 = hol_ph_s(w, X0, BA, bac)
    h23 = d('z6ehmul', [h2, h3], HOL('( s e. CC |-> ( ( exp ` ( A x. s ) ) x. %s ) )' % PH(BA, 's'), 'CC'))
    KQS = '( s e. CC |-> %s )' % KQ('A', 'B', 'L', 's')
    hk = d('z6ehmul', [h1, h23], HOL(KQS, 'CC'))
    # Gamma on HP 0, renamed
    GZ = '( z e. %s |-> ( _G ` z ) )' % HP0
    GY = '( y e. %s |-> ( _G ` y ) )' % HP0
    cb = w.s([w.s([], 'fveq2', '( z = y -> ( _G ` z ) = ( _G ` y ) )')], 'cbvmptv', '%s = %s' % (GZ, GY))
    hg = d('mpd', [a1(w, X0, 'z6gamhol', HOL(GZ, HP0)), holeq(w, X0, w.s([cb], 'a1i', '( %s -> %s = %s )' % (X0, GZ, GY)), GZ, GY, HP0)], HOL(GY, HP0))
    # shifts
    opn = a1(w, X0, 'hpopn', '%s e. ( TopOpen ` CCfld )' % HPM1)
    Xw = '( %s /\\ w e. %s )' % (X0, HPM1)
    dw = mk(w, Xw)
    wm = dw('mpbid', [w.s([], 'simpr', '( %s -> w e. %s )' % (Xw, HPM1)), dw('syl', [a1(w, Xw, 'neg1rr', '-u 1 e. RR'), w.inst('elhp2')], '( w e. %s <-> ( w e. CC /\\ -u 1 < ( Re ` w ) ) )' % HPM1)],
             '( w e. CC /\\ -u 1 < ( Re ` w ) )')
    wcc = dw('simpld', [wm], 'w e. CC'); wre = dw('simprd', [wm], '-u 1 < ( Re ` w )')
    one = a1(w, Xw, 'ax-1cn', '1 e. CC')
    w1c = dw('addcld', [wcc, one], '( w + 1 ) e. CC')
    rw1 = dw('eqtrd', [dw('syl2anc', [wcc, one, w.inst('readd')], '( Re ` ( w + 1 ) ) = ( ( Re ` w ) + ( Re ` 1 ) )'),
                       dw('oveq2d', [a1(w, Xw, 're1', '( Re ` 1 ) = 1')], '( ( Re ` w ) + ( Re ` 1 ) ) = ( ( Re ` w ) + 1 )')], '( Re ` ( w + 1 ) ) = ( ( Re ` w ) + 1 )')
    rwr = dw('recld', [wcc], '( Re ` w ) e. RR'); rw1r = dw('recld', [w1c], '( Re ` ( w + 1 ) ) e. RR')
    cl = Closure(w, Xw, {'( Re ` w )': rwr, '( Re ` ( w + 1 ) )': rw1r})
    cl.atom('( Re ` ( w + 1 ) )')
    pos = lin.linarith(w, Xw, [rw1, wre], '0 < ( Re ` ( w + 1 ) )', closure=cl)
    inhp = dw('mpbird', [dw('jca', [w1c, pos], '( ( w + 1 ) e. CC /\\ 0 < ( Re ` ( w + 1 ) ) )'),
                         dw('syl', [a1(w, Xw, '0re', '0 e. RR'), w.inst('elhp2')], '( ( w + 1 ) e. %s <-> ( ( w + 1 ) e. CC /\\ 0 < ( Re ` ( w + 1 ) ) ) )' % HP0)], '( w + 1 ) e. %s' % HP0)
    all1 = d('ralrimiva', [inhp], 'A. w e. %s ( w + 1 ) e. %s' % (HPM1, HP0))
    all0 = d('ralrimiva', [dw('addcld', [wcc, a1(w, Xw, '0cn', '0 e. CC')], '( w + 0 ) e. CC')], 'A. w e. %s ( w + 0 ) e. CC' % HPM1)
    FG = '( z e. %s |-> ( %s ` ( z + 1 ) ) )' % (HPM1, GY)
    FK = '( z e. %s |-> ( %s ` ( z + 0 ) ) )' % (HPM1, KQS)
    sh1 = w.s([d('jca', [hg, d('3jca', [opn, a1(w, X0, 'ax-1cn', '1 e. CC'), all1], '( %s e. ( TopOpen ` CCfld ) /\\ 1 e. CC /\\ A. w e. %s ( w + 1 ) e. %s )' % (HPM1, HPM1, HP0))],
                     '( %s /\\ ( %s e. ( TopOpen ` CCfld ) /\\ 1 e. CC /\\ A. w e. %s ( w + 1 ) e. %s ) )' % (HOL(GY, HP0), HPM1, HPM1, HP0)), w.inst('z6hshift')], 'syl', '( %s -> %s )' % (X0, HOL(FG, HPM1)))
    sh0 = w.s([d('jca', [hk, d('3jca', [opn, a1(w, X0, '0cn', '0 e. CC'), all0], '( %s e. ( TopOpen ` CCfld ) /\\ 0 e. CC /\\ A. w e. %s ( w + 0 ) e. CC )' % (HPM1, HPM1))],
                     '( %s /\\ ( %s e. ( TopOpen ` CCfld ) /\\ 0 e. CC /\\ A. w e. %s ( w + 0 ) e. CC ) )' % (HOL(KQS, 'CC'), HPM1, HPM1)), w.inst('z6hshift')], 'syl', '( %s -> %s )' % (X0, HOL(FK, HPM1)))
    hm = w.s([d('jca', [sh1, sh0], '( %s /\\ %s )' % (HOL(FG, HPM1), HOL(FK, HPM1))), w.inst('holmul')], 'syl',
             '( %s -> %s )' % (X0, HOL('( w e. %s |-> ( ( %s ` w ) x. ( %s ` w ) ) )' % (HPM1, FG, FK), HPM1)))
    # pointwise values
    w_in = w.s([], 'simpr', '( %s -> w e. %s )' % (Xw, HPM1))
    f1 = dw('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Xw, FG, FG)),
                       w.s([w.s([w.s([], 'oveq1', '( z = w -> ( z + 1 ) = ( w + 1 ) )')], 'fveq2d', '( z = w -> ( %s ` ( z + 1 ) ) = ( %s ` ( w + 1 ) ) )' % (GY, GY))], 'adantl',
                           '( ( %s /\\ z = w ) -> ( %s ` ( z + 1 ) ) = ( %s ` ( w + 1 ) ) )' % (Xw, GY, GY)),
                       w_in, a1(w, Xw, 'fvex', '( %s ` ( w + 1 ) ) e. _V' % GY)], '( %s ` w ) = ( %s ` ( w + 1 ) )' % (FG, GY))
    f2 = dw('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Xw, GY, GY)),
                       w.s([w.s([], 'fveq2', '( y = ( w + 1 ) -> ( _G ` y ) = ( _G ` ( w + 1 ) ) )')], 'adantl', '( ( %s /\\ y = ( w + 1 ) ) -> ( _G ` y ) = ( _G ` ( w + 1 ) ) )' % Xw),
                       inhp, a1(w, Xw, 'fvex', '( _G ` ( w + 1 ) ) e. _V')], '( %s ` ( w + 1 ) ) = ( _G ` ( w + 1 ) )' % GY)
    k1 = dw('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Xw, FK, FK)),
                       w.s([w.s([w.s([], 'oveq1', '( z = w -> ( z + 0 ) = ( w + 0 ) )')], 'fveq2d', '( z = w -> ( %s ` ( z + 0 ) ) = ( %s ` ( w + 0 ) ) )' % (KQS, KQS))], 'adantl',
                           '( ( %s /\\ z = w ) -> ( %s ` ( z + 0 ) ) = ( %s ` ( w + 0 ) ) )' % (Xw, KQS, KQS)),
                       w_in, a1(w, Xw, 'fvex', '( %s ` ( w + 0 ) ) e. _V' % KQS)], '( %s ` w ) = ( %s ` ( w + 0 ) )' % (FK, KQS))
    k2 = dw('fveq2d', [dw('addridd', [wcc], '( w + 0 ) = w')], '( %s ` ( w + 0 ) ) = ( %s ` w )' % (KQS, KQS))
    kqwc = dw('simpld', [dw('syl', [dw('3jca', [lift(w, d('jca', [ar, br], '( A e. RR /\\ B e. RR )'), Xw), lift(w, lp, Xw), wcc], '( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ /\\ w e. CC )'), w.inst('gf1kq')],
                                    split_imp(tsub(S['gf1kq'], {'W': 'w'}))[1])], '%s e. CC' % KQ('A', 'B', 'L', 'w'))
    k3 = dw('fvmptd', [w.s([], 'eqidd', '( %s -> %s = %s )' % (Xw, KQS, KQS)),
                       w.s([kqsub(w, 's', 'w')], 'adantl', '( ( %s /\\ s = w ) -> %s = %s )' % (Xw, KQ('A', 'B', 'L', 's'), KQ('A', 'B', 'L', 'w'))),
                       wcc, kqwc], '( %s ` w ) = %s' % (KQS, KQ('A', 'B', 'L', 'w')))
    fv = dw('oveq12d', [dw('eqtrd', [f1, f2], '( %s ` w ) = ( _G ` ( w + 1 ) )' % FG), chain(w, Xw, ['( %s ` w )' % FK, '( %s ` ( w + 0 ) )' % KQS, '( %s ` w )' % KQS, KQ('A', 'B', 'L', 'w')], [k1, k2, k3])],
            '( ( %s ` w ) x. ( %s ` w ) ) = %s' % (FG, FK, G1('A', 'B', 'L', 'w')))
    MP = '( w e. %s |-> ( ( %s ` w ) x. ( %s ` w ) ) )' % (HPM1, FG, FK)
    GW = '( w e. %s |-> %s )' % (HPM1, G1('A', 'B', 'L', 'w'))
    eq = d('mpteq2dva', [fv], '%s = %s' % (MP, GW))
    fin = d('mpd', [hm, holeq(w, X0, eq, MP, GW, HPM1)], CONC)
    w.qed([fin], 'idi', S['gf1g1h'])
    return run(w, only)


def gen_g1b():
    w = W('gf1g1b', 'Blueprint Lemma 6.2, the kernel bounds: for ` -1/50 <_ Re Z <_ 0 ` , ` abs G1 ( Z ) <_ C7 exp ( - abs Im Z / 2 ) Y ` , ` abs Im Z abs G1 <_ C7 exp ( - abs Im Z / 2 ) ` , ` ( Im Z ) ^ 2 L abs G1 <_ 4 C7 exp ( - abs Im Z / 2 ) ` , with ` C7 = 8337480 ` (Lean ` G1_bounds ` ; ~ gf1ga , ~ gf1kqb , ~ gf1kb ).')
    X0, CONC = split_imp(S['gf1g1b'])
    d = mk(w, X0)
    ar = proj(w, X0, 'A e. RR'); br = proj(w, X0, 'B e. RR'); a0 = proj(w, X0, '0 <_ A'); ab = proj(w, X0, 'A <_ B')
    lp = proj(w, X0, 'L e. RR+'); yr = proj(w, X0, 'Y e. RR'); y1 = proj(w, X0, '1 <_ Y')
    hs = proj(w, X0, '( ( B + A ) + ( 2 x. L ) ) <_ ( ( 5 / 2 ) x. Y )')
    zc = proj(w, X0, 'Z e. CC'); z1 = proj(w, X0, '-u ( 1 / ; 5 0 ) <_ ( Re ` Z )'); z2 = proj(w, X0, '( Re ` Z ) <_ 0')
    lr = d('rpred', [lp], 'L e. RR'); l0 = d('rpge0d', [lp], '0 <_ L')
    b0 = d('letrd', [a1(w, X0, '0re', '0 e. RR'), ar, br, a0, ab], '0 <_ B')
    KQv = KQ('A', 'B', 'L', 'Z'); Kv = KK('A', 'B', 'L', 'Z'); Gv = G1('A', 'B', 'L', 'Z')
    GAM = '( _G ` ( Z + 1 ) )'
    ga = d('syl', [d('jca', [zc, d('jca', [z1, z2], '( -u ( 1 / ; 5 0 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 0 )')], split_imp(S['gf1ga'])[0]), w.inst('gf1ga')], split_imp(S['gf1ga'])[1])
    AT = '( abs ` ( Im ` Z ) )'
    ET = '( exp ` -u %s )' % AT
    EH = EXPH('Z')
    kqb = d('syl', [d('3jca', [d('jca', [d('jca', [ar, br], '( A e. RR /\\ B e. RR )'), d('jca', [a0, ab], '( 0 <_ A /\\ A <_ B )')], '( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ A <_ B ) )'),
                                 lp, d('jca', [zc, z2], '( Z e. CC /\\ ( Re ` Z ) <_ 0 )')], tsub(split_imp(S['gf1kqb'])[0], {'W': 'Z'})), w.inst('gf1kqb')],
            '( abs ` %s ) <_ ( B - A )' % KQv)
    kq = d('syl', [d('3jca', [d('jca', [ar, br], '( A e. RR /\\ B e. RR )'), lp, zc], '( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ /\\ Z e. CC )'), w.inst('gf1kq')],
           tsub(split_imp(S['gf1kq'])[1], {'W': 'Z'}))
    kqc = d('simpld', [kq], '%s e. CC' % KQv)
    ke = d('simprd', [kq], '%s = ( Z x. %s )' % (Kv, KQv))
    kb = d('syl', [d('3jca', [d('jca', [d('jca', [ar, br], '( A e. RR /\\ B e. RR )'), d('jca', [a0, b0], '( 0 <_ A /\\ 0 <_ B )')], '( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) )'),
                                lp, zc], tsub(split_imp(S['gf1kb'])[0], {'W': 'Z'})), w.inst('gf1kb')],
           tsub(split_imp(S['gf1kb'])[1], {'W': 'Z'}))
    kb0 = d('mpd', [z2, d('simpld', [kb], tsub('( ( Re ` W ) <_ 0 -> ( ( abs ` %s ) <_ ( ( exp ` ( B x. ( Re ` W ) ) ) + ( exp ` ( A x. ( Re ` W ) ) ) ) /\\ ( abs ` %s ) <_ 2 /\\ ( ( abs ` %s ) x. ( L x. ( abs ` W ) ) ) <_ 4 ) )' % ((KK('A', 'B', 'L', 'W'),) * 3), {'W': 'Z'}))],
              '( ( abs ` %s ) <_ ( ( exp ` ( B x. ( Re ` Z ) ) ) + ( exp ` ( A x. ( Re ` Z ) ) ) ) /\\ ( abs ` %s ) <_ 2 /\\ ( ( abs ` %s ) x. ( L x. ( abs ` Z ) ) ) <_ 4 )' % (Kv, Kv, Kv))
    k2 = d('simp2d', [kb0], '( abs ` %s ) <_ 2' % Kv)
    k4 = d('simp3d', [kb0], '( ( abs ` %s ) x. ( L x. ( abs ` Z ) ) ) <_ 4' % Kv)
    gc = d('syl', [d('addcld', [zc, a1(w, X0, 'ax-1cn', '1 e. CC')], '( Z + 1 ) e. CC') if False else None, w.inst('gamcl')], '') if False else None
    # Gamma ( Z + 1 ) e. CC: Re ( Z + 1 ) > 0
    one = a1(w, X0, 'ax-1cn', '1 e. CC')
    z1c = d('addcld', [zc, one], '( Z + 1 ) e. CC')
    rz1 = d('eqtrd', [d('syl2anc', [zc, one, w.inst('readd')], '( Re ` ( Z + 1 ) ) = ( ( Re ` Z ) + ( Re ` 1 ) )'),
                      d('oveq2d', [a1(w, X0, 're1', '( Re ` 1 ) = 1')], '( ( Re ` Z ) + ( Re ` 1 ) ) = ( ( Re ` Z ) + 1 )')], '( Re ` ( Z + 1 ) ) = ( ( Re ` Z ) + 1 )')
    clr = Closure(w, X0, {'( Re ` Z )': d('recld', [zc], '( Re ` Z ) e. RR'), '( Re ` ( Z + 1 ) )': d('recld', [z1c], '( Re ` ( Z + 1 ) ) e. RR')})
    clr.atom('( Re ` ( Z + 1 ) )')
    pz1 = lin.linarith(w, X0, [rz1, z1], '0 < ( Re ` ( Z + 1 ) )', closure=clr)
    gmc = d('syl', [d('syl', [d('jca', [z1c, pz1], '( ( Z + 1 ) e. CC /\\ 0 < ( Re ` ( Z + 1 ) ) )'), w.inst('zrenn')], '( Z + 1 ) e. ( CC \\ ( ZZ \\ NN ) )'), w.inst('gamcl')], '%s e. CC' % GAM)
    # absolute values
    gv = '( abs ` %s )' % GAM; kv = '( abs ` %s )' % KQv; Kav = '( abs ` %s )' % Kv; Gav = '( abs ` %s )' % Gv; za = '( abs ` Z )'
    gvr = d('abscld', [gmc], '%s e. RR' % gv); gv0 = d('absge0d', [gmc], '0 <_ %s' % gv)
    kvr = d('abscld', [kqc], '%s e. RR' % kv); kv0 = d('absge0d', [kqc], '0 <_ %s' % kv)
    zar = d('abscld', [zc], '%s e. RR' % za); za0 = d('absge0d', [zc], '0 <_ %s' % za)
    Kc = d('subcld', [d('mulcld', [d('efcld', [d('mulcld', [d('recnd', [br], 'B e. CC'), zc], '( B x. Z ) e. CC')], '( exp ` ( B x. Z ) ) e. CC'),
                                   d('divcld', [d('simp1d', [d('syl2anc', [d('rpcnd', [lp], 'L e. CC'), zc, w.inst('gf1phv')], tsub(split_imp(S['gf1phv'])[1], {'C': 'L', 'W': 'Z'}))], '%s e. CC' % PH('L', 'Z')),
                                                d('rpcnd', [lp], 'L e. CC'), d('rpne0d', [lp], 'L =/= 0')], '( %s / L ) e. CC' % PH('L', 'Z'))], '%s e. CC' % AVG('B', 'L', 'Z')),
                      d('mulcld', [d('efcld', [d('mulcld', [d('recnd', [ar], 'A e. CC'), zc], '( A x. Z ) e. CC')], '( exp ` ( A x. Z ) ) e. CC'),
                                   d('divcld', [d('simp1d', [d('syl2anc', [d('rpcnd', [lp], 'L e. CC'), zc, w.inst('gf1phv')], tsub(split_imp(S['gf1phv'])[1], {'C': 'L', 'W': 'Z'}))], '%s e. CC' % PH('L', 'Z')),
                                                d('rpcnd', [lp], 'L e. CC'), d('rpne0d', [lp], 'L =/= 0')], '( %s / L ) e. CC' % PH('L', 'Z'))], '%s e. CC' % AVG('A', 'L', 'Z'))], '%s e. CC' % Kv)
    Kar = d('abscld', [Kc], '%s e. RR' % Kav)
    ag = d('absmuld', [gmc, kqc], '%s = ( %s x. %s )' % (Gav, gv, kv))
    aK = d('eqtrd', [d('fveq2d', [ke], '%s = ( abs ` ( Z x. %s ) )' % (Kav, KQv)), d('absmuld', [zc, kqc], '( abs ` ( Z x. %s ) ) = ( %s x. %s )' % (KQv, za, kv))],
           '%s = ( %s x. %s )' % (Kav, za, kv))
    atr = d('abscld', [d('recnd', [d('imcld', [zc], '( Im ` Z ) e. RR')], '( Im ` Z ) e. CC')], '%s e. RR' % AT)
    at0 = d('absge0d', [d('recnd', [d('imcld', [zc], '( Im ` Z ) e. RR')], '( Im ` Z ) e. CC')], '0 <_ %s' % AT)
    atz = d('syl', [zc, w.inst('absimle')], '%s <_ %s' % (AT, za))
    etr = d('reefcld', [d('renegcld', [atr], '-u %s e. RR' % AT)], '%s e. RR' % ET)
    ehr = d('reefcld', [d('renegcld' if False else 'redivcld', [d('renegcld', [atr], '-u %s e. RR' % AT), a1(w, X0, '2re', '2 e. RR'), a1(w, X0, '2ne0', '2 =/= 0')], '( -u %s / 2 ) e. RR' % AT)], '%s e. RR' % EH)
    eh0 = d('ltled', [a1(w, X0, '0re', '0 e. RR'), ehr, d('syl', [d('redivcld', [d('renegcld', [atr], '-u %s e. RR' % AT), a1(w, X0, '2re', '2 e. RR'), a1(w, X0, '2ne0', '2 =/= 0')], '( -u %s / 2 ) e. RR' % AT), w.inst('efgt0')], '0 < %s' % EH)], '0 <_ %s' % EH)
    ca = Closure(w, X0, {AT: atr})
    ca.atom(AT)
    lx = lin.linarith(w, X0, [at0], '-u %s <_ ( -u %s / 2 )' % (AT, AT), closure=ca)
    eth = d('mpbid', [lx, d('syl2anc', [d('renegcld', [atr], '-u %s e. RR' % AT), d('redivcld', [d('renegcld', [atr], '-u %s e. RR' % AT), a1(w, X0, '2re', '2 e. RR'), a1(w, X0, '2ne0', '2 =/= 0')], '( -u %s / 2 ) e. RR' % AT), w.inst('efle')],
                                  '( -u %s <_ ( -u %s / 2 ) <-> %s <_ %s )' % (AT, AT, ET, EH))], '%s <_ %s' % (ET, EH))
    K7 = '( ; ; ; 4 8 9 6 x. %s )' % ET
    k7r = d('remulcld', [a1(w, X0, 'ax-mp' if False else 'eqid', '0 = 0') if False else d('rpred' if False else 'recnd', [], '') if False else None, etr], '') if False else None
    n4896 = a1(w, X0, 'ax-mp' if False else 'eqid', '0 = 0') if False else None
    import num as _num
    k48 = _num.re_nat(w, 4896)
    k7r = d('remulcld', [a1(w, X0, 'a1i' if False else 'idi', '; ; ; 4 8 9 6 e. RR', [k48]) if False else w.s([k48], 'a1i', '( %s -> ; ; ; 4 8 9 6 e. RR )' % X0), etr], '%s e. RR' % K7)
    bar = d('resubcld', [br, ar], '( B - A ) e. RR')
    # (1)
    m1 = d('lemul12ad', [gvr, k7r, kvr, bar, gv0, ga, kv0, kqb], '( %s x. %s ) <_ ( %s x. ( B - A ) )' % (gv, kv, K7))
    c1 = Closure(w, X0, {ET: etr, EH: ehr, 'A': ar, 'B': br, 'L': lr, 'Y': yr})
    c1.atom(ET); c1.atom(EH)
    ey = d('mulge0d', [ehr, yr, eh0, d('letrd', [a1(w, X0, '0re', '0 e. RR'), a1(w, X0, '1re', '1 e. RR'), yr, a1(w, X0, '0le1', '0 <_ 1'), y1], '0 <_ Y')], '0 <_ ( %s x. Y )' % EH)
    ea_ = d('mulge0d', [etr, bar, d('ltled', [a1(w, X0, '0re', '0 e. RR'), etr, d('syl', [d('renegcld', [atr], '-u %s e. RR' % AT), w.inst('efgt0')], '0 < %s' % ET)], '0 <_ %s' % ET),
                        d('subge0d', [br, ar], '( 0 <_ ( B - A ) <-> A <_ B )')] if False else [etr, bar, d('ltled', [a1(w, X0, '0re', '0 e. RR'), etr, d('syl', [d('renegcld', [atr], '-u %s e. RR' % AT), w.inst('efgt0')], '0 < %s' % ET)], '0 <_ %s' % ET),
                        d('mpbird', [ab, d('subge0d', [br, ar], '( 0 <_ ( B - A ) <-> A <_ B )')], '0 <_ ( B - A )')], '0 <_ ( %s x. ( B - A ) )' % ET)
    # ET ( B - A ) <_ EH ( 5/2 ) Y
    ba52 = lin.linarith(w, X0, [hs, a0, l0], '( B - A ) <_ ( ( 5 / 2 ) x. Y )', closure=Closure(w, X0, {'A': ar, 'B': br, 'L': lr, 'Y': yr}))
    et0 = d('ltled', [a1(w, X0, '0re', '0 e. RR'), etr, d('syl', [d('renegcld', [atr], '-u %s e. RR' % AT), w.inst('efgt0')], '0 < %s' % ET)], '0 <_ %s' % ET)
    m2 = d('lemul12ad', [etr, ehr, bar, d('remulcld', [a1(w, X0, 'ax-mp', '( 5 / 2 ) e. RR', [w.s([], '5re', '5 e. RR'), w.s([], '2re', '2 e. RR'), w.s([], '2ne0', '2 =/= 0'), w.inst('redivcli')]) if False else w.s([w.s([w.s([], '5re', '5 e. RR'), w.s([], '2re', '2 e. RR'), w.s([], '2ne0', '2 =/= 0')], 'redivcli', '( 5 / 2 ) e. RR')], 'a1i', '( %s -> ( 5 / 2 ) e. RR )' % X0), yr], '( ( 5 / 2 ) x. Y ) e. RR'),
                         et0, eth, d('mpbird', [ab, d('subge0d', [br, ar], '( 0 <_ ( B - A ) <-> A <_ B )')], '0 <_ ( B - A )'), ba52],
               '( %s x. ( B - A ) ) <_ ( %s x. ( ( 5 / 2 ) x. Y ) )' % (ET, EH))
    cg = Closure(w, X0, {gv: gvr, kv: kvr, ET: etr, EH: ehr, 'A': ar, 'B': br, 'Y': yr, Gav: d('abscld', [d('mulcld', [gmc, kqc], '%s e. CC' % Gv)], '%s e. RR' % Gav)})
    for a_ in [gv, kv, ET, EH, Gav]:
        cg.atom(a_)
    r1 = lin.nlinarith(w, X0, [ag, m1, m2, ey], '%s <_ ( ( %s x. %s ) x. Y )' % (Gav, C7, EH), closure=cg)
    # (2) |theta| |G1| <_ |Z| |G1| = gv |K| <_ 4896 ET 2
    Gar = cg.mem(Gav, 'RR')
    s1 = d('lemul1ad', [atr, zar, Gar, d('absge0d', [d('mulcld', [gmc, kqc], '%s e. CC' % Gv)], '0 <_ %s' % Gav), atz], '( %s x. %s ) <_ ( %s x. %s )' % (AT, Gav, za, Gav))
    cz = Closure(w, X0, {gv: ('CC', d('recnd', [gvr], '%s e. CC' % gv)), kv: ('CC', d('recnd', [kvr], '%s e. CC' % kv)), za: ('CC', d('recnd', [zar], '%s e. CC' % za))})
    for a_ in [gv, kv, za]:
        cz.atom(a_)
    s2 = d('eqtrd', [d('oveq2d', [ag], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (za, Gav, za, gv, kv)), ringeq(w, X0, '( %s x. ( %s x. %s ) )' % (za, gv, kv), '( %s x. ( %s x. %s ) )' % (gv, za, kv), cz)],
           '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (za, Gav, gv, za, kv))
    s3 = d('eqtrd', [s2, d('oveq2d', [d('eqcomd', [aK], '( %s x. %s ) = %s' % (za, kv, Kav))], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (gv, za, kv, gv, Kav))],
           '( %s x. %s ) = ( %s x. %s )' % (za, Gav, gv, Kav))
    m3 = d('lemul12ad', [gvr, k7r, Kar, a1(w, X0, '2re', '2 e. RR'), gv0, ga, d('absge0d', [Kc], '0 <_ %s' % Kav), k2], '( %s x. %s ) <_ ( %s x. 2 )' % (gv, Kav, K7))
    cg2 = Closure(w, X0, {ET: etr, EH: ehr, AT: atr, Gav: Gar, za: zar, gv: gvr, Kav: Kar})
    for a_ in [ET, EH, AT, Gav, za, gv, Kav]:
        cg2.atom(a_)
    r2 = lin.nlinarith(w, X0, [s1, s3, m3, eth, eh0], '( %s x. %s ) <_ ( %s x. %s )' % (AT, Gav, C7, EH), closure=cg2)
    # (3)
    TH = '( Im ` Z )'
    thr = d('imcld', [zc], '%s e. RR' % TH)
    sq1 = d('eqtrd', [d('eqcomd', [d('syl', [thr, w.inst('absresq')], '( %s ^ 2 ) = ( %s ^ 2 )' % (AT, TH))], '( %s ^ 2 ) = ( %s ^ 2 )' % (TH, AT)),
                      d('sqvald', [d('recnd', [atr], '%s e. CC' % AT)], '( %s ^ 2 ) = ( %s x. %s )' % (AT, AT, AT))], '( %s ^ 2 ) = ( %s x. %s )' % (TH, AT, AT))
    LHS3 = '( ( ( %s ^ 2 ) x. L ) x. %s )' % (TH, Gav)
    t1 = d('oveq1d', [d('oveq1d', [sq1], '( ( %s ^ 2 ) x. L ) = ( ( %s x. %s ) x. L )' % (TH, AT, AT))], '%s = ( ( ( %s x. %s ) x. L ) x. %s )' % (LHS3, AT, AT, Gav))
    aa = d('lemul12ad', [atr, zar, atr, zar, at0, atz, at0, atz], '( %s x. %s ) <_ ( %s x. %s )' % (AT, AT, za, za))
    lg0 = d('mulge0d', [lr, Gar, l0, d('absge0d', [d('mulcld', [gmc, kqc], '%s e. CC' % Gv)], '0 <_ %s' % Gav)], '0 <_ ( L x. %s )' % Gav)
    t2 = d('lemul1ad', [d('remulcld', [atr, atr], '( %s x. %s ) e. RR' % (AT, AT)), d('remulcld', [zar, zar], '( %s x. %s ) e. RR' % (za, za)), d('remulcld', [lr, Gar], '( L x. %s ) e. RR' % Gav), lg0, aa],
           '( ( %s x. %s ) x. ( L x. %s ) ) <_ ( ( %s x. %s ) x. ( L x. %s ) )' % (AT, AT, Gav, za, za, Gav))
    cz3 = Closure(w, X0, {gv: ('CC', d('recnd', [gvr], '%s e. CC' % gv)), kv: ('CC', d('recnd', [kvr], '%s e. CC' % kv)), za: ('CC', d('recnd', [zar], '%s e. CC' % za)),
                          AT: ('CC', d('recnd', [atr], '%s e. CC' % AT)), 'L': ('CC', d('rpcnd', [lp], 'L e. CC')), Gav: ('CC', d('recnd', [Gar], '%s e. CC' % Gav))})
    for a_ in [gv, kv, za, AT, Gav]:
        cz3.atom(a_)
    t0 = ringeq(w, X0, '( ( ( %s x. %s ) x. L ) x. %s )' % (AT, AT, Gav), '( ( %s x. %s ) x. ( L x. %s ) )' % (AT, AT, Gav), cz3)
    u1 = d('oveq2d', [d('oveq2d', [ag], '( L x. %s ) = ( L x. ( %s x. %s ) )' % (Gav, gv, kv))], '( ( %s x. %s ) x. ( L x. %s ) ) = ( ( %s x. %s ) x. ( L x. ( %s x. %s ) ) )' % (za, za, Gav, za, za, gv, kv))
    u2 = ringeq(w, X0, '( ( %s x. %s ) x. ( L x. ( %s x. %s ) ) )' % (za, za, gv, kv), '( %s x. ( ( %s x. %s ) x. ( L x. %s ) ) )' % (gv, za, kv, za), cz3)
    u3 = d('oveq2d', [d('oveq1d', [d('eqcomd', [aK], '( %s x. %s ) = %s' % (za, kv, Kav))], '( ( %s x. %s ) x. ( L x. %s ) ) = ( %s x. ( L x. %s ) )' % (za, kv, za, Kav, za))],
           '( %s x. ( ( %s x. %s ) x. ( L x. %s ) ) ) = ( %s x. ( %s x. ( L x. %s ) ) )' % (gv, za, kv, za, gv, Kav, za))
    kl = '( %s x. ( L x. %s ) )' % (Kav, za)
    m4 = d('lemul12ad', [gvr, k7r, d('remulcld', [Kar, d('remulcld', [lr, zar], '( L x. %s ) e. RR' % za)], '%s e. RR' % kl), a1(w, X0, '4re', '4 e. RR'), gv0, ga,
                         d('mulge0d', [Kar, d('remulcld', [lr, zar], '( L x. %s ) e. RR' % za), d('absge0d', [Kc], '0 <_ %s' % Kav), d('mulge0d', [lr, zar, l0, za0], '0 <_ ( L x. %s )' % za)], '0 <_ %s' % kl), k4],
           '( %s x. %s ) <_ ( %s x. 4 )' % (gv, kl, K7))
    ch3a = chain(w, X0, [LHS3, '( ( ( %s x. %s ) x. L ) x. %s )' % (AT, AT, Gav), '( ( %s x. %s ) x. ( L x. %s ) )' % (AT, AT, Gav), '( ( %s x. %s ) x. ( L x. %s ) )' % (za, za, Gav),
                        '( ( %s x. %s ) x. ( L x. ( %s x. %s ) ) )' % (za, za, gv, kv), '( %s x. ( ( %s x. %s ) x. ( L x. %s ) ) )' % (gv, za, kv, za), '( %s x. %s )' % (gv, kl)],
                [t1, t0, t2, u1, u2, u3], ['=', '=', '<_', '=', '=', '='])
    lhs3r = d('remulcld', [d('remulcld', [d('resqcld', [thr], '( %s ^ 2 ) e. RR' % TH), lr], '( ( %s ^ 2 ) x. L ) e. RR' % TH), Gar], '%s e. RR' % LHS3)
    gklr = d('remulcld', [gvr, d('remulcld', [Kar, d('remulcld', [lr, zar], '( L x. %s ) e. RR' % za)], '%s e. RR' % kl)], '( %s x. %s ) e. RR' % (gv, kl))
    ch3 = d('letrd', [lhs3r, gklr, d('remulcld', [k7r, a1(w, X0, '4re', '4 e. RR')], '( %s x. 4 ) e. RR' % K7), ch3a, m4], '%s <_ ( %s x. 4 )' % (LHS3, K7))
    cg3 = Closure(w, X0, {ET: etr, EH: ehr})
    cg3.atom(ET); cg3.atom(EH)
    k7c = d('remulcld', [d('remulcld', [a1(w, X0, '4re', '4 e. RR'), w.s([_num.re_nat(w, 8337480)], 'a1i', '( %s -> %s e. RR )' % (X0, C7))], '( 4 x. %s ) e. RR' % C7), ehr], '( ( 4 x. %s ) x. %s ) e. RR' % (C7, EH))
    fin3 = d('letrd', [lhs3r,
                        d('remulcld', [k7r, a1(w, X0, '4re', '4 e. RR')], '( %s x. 4 ) e. RR' % K7), k7c, ch3,
                        lin.nlinarith(w, X0, [eth, eh0, et0], '( %s x. 4 ) <_ ( ( 4 x. %s ) x. %s )' % (K7, C7, EH), closure=cg3)], '%s <_ ( ( 4 x. %s ) x. %s )' % (LHS3, C7, EH))
    fin = d('3jca', [r1, r2, fin3], CONC)
    w.qed([fin], 'idi', S['gf1g1b'])
    return run(w, only)


if __name__ == '__main__':
    gen_ga()
    gen_g10()
    gen_g1v()
    gen_g1h()
    gen_g1b()
