"""Sortie ZD2: Theorem A at a point (Lean sum_zeroCountBox_le_sq, theoremH, logfree_of_logged_of_mertens):
zd2split, zd2sq, zd2pt."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zd2_base import *
from zc1_m import e_h2

DBN = DB_N
YD = '( %s \\ { %s } )' % (DBN, X0)
EXX = lambda x: '( N DChrLF %s )' % x
ZCXx = lambda x: ZCX('N', x, 'S', 'T')
NCn = NC('N', 'S', 'T'); ZC0n = ZC0('N', 'S', 'T'); NCNPn = NCNP('N', 'S', 'T')


def grp_x0(w, A, c, nn_):
    """( A -> X0 e. DB ), ( A -> DB e. Fin )"""
    g = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); b = w.s([], 'eqid', '%s = %s' % (DBN, DBN)); o = w.s([], 'eqid', '%s = %s' % (X0, X0))
    abl = c([nn_, w.s([g], 'dchrabl', '( N e. NN -> ( DChr ` N ) e. Abel )')], 'syl', '( DChr ` N ) e. Abel')
    grp = c([abl, w.inst('ablgrp')], 'syl', '( DChr ` N ) e. Grp')
    x0 = c([grp, w.s([b, o], 'grpidcl', '( ( DChr ` N ) e. Grp -> %s e. %s )' % (X0, DBN))], 'syl', '%s e. %s' % (X0, DBN))
    dbf = c([nn_, w.s([g, b], 'dchrfi', '( N e. NN -> %s e. Fin )' % DBN)], 'syl', '%s e. Fin' % DBN)
    return x0, dbf


def zcx_re(w, A, c, nn_, sr, s0, s1, tr, x, xin, s_='S'):
    """( A -> ZCX(x) e. RR ), ( A -> 0 <_ ZCX(x) ) for xin : ( A -> x e. DB )"""
    EZ = tsub(stmt('ezf'), {'X': x, 'A': s_})
    eza, ezc = ante_of(EZ)
    ez = c([c([c([nn_, xin], 'jca', '( N e. NN /\\ %s e. %s )' % (x, DBN)), c([c([sr, s0, s1], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (s_, s_, s_)), tr], 'jca', '( ( %s e. RR /\\ 0 < %s /\\ %s <_ 1 ) /\\ T e. RR )' % (s_, s_, s_))], 'jca', eza), w.inst('ezf')], 'syl', ezc)
    Z = ZF(EXX(x), s_, 'T'); OR = '( %s holord q )' % EXX(x)
    fin = c([ez], 'simpld', '%s e. Fin' % Z); al = c([ez], 'simprd', 'A. q e. %s %s e. NN' % (Z, OR))
    Aq = '( %s /\\ q e. %s )' % (A, Z)
    cq = Ctx(w, Aq)
    on = cq([lift(w, al, Aq), cq([], 'simpr', 'q e. %s' % Z), w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (Z, OR, Z, OR))], 'sylc', '%s e. NN' % OR)
    return c([fin, cq([on], 'nnred', '%s e. RR' % OR)], 'fsumrecl', '%s e. RR' % ZCX('N', x, s_, 'T')), c([fin, cq([on], 'nnred', '%s e. RR' % OR), cq([cq([on], 'nnrpd', '%s e. RR+' % OR)], 'rpge0d', '0 <_ %s' % OR)], 'fsumge0', '0 <_ %s' % ZCX('N', x, s_, 'T'))


def nc_re(w, A, c, nn_, sr, s0, s1, tr, s_='S'):
    """NC, ZC0, NCNP real (and NC >_ 0, NCNP >_ 0) at abscissa s_"""
    x0, dbf = grp_x0(w, A, c, nn_)
    Ax = '( %s /\\ x e. %s )' % (A, DBN)
    cx = Ctx(w, Ax)
    L = lambda st: lift(w, st, Ax)
    zr, z0 = zcx_re(w, Ax, cx, L(nn_), L(sr), L(s0), L(s1), L(tr), 'x', cx([], 'simpr', 'x e. %s' % DBN), s_)
    ncr = c([dbf, zr], 'fsumrecl', '%s e. RR' % NC('N', s_, 'T'))
    nc0 = c([dbf, zr, z0], 'fsumge0', '0 <_ %s' % NC('N', s_, 'T'))
    zc0r, _ = zcx_re(w, A, c, nn_, sr, s0, s1, tr, X0, x0, s_)
    ydf = c([dbf, c.a1(w.s([], 'difss', '%s C_ %s' % (YD, DBN)), '%s C_ %s' % (YD, DBN)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % YD)
    Ay = '( %s /\\ x e. %s )' % (A, YD)
    cy = Ctx(w, Ay)
    Ly = lambda st: lift(w, st, Ay)
    xin = cy([cy([], 'simpr', 'x e. %s' % YD), w.inst('eldifi')], 'syl', 'x e. %s' % DBN)
    zry, z0y = zcx_re(w, Ay, cy, Ly(nn_), Ly(sr), Ly(s0), Ly(s1), Ly(tr), 'x', xin, s_)
    npr = c([ydf, zry], 'fsumrecl', '%s e. RR' % NCNP('N', s_, 'T'))
    np0 = c([ydf, zry, z0y], 'fsumge0', '0 <_ %s' % NCNP('N', s_, 'T'))
    return dict(x0=x0, dbf=dbf, ncr=ncr, nc0=nc0, zc0r=zc0r, npr=npr, np0=np0, ydf=ydf, zr=zr, Ax=Ax)


def gen_split():
    w = W('zd2split', 'The character sum of the box counts splits off the principal character (Lean ` logfree_of_logged_of_mertens ` , ` hsplit ` ): ` sum_chi N = N ( chi_0 ) + sum_{ chi =/= chi_0 } N ` ( ~ fsumsplitsn ).')
    A0 = ante_of(S['zd2split'])[0]
    c = Ctx(w, A0)
    nn_, sr, s0, s1, tr = [c.g(x) for x in ('N e. NN', 'S e. RR', '0 < S', 'S <_ 1', 'T e. RR')]
    f = nc_re(w, A0, c, nn_, sr, s0, s1, tr)
    nfph = w.s([], 'nfv', 'F/ x %s' % A0)
    nfd = w.s([], 'nfcv', 'F/_ x %s' % ZC0n)
    nin = c([c.a1(w.s([], 'neldifsnd' if False else 'x', 'x') if False else w.s([], 'neldifsn', '-. %s e. %s' % (X0, YD)), '-. %s e. %s' % (X0, YD))], 'x', 'x') if False else c.a1(w.s([], 'neldifsn', '-. %s e. %s' % (X0, YD)), '-. %s e. %s' % (X0, YD))
    Ay = '( %s /\\ x e. %s )' % (A0, YD)
    cy = Ctx(w, Ay)
    xin = cy([cy([], 'simpr', 'x e. %s' % YD), w.inst('eldifi')], 'syl', 'x e. %s' % DBN)
    zry, _ = zcx_re(w, Ay, cy, lift(w, nn_, Ay), lift(w, sr, Ay), lift(w, s0, Ay), lift(w, s1, Ay), lift(w, tr, Ay), 'x', xin)
    zcc = cy([zry], 'recnd', '%s e. CC' % ZCXx('x'))
    st, val = w.congr(ZCXx('x'), {'x': X0}, 'x = %s' % X0, {'x': w.s([], 'id', '( x = %s -> x = %s )' % (X0, X0))})
    assert val == ZC0n, val[:200]
    dcn = c([f['zc0r']], 'recnd', '%s e. CC' % ZC0n)
    sp = c([nfph, nfd, f['ydf'], c([f['x0']], 'elexd', '%s e. _V' % X0), nin, zcc, st, dcn], 'fsumsplitsn', 'sum_ x e. ( %s u. { %s } ) %s = ( %s + %s )' % (YD, X0, ZCXx('x'), NCNPn, ZC0n))
    un = c([f['x0'], w.inst('difsnid')], 'syl', '( %s u. { %s } ) = %s' % (YD, X0, DBN))
    se = c([un], 'sumeq1d', 'sum_ x e. ( %s u. { %s } ) %s = %s' % (YD, X0, ZCXx('x'), NCn))
    ac = c([c([f['npr']], 'recnd', '%s e. CC' % NCNPn), dcn], 'addcomd', '( %s + %s ) = ( %s + %s )' % (NCNPn, ZC0n, ZC0n, NCNPn))
    w.qed([c([se, sp], 'eqtr3d', '%s = ( %s + %s )' % (NCn, NCNPn, ZC0n)), ac], 'eqtrd', S['zd2split'])
    return go(w)


def gen_sq():
    w = W('zd2sq', 'The I6 absorption (Lean ` sum_zeroCountBox_le_sq ` at ZC1\'s 6400): ` sum_chi N ( S , T , chi ) <_ 6400 ( N ( T + 2 ) ) ^ 2 ` for ` T >_ 1 ` , ` S >_ 1 / 2 ` ( ~ zcmono , ~ zc1sum , ~ zdsqabs ).')
    A0 = ante_of(S['zd2sq'])[0]
    c = Ctx(w, A0)
    nn_, sr, sh, s1, tr, t1 = [c.g(x) for x in ('N e. NN', 'S e. RR', '( 1 / 2 ) <_ S', 'S <_ 1', 'T e. RR', '1 <_ T')]
    s0 = lin8(w, A0, [sh], '0 < S', {'S': sr})
    f = nc_re(w, A0, c, nn_, sr, s0, s1, tr)
    HALF = '( 1 / 2 )'
    fh = nc_re(w, A0, c, nn_, numst(w, A0, HALF, 'RR'), numst(w, A0, HALF, 'gt0'), lin8(w, A0, [], '%s <_ 1' % HALF, {}), tr, s_=HALF)
    # termwise monotonicity
    Ax = '( %s /\\ x e. %s )' % (A0, DBN)
    cx = Ctx(w, Ax)
    L = lambda st: lift(w, st, Ax)
    xb = cx([], 'simpr', 'x e. %s' % DBN)
    nx = cx([L(nn_), xb], 'jca', '( N e. NN /\\ x e. %s )' % DBN)
    h2 = e_h2(w, Ax, nx, Nv='N', Xv='x')
    MO = tsub(stmt('zcmono'), {'F': EXX('x'), 'A': HALF, 'B': 'S'})
    moa, moc = ante_of(MO)
    mo = cx([cx([h2, cx([cx([numst(w, Ax, HALF, 'RR'), numst(w, Ax, HALF, 'gt0'), lin8(w, Ax, [], '%s <_ 1' % HALF, {})], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (HALF, HALF, HALF)), cx([L(sr), L(sh)], 'jca', '( S e. RR /\\ %s <_ S )' % HALF), L(tr)], '3jca', top_and(moa)[1])], 'jca', moa), w.inst('zcmono')], 'syl', moc)
    zrS, _ = zcx_re(w, Ax, cx, L(nn_), L(sr), L(s0), L(s1), L(tr), 'x', xb)
    zrH, _ = zcx_re(w, Ax, cx, L(nn_), numst(w, Ax, HALF, 'RR'), numst(w, Ax, HALF, 'gt0'), lin8(w, Ax, [], '%s <_ 1' % HALF, {}), L(tr), 'x', xb, s_=HALF)
    le1 = c([f['dbf'], zrS, zrH, mo], 'fsumle', '%s <_ %s' % (NCn, NC('N', HALF, 'T')))
    ZS = tsub(stmt('zc1sum'), {})
    zsa, zsc = ante_of(ZS)
    zs = c([c([nn_, c([tr, t1], 'jca', '( T e. RR /\\ 1 <_ T )')], 'jca', zsa), w.inst('zc1sum')], 'syl', zsc)
    assert zsc.startswith(NC('N', HALF, 'T') + ' <_ '), zsc[:200]
    SA = tsub(stmt('zdsqabs'), {})
    saa, sac = ante_of(SA)
    sa = c([c([nn_, c([tr, t1], 'jca', '( T e. RR /\\ 1 <_ T )')], 'jca', saa), w.inst('zdsqabs')], 'syl', sac)
    nr = c([nn_], 'nnred', 'N e. RR')
    dr = c([nr, c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')], 'remulcld', '%s e. RR' % DSC)
    d2 = c([dr], 'resqcld', '( %s ^ 2 ) e. RR' % DSC)
    ldr = c([c([dr, lin8(w, A0, [c([nn_], 'nnge1d', '1 <_ N'), t1], '0 < %s' % DSC, {'N': nr, 'T': tr}, products=True)], 'elrpd', '%s e. RR+' % DSC)], 'relogcld', '%s e. RR' % LD)
    lv = {'T': tr, 'N': nr, LD: ldr, '( %s ^ 2 )' % DSC: d2}
    sc = lin.linarith(w, A0, [sa], '( %s x. ( ( T x. N ) x. %s ) ) <_ ( %s x. ( %s ^ 2 ) )' % (N6400, LD, N6400, DSC), leaves=lv, products=True, atoms=list(lv))
    m = c([numst(w, A0, N6400, 'RR'), c([c([tr, nr], 'remulcld', '( T x. N ) e. RR'), ldr], 'remulcld', '( ( T x. N ) x. %s ) e. RR' % LD)], 'remulcld', '( %s x. ( ( T x. N ) x. %s ) ) e. RR' % (N6400, LD))
    k1 = c([f['ncr'], fh['ncr'], m, le1, zs], 'letrd', '%s <_ ( %s x. ( ( T x. N ) x. %s ) )' % (NCn, N6400, LD))
    w.qed([f['ncr'], m, c([numst(w, A0, N6400, 'RR'), d2], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (N6400, DSC)), k1, sc], 'letrd', S['zd2sq'])
    return go(w)


def gen_pt():
    w = W('zd2pt', 'Theorem A at a point (Lean ` logfree_of_logged_of_mertens ` , the three ranges): from Theorem M and Theorem Z at the point (` 99 / 100 <_ S ` , ` D_0 <_ D ` ), the I6 absorption ( ~ zd2sq , ` D < D_0 ` ) and Theorem H ( ~ zdthmh , ` S < 99 / 100 ` ): ` sum_chi N ( S , T , chi ) <_ gamma_2 ( N T ^ c_0 ) ^ ( ( 9 / 2 ) ( 1 - S ) ) ` .')
    A0 = ante_of(S['zd2pt'])[0]
    c = Ctx(w, A0)
    hr, h1, wr, w0, w72, cr, c1, c54, kn, gr, g0, er, e1, zr, z1 = [c.g(x) for x in (
        'H e. RR', '1 <_ H', 'W e. RR', '0 <_ W', 'W <_ ( 7 / 2 )', 'C e. RR', '1 <_ C', 'C <_ ( 5 / 4 )', 'K e. NN0', 'G e. RR', '0 <_ G', 'E e. RR', '1 <_ E', 'Z e. RR', '1 <_ Z')]
    nn_, tr, t2, sr, s910, s1 = [c.g(x) for x in ('N e. NN', 'T e. RR', '2 <_ T', 'S e. RR', '%s <_ S' % F910, 'S <_ 1')]
    hm, hz, hh = c.g(HM), c.g(HZ), c.g(HH)
    s0 = lin8(w, A0, [s910], '0 < S', {'S': sr})
    # the sums' closures under PTH alone (the hypotheses HM, HZ, HH bind x q r)
    cP = Ctx(w, PTH)
    nnP, trP, srP, s910P, s1P = [cP.g(x) for x in ('N e. NN', 'T e. RR', 'S e. RR', '%s <_ S' % F910, 'S <_ 1')]
    fP = nc_re(w, PTH, cP, nnP, srP, lin8(w, PTH, [s910P], '0 < S', {'S': srP}), s1P, trP)
    f = {k_: lift(w, v_, A0) for k_, v_ in fP.items() if k_ not in ('Ax', 'zr')}
    nr = c([nn_], 'nnred', 'N e. RR'); n1 = c([nn_], 'nnge1d', '1 <_ N')
    t0 = lin8(w, A0, [t2], '0 <_ T', {'T': tr})
    dr = c([nr, c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')], 'remulcld', '%s e. RR' % DSC)
    d0 = lin8(w, A0, [n1, t2], '0 < %s' % DSC, {'N': nr, 'T': tr}, products=True)
    drp = c([dr, d0], 'elrpd', '%s e. RR+' % DSC)
    # E = N T ^ C and its powers
    ee2 = c([c([nn_, c([tr, t2], 'jca', '( T e. RR /\\ 2 <_ T )'), c([cr, c1], 'jca', '( C e. RR /\\ 1 <_ C )')], '3jca', '( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) )'), w.inst('zdscale2')], 'syl', '2 <_ %s' % EE)
    dle = c([c([nn_, c([tr, t2], 'jca', '( T e. RR /\\ 2 <_ T )'), c([cr, c1], 'jca', '( C e. RR /\\ 1 <_ C )')], '3jca', '( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) )'), w.inst('zdscale')], 'syl', '%s <_ ( 2 x. %s )' % (DSC, EE))
    eer = c([nr, c([c([c([tr, lin8(w, A0, [t2], '0 < T', {'T': tr})], 'elrpd', 'T e. RR+'), cr], 'rpcxpcld', '( T ^c C ) e. RR+')], 'rpred', '( T ^c C ) e. RR')], 'remulcld', '%s e. RR' % EE)
    ee1 = lin8(w, A0, [ee2], '1 <_ %s' % EE, {EE: eer})
    eep = c([eer, lin8(w, A0, [ee2], '0 < %s' % EE, {EE: eer})], 'elrpd', '%s e. RR+' % EE)
    E9 = '( %s x. ( 1 - S ) )' % F92; E5 = '( %s x. ( 1 - S ) )' % F52
    e9r = c([numst(w, A0, F92, 'RR'), c([numst(w, A0, '1', 'RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '%s e. RR' % E9)
    e5r = c([numst(w, A0, F52, 'RR'), c([numst(w, A0, '1', 'RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '%s e. RR' % E5)
    e90 = lin8(w, A0, [s1], '0 <_ %s' % E9, {'S': sr}); e50 = lin8(w, A0, [s1], '0 <_ %s' % E5, {'S': sr})
    epr = c([c([eep, e9r], 'rpcxpcld', '%s e. RR+' % EPOW)], 'rpred', '%s e. RR' % EPOW)
    ep0 = c([c([eep, e9r], 'rpcxpcld', '%s e. RR+' % EPOW)], 'rpge0d', '0 <_ %s' % EPOW)
    ep1 = c([eer, ee1, e9r, e90], 'a5ge1cxp', '1 <_ %s' % EPOW)
    # GAM2
    PK = '( ( %s x. ( K + 1 ) ) ^ K )' % N400
    pkr = c([c([numst(w, A0, N400, 'RR'), c([c([kn], 'nn0red', 'K e. RR'), numst(w, A0, '1', 'RR')], 'readdcld', '( K + 1 ) e. RR')], 'remulcld', '( %s x. ( K + 1 ) ) e. RR' % N400), kn], 'reexpcld', '%s e. RR' % PK)
    pk0 = c([c([numst(w, A0, N400, 'RR'), c([c([kn], 'nn0red', 'K e. RR'), numst(w, A0, '1', 'RR')], 'readdcld', '( K + 1 ) e. RR')], 'remulcld', '( %s x. ( K + 1 ) ) e. RR' % N400), kn,
             lin8(w, A0, [c([kn], 'nn0ge0d', '0 <_ K')], '0 <_ ( %s x. ( K + 1 ) )' % N400, {'K': c([kn], 'nn0red', 'K e. RR')})], 'expge0d', '0 <_ %s' % PK)
    HPK = '( H x. %s )' % PK
    hpkr = c([hr, pkr], 'remulcld', '%s e. RR' % HPK); hpk0 = c([hr, pkr, lin8(w, A0, [h1], '0 <_ H', {'H': hr}), pk0], 'mulge0d', '0 <_ %s' % HPK)
    E2 = '( E ^ 2 )'
    e2r = c([er], 'resqcld', '%s e. RR' % E2); e20 = c([er], 'sqge0d', '0 <_ %s' % E2)
    gam2r = c([c([c([numst(w, A0, '2', 'RR'), c([gr, zr], 'readdcld', '( G + Z ) e. RR')], 'remulcld', '( 2 x. ( G + Z ) ) e. RR'), c([numst(w, A0, N6400, 'RR'), e2r], 'remulcld', '( %s x. %s ) e. RR' % (N6400, E2))], 'readdcld', '( ( 2 x. ( G + Z ) ) + ( %s x. %s ) ) e. RR' % (N6400, E2)),
               c([hpkr, numst(w, A0, '1', 'RR')], 'readdcld', '( %s + 1 ) e. RR' % HPK)], 'readdcld', '%s e. RR' % GAM2)
    lvc = {'G': gr, 'Z': zr, E2: e2r, HPK: hpkr, EPOW: epr}
    gam20 = lin8(w, A0, [g0, z1, e20, hpk0], '0 <_ %s' % GAM2, lvc)
    GOAL = '%s <_ ( %s x. %s )' % (NCn, GAM2, EPOW)
    gepr = c([gam2r, epr], 'remulcld', '( %s x. %s ) e. RR' % (GAM2, EPOW))
    ge1 = c([c([c([gam2r], 'recnd', '%s e. CC' % GAM2)], 'mulridd', '( %s x. 1 ) = %s' % (GAM2, GAM2)), c([numst(w, A0, '1', 'RR'), epr, gam2r, gam20, ep1], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (GAM2, GAM2, EPOW))], 'eqbrtrrd', '%s <_ ( %s x. %s )' % (GAM2, GAM2, EPOW))
    # the split
    SP = ante_of(S['zd2split'])
    sp = c([c([nn_, c([c([sr, s0, s1], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), tr], 'jca', '( ( S e. RR /\\ 0 < S /\\ S <_ 1 ) /\\ T e. RR )')], 'jca', SP[0]), w.inst('zd2split')], 'syl', SP[1])
    # ---- case 1: 99/100 <_ S
    A1 = '( %s /\\ %s <_ S )' % (A0, F99)
    c1_ = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    s99 = c1_([], 'simpr', '%s <_ S' % F99)
    ptz = c1_([L1(t2), c1_([s99, L1(s1)], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', PTZ)
    hz1 = c1_([ptz, L1(hz)], 'mpd', '%s <_ ( Z x. %s )' % (ZC0n, TPOW))
    tpr = c1_([c1_([L1(c([c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A0, [t2], '0 < ( T + 2 )', {'T': tr})], 'elrpd', '( T + 2 ) e. RR+')), L1(e5r)], 'rpcxpcld', '%s e. RR+' % TPOW)], 'rpred', '%s e. RR' % TPOW)
    dpr = c1_([c1_([L1(drp), L1(e5r)], 'rpcxpcld', '%s e. RR+' % DPOW)], 'rpred', '%s e. RR' % DPOW)
    dp0 = c1_([c1_([L1(drp), L1(e5r)], 'rpcxpcld', '%s e. RR+' % DPOW)], 'rpge0d', '0 <_ %s' % DPOW)
    t2d = lin8(w, A1, [L1(n1), L1(t2)], '( T + 2 ) <_ %s' % DSC, {'N': L1(nr), 'T': L1(tr)}, products=True)
    tpd = c1_([L1(c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')), lin8(w, A1, [L1(t2)], '0 <_ ( T + 2 )', {'T': L1(tr)}), L1(dr), L1(e5r), L1(e50), t2d], 'cxple2ad', '%s <_ %s' % (TPOW, DPOW))
    D2E = tsub(stmt('zdd2e'), {'D': DSC, 'E': EE})
    d2a, d2c = ante_of(D2E)
    d2e = c1_([c1_([c1_([L1(drp), L1(eer)], 'jca', '( %s e. RR+ /\\ %s e. RR )' % (DSC, EE)), c1_([c1_([L1(ee1), L1(dle)], 'jca', '( 1 <_ %s /\\ %s <_ ( 2 x. %s ) )' % (EE, DSC, EE)), c1_([L1(sr), c1_([s99, L1(s1)], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS)], 'jca', top_and(d2a)[1])], 'jca', d2a), w.inst('zdd2e')], 'syl', d2c)
    assert d2c == '%s <_ ( 2 x. %s )' % (DPOW, EPOW), d2c
    # case 1a: E <_ DSC
    A1a = '( %s /\\ E <_ %s )' % (A1, DSC)
    ca = Ctx(w, A1a)
    La = lambda st: lift(w, st, A1a)
    hm1 = ca([ca([La(ptz), ca([], 'simpr', 'E <_ %s' % DSC)], 'jca', '( %s /\\ E <_ %s )' % (PTZ, DSC)), La(hm)], 'mpd', '%s <_ ( G x. %s )' % (NCNPn, DPOW))
    lva = {NCn: La(f['ncr']), ZC0n: La(f['zc0r']), NCNPn: La(f['npr']), TPOW: La(tpr), DPOW: La(dpr), EPOW: La(epr), 'G': La(gr), 'Z': La(zr), E2: La(e2r), HPK: La(hpkr)}
    case1a = lin.linarith(w, A1a, [La(sp), hm1, La(hz1), La(tpd), La(d2e), La(g0), La(z1), La(e20), La(hpk0), La(dp0), La(ep0)], GOAL, leaves=lva, products=True, atoms=list(lva))
    # case 1b: DSC < E
    A1b = '( %s /\\ %s < E )' % (A1, DSC)
    cb = Ctx(w, A1b)
    Lb = lambda st: lift(w, st, A1b)
    SQ = ante_of(S['zd2sq'])
    sq = cb([cb([Lb(nn_), cb([cb([Lb(sr), lin8(w, A1b, [Lb(s99)], '( 1 / 2 ) <_ S', {'S': Lb(sr)}), Lb(s1)], '3jca', '( S e. RR /\\ ( 1 / 2 ) <_ S /\\ S <_ 1 )'), cb([Lb(tr), lin8(w, A1b, [Lb(t2)], '1 <_ T', {'T': Lb(tr)})], 'jca', '( T e. RR /\\ 1 <_ T )')], 'jca', '( ( S e. RR /\\ ( 1 / 2 ) <_ S /\\ S <_ 1 ) /\\ ( T e. RR /\\ 1 <_ T ) )')], 'jca', SP[0] if False else SQ[0]), w.inst('zd2sq')], 'syl', SQ[1])
    dsq = cb([cb([cb([Lb(dr), lin8(w, A1b, [Lb(d0)], '0 <_ %s' % DSC, {DSC: Lb(dr)})], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (DSC, DSC)), cb([Lb(er), cb([], 'simpr', '%s < E' % DSC)], 'x', 'x') if False else cb([Lb(er), cb([cb([], 'simpr', '%s < E' % DSC)], 'ltled', '%s <_ E' % DSC)], 'jca', '( E e. RR /\\ %s <_ E )' % DSC)], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( E e. RR /\\ %s <_ E ) )' % (DSC, DSC, DSC)), w.inst('le2sq2')], 'syl', '( %s ^ 2 ) <_ %s' % (DSC, E2))
    lvb = {NCn: Lb(f['ncr']), '( %s ^ 2 )' % DSC: Lb(c([dr], 'resqcld', '( %s ^ 2 ) e. RR' % DSC)), E2: Lb(e2r), 'G': Lb(gr), 'Z': Lb(zr), HPK: Lb(hpkr), '( %s x. %s )' % (GAM2, EPOW): Lb(gepr)}
    case1b = lin.linarith(w, A1b, [sq, dsq, Lb(g0), Lb(z1), Lb(hpk0), Lb(ge1)], GOAL, leaves=lvb, products=True, atoms=list(lvb))
    tri1 = c1_([L1(er), L1(dr), w.inst('lelttric')], 'syl2anc', '( E <_ %s \\/ %s < E )' % (DSC, DSC))
    case1 = c1_([case1a, case1b, tri1], 'mpjaodan', GOAL)
    # ---- case 2: S < 99/100: Theorem H
    A2 = '( %s /\\ S < %s )' % (A0, F99)
    c2 = Ctx(w, A2)
    L2 = lambda st: lift(w, st, A2)
    s99b = c2([c2([], 'simpr', 'S < %s' % F99)], 'ltled', 'S <_ %s' % F99)
    hh2 = c2([c2([L2(t2), lin8(w, A2, [L2(s910)], '%s <_ S' % F3950, {'S': L2(sr)}), L2(s1)], '3jca', '( 2 <_ T /\\ %s <_ S /\\ S <_ 1 )' % F3950), L2(hh)], 'mpd', HH.split(' -> ', 1)[1][:-2])
    TH = tsub(stmt('zdthmh'), {'P': 'W', 'Z': NCn})
    tha, thc = ante_of(TH)
    th = c2([c2([c2([c2([L2(nn_), c2([L2(tr), L2(t2)], 'jca', '( T e. RR /\\ 2 <_ T )'), c2([L2(cr), L2(c1)], 'jca', '( C e. RR /\\ 1 <_ C )')], '3jca', '( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) )'),
                         c2([c2([L2(wr), L2(w72)], 'jca', '( W e. RR /\\ W <_ ( 7 / 2 ) )'), c2([L2(sr), c2([L2(s910), s99b], 'jca', '( %s <_ S /\\ S <_ %s )' % (F910, F99))], 'jca', '( S e. RR /\\ ( %s <_ S /\\ S <_ %s ) )' % (F910, F99))], 'jca', '( ( W e. RR /\\ W <_ ( 7 / 2 ) ) /\\ ( S e. RR /\\ ( %s <_ S /\\ S <_ %s ) ) )' % (F910, F99))], 'jca', top_and(tha)[0]),
                     c2([c2([L2(kn), c2([L2(hr), lin8(w, A2, [L2(h1)], '0 <_ H', {'H': L2(hr)})], 'jca', '( H e. RR /\\ 0 <_ H )')], 'jca', '( K e. NN0 /\\ ( H e. RR /\\ 0 <_ H ) )'), c2([L2(f['ncr']), hh2], 'jca', '( %s e. RR /\\ %s )' % (NCn, strip_ante(formula_of(w, hh2), A2)))], 'jca', top_and(tha)[1])], 'jca', tha), w.inst('zdthmh')], 'syl', thc)
    assert thc == '%s <_ ( %s x. %s )' % (NCn, HPK, EPOW), thc
    lv2 = {NCn: L2(f['ncr']), HPK: L2(hpkr), EPOW: L2(epr), 'G': L2(gr), 'Z': L2(zr), E2: L2(e2r)}
    case2 = lin.linarith(w, A2, [th, L2(g0), L2(z1), L2(e20), L2(ep0)], GOAL, leaves=lv2, products=True, atoms=list(lv2))
    tri = c([numst(w, A0, F99, 'RR'), sr, w.inst('lelttric')], 'syl2anc', '( %s <_ S \\/ S < %s )' % (F99, F99))
    w.qed([case1, case2, tri], 'mpjaodan', S['zd2pt'])
    return go(w)


GENS = {'zd2split': gen_split, 'zd2sq': gen_sq, 'zd2pt': gen_pt}

if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
