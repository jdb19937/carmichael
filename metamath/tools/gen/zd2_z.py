"""Sortie ZD2: Theorem Z (Lean zeroCountBox_one_le_density_of_mertens, zeroCountBox_trivChar_le_density):
zd2zsm, zd2zbe, zd2zbc, zd2zbg, zd2zpt, zd2tzpt, zd2tz1, zd2tz."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zd2_base import *
from zc1_m import e_h2
from zd2_thm import cjk_facts, cmx_facts

X01 = '( 0g ` ( DChr ` 1 ) )'
DB1 = '( Base ` ( DChr ` 1 ) )'
G1_ = '( DChr ` 1 )'
D1 = '( 1 x. ( T + 2 ) )'
L1 = ZL.L1
LAM1 = '( ( 1 - S ) x. %s )' % L1
LAMG1 = ZL.LAMG1
C6 = '( log ` ( ( %s x. ( exp ` 1 ) ) x. ; 6 0 ) )' % N3200
HALF = '( 1 / 2 )'
ZF1 = lambda s, t: ZF(E1, s, t)
ORD1 = lambda q='q': '( %s holord %s )' % (E1, q)
GLAM1 = tsub(GLAM, {'N': '1'})
GAMK1 = tsub(GAMK, {'N': '1'})


def e1_facts(w, A, c):
    """( A -> ( 1 e. NN /\\ X01 e. DB1 ) ), ( A -> H2(E1) ) (holomorphy on HP0 and E1(2) =/= 0)"""
    g = w.s([], 'eqid', '%s = %s' % (G1_, G1_)); b = w.s([], 'eqid', '%s = %s' % (DB1, DB1)); o = w.s([], 'eqid', '%s = %s' % (X01, X01))
    one = c.a1(w.s([], '1nn', '1 e. NN'), '1 e. NN')
    abl = c([one, w.s([g], 'dchrabl', '( 1 e. NN -> %s e. Abel )' % G1_)], 'syl', '%s e. Abel' % G1_)
    grp = c([abl, w.inst('ablgrp')], 'syl', '%s e. Grp' % G1_)
    x0 = c([grp, w.s([b, o], 'grpidcl', '( %s e. Grp -> %s e. %s )' % (G1_, X01, DB1))], 'syl', '%s e. %s' % (X01, DB1))
    nx = c([one, x0], 'jca', '( 1 e. NN /\\ %s e. %s )' % (X01, DB1))
    h2 = e_h2(w, A, nx, Nv='1', Xv=X01)
    return nx, h2


def zf1_facts(w, A, c, nx, s_, sr, s0, s1, tr, t_='T'):
    """ezf at E1: ( A -> ZF1(s_, t_) e. Fin ), ( A -> A. q e. ZF1 ORD1 e. NN )"""
    EZ = tsub(stmt('ezf'), {'N': '1', 'X': X01, 'A': s_, 'T': t_})
    eza, ezc = ante_of(EZ)
    ez = c([c([nx, c([c([sr, s0, s1], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (s_, s_, s_)), tr], 'jca', '( ( %s e. RR /\\ 0 < %s /\\ %s <_ 1 ) /\\ %s e. RR )' % (s_, s_, s_, t_))], 'jca', eza), w.inst('ezf')], 'syl', ezc)
    return c([ez], 'simpld', '%s e. Fin' % ZF1(s_, t_)), c([ez], 'simprd', 'A. q e. %s %s e. NN' % (ZF1(s_, t_), ORD1()))


def ord_facts(w, Aq, cq, alln, qin, Z):
    """under Aq with qin : q e. Z and alln lifted: ORD1 e. NN, e. RR, 0 <_"""
    on = cq([alln, qin, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (Z, ORD1(), Z, ORD1()))], 'sylc', '%s e. NN' % ORD1())
    return on, cq([on], 'nnred', '%s e. RR' % ORD1()), cq([cq([on], 'nnrpd', '%s e. RR+' % ORD1())], 'rpge0d', '0 <_ %s' % ORD1())


def zfel(w, A, c, s_, sr, tr, V, vin):
    """the box facts of V e. ZF1(s_, T): dict cc, re1 (s_ <_ Re), re2, im (abs Im <_ T), ne1, zero, rer, imr, absr"""
    ZE = tsub(stmt('t21zfel'), {'F': E1, 'A': s_, 'Q': V})
    zea, zec = ante_of(ZE)
    ze = c([c([sr, tr], 'jca', zea), w.inst('t21zfel')], 'syl', zec)
    both = c([vin, ze], 'mpbid', zec.split(' <-> ', 1)[1][:-2])
    P = top_and(zec.split(' <-> ', 1)[1][:-2])
    cc = c([both], 'simp1d', P[0]); mid = c([both], 'simp2d', P[1]); last = c([both], 'simp3d', P[2])
    re = c([mid], 'simpld', top_and(P[1])[0]); im = c([mid], 'simprd', top_and(P[1])[1])
    re1 = c([re], 'simpld', '%s <_ ( Re ` %s )' % (s_, V)); re2 = c([re], 'simprd', '( Re ` %s ) <_ 1' % V)
    ne1 = c([last], 'simpld', '%s =/= 1' % V); zero = c([last], 'simprd', '( %s ` %s ) = 0' % (E1, V))
    rer = c([cc], 'recld', '( Re ` %s ) e. RR' % V); imr = c([cc], 'imcld', '( Im ` %s ) e. RR' % V)
    absr = c([c([imr], 'recnd', '( Im ` %s ) e. CC' % V)], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % V)
    abs0 = c([c([imr], 'recnd', '( Im ` %s ) e. CC' % V)], 'absge0d', '0 <_ ( abs ` ( Im ` %s ) )' % V)
    return dict(cc=cc, re1=re1, re2=re2, im=im, ne1=ne1, zero=zero, rer=rer, imr=imr, absr=absr, abs0=abs0, all=both, ze=ze)


def l1_facts(w, A, c, tr, t2):
    """D1 e. RR+, D1 = ( T + 2 ), L1 e. RR, L1 = log ( T + 2 )"""
    t2r = c([tr, numst(w, A, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')
    t2p = c([t2r, lin8(w, A, [t2], '0 < ( T + 2 )', {'T': tr})], 'elrpd', '( T + 2 ) e. RR+')
    d1e = c([c([t2r], 'recnd', '( T + 2 ) e. CC')], 'mullidd', '%s = ( T + 2 )' % D1)
    d1p = c([d1e, t2p], 'eqeltrd', '%s e. RR+' % D1)
    l1r = c([d1p], 'relogcld', '%s e. RR' % L1)
    l1e = c([d1e], 'fveq2d', '%s = ( log ` ( T + 2 ) )' % L1)
    return dict(t2r=t2r, t2p=t2p, d1e=d1e, d1p=d1p, l1r=l1r, l1e=l1e)


def gen_zsm():
    w = W('zd2zsm', 'Theorem Z, the small heights (Lean ` zeroCountBox_one_le_density_of_mertens ` , case ` t + 2 <_ nu_0 ` ): ` N_zeta ( S , T ) <_ 6400 V log ( V + 2 ) ` for ` T + 2 <_ V ` ( ~ zcmono , ~ zc1one ).')
    A0 = ante_of(S['zd2zsm'])[0]
    c = Ctx(w, A0)
    tr, t2, sr, s99, s1, vr, tv = [c.g(x) for x in ('T e. RR', '2 <_ T', 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'V e. RR', '( T + 2 ) <_ V')]
    nx, h2 = e1_facts(w, A0, c)
    hr = numst(w, A0, HALF, 'RR')
    MO = tsub(stmt('zcmono'), {'F': E1, 'A': HALF, 'B': 'S'})
    moa, moc = ante_of(MO)
    mo = c([c([h2, c([c([hr, numst(w, A0, HALF, 'gt0'), lin8(w, A0, [], '%s <_ 1' % HALF, {})], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 1 )' % (HALF, HALF, HALF)),
                        c([sr, lin8(w, A0, [s99], '%s <_ S' % HALF, {'S': sr})], 'jca', '( S e. RR /\\ %s <_ S )' % HALF), tr], '3jca', top_and(moa)[1])], 'jca', moa), w.inst('zcmono')], 'syl', moc)
    t1 = lin8(w, A0, [t2], '1 <_ T', {'T': tr})
    one = c([c([tr, t1], 'jca', '( T e. RR /\\ 1 <_ T )'), w.inst('zc1one')], 'syl', ante_of(stmt('zc1one'))[1])
    LT, LV = '( log ` ( T + 2 ) )', '( log ` ( V + 2 ) )'
    t2p = c([c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A0, [t2], '0 < ( T + 2 )', {'T': tr})], 'elrpd', '( T + 2 ) e. RR+')
    v2p = c([c([vr, numst(w, A0, '2', 'RR')], 'readdcld', '( V + 2 ) e. RR'), lin8(w, A0, [tv, t2], '0 < ( V + 2 )', {'T': tr, 'V': vr})], 'elrpd', '( V + 2 ) e. RR+')
    ltr = c([t2p], 'relogcld', '%s e. RR' % LT); lvr = c([v2p], 'relogcld', '%s e. RR' % LV)
    lt0 = c([c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A0, [t2], '1 <_ ( T + 2 )', {'T': tr}), w.inst('logge0')], 'syl2anc', '0 <_ %s' % LT)
    lle = c([lin8(w, A0, [tv], '( T + 2 ) <_ ( V + 2 )', {'T': tr, 'V': vr}), c([t2p, v2p], 'logled', '( ( T + 2 ) <_ ( V + 2 ) <-> %s <_ %s )' % (LT, LV))], 'mpbid', '%s <_ %s' % (LT, LV))
    m = c([tr, vr, ltr, lvr, lin8(w, A0, [t2], '0 <_ T', {'T': tr}), lt0, lin8(w, A0, [tv], 'T <_ V', {'T': tr, 'V': vr}), lle], 'lemul12ad', '( T x. %s ) <_ ( V x. %s )' % (LT, LV))
    m2 = c([c([tr, ltr], 'remulcld', '( T x. %s ) e. RR' % LT), c([vr, lvr], 'remulcld', '( V x. %s ) e. RR' % LV), numst(w, A0, N6400, 'RR'), numst(w, A0, N6400, 'ge0'), m], 'lemul2ad', '( %s x. ( T x. %s ) ) <_ ( %s x. ( V x. %s ) )' % (N6400, LT, N6400, LV))
    fin_, alln = zf1_facts(w, A0, c, nx, 'S', sr, lin8(w, A0, [s99], '0 < S', {'S': sr}), s1, tr)
    Aq = '( %s /\\ q e. %s )' % (A0, ZF1('S', 'T'))
    cq = Ctx(w, Aq)
    _, ordr, _ = ord_facts(w, Aq, cq, lift(w, alln, Aq), cq([], 'simpr', 'q e. %s' % ZF1('S', 'T')), ZF1('S', 'T'))
    zr = c([fin_, ordr], 'fsumrecl', '%s e. RR' % ZC1_('S', 'T'))
    finh, allh = zf1_facts(w, A0, c, nx, HALF, hr, numst(w, A0, HALF, 'gt0'), lin8(w, A0, [], '%s <_ 1' % HALF, {}), tr)
    Aqh = '( %s /\\ q e. %s )' % (A0, ZF1(HALF, 'T'))
    cqh = Ctx(w, Aqh)
    _, ordrh, _ = ord_facts(w, Aqh, cqh, lift(w, allh, Aqh), cqh([], 'simpr', 'q e. %s' % ZF1(HALF, 'T')), ZF1(HALF, 'T'))
    zrh = c([finh, ordrh], 'fsumrecl', '%s e. RR' % ZC1_(HALF, 'T'))
    k1 = c([zr, zrh, c([numst(w, A0, N6400, 'RR'), c([tr, ltr], 'remulcld', '( T x. %s ) e. RR' % LT)], 'remulcld', '( %s x. ( T x. %s ) ) e. RR' % (N6400, LT)), mo, one], 'letrd', '%s <_ ( %s x. ( T x. %s ) )' % (ZC1_('S', 'T'), N6400, LT))
    w.qed([zr, c([numst(w, A0, N6400, 'RR'), c([tr, ltr], 'remulcld', '( T x. %s ) e. RR' % LT)], 'remulcld', '( %s x. ( T x. %s ) ) e. RR' % (N6400, LT)), c([numst(w, A0, N6400, 'RR'), c([vr, lvr], 'remulcld', '( V x. %s ) e. RR' % LV)], 'remulcld', '( %s x. ( V x. %s ) ) e. RR' % (N6400, LV)), k1, m2], 'letrd', S['zd2zsm'])
    return go(w)


def zph_facts(w, A, c):
    """the leaves of ZPH under A"""
    d = {}
    for k_, x in (('tr', 'T e. RR'), ('t2', '2 <_ T'), ('sr', 'S e. RR'), ('s99', '%s <_ S' % F99), ('s1', 'S <_ 1'), ('cr', 'c e. RR'), ('c0', '0 < c'), ('l200', '; ; 2 0 0 <_ %s' % L1),
                   ('b1', '( log ` %s ) <_ ( %s / 4 )' % (L1, L1)), ('b2', '( ( log ` %s ) ^ 2 ) <_ ( ( c ^ 2 ) x. %s )' % (L1, L1)), ('b3', '( %s + 3 ) <_ ( %s / 2 )' % (C6, L1))):
        d[k_] = c.g(x)
    d.update(l1_facts(w, A, c, d['tr'], d['t2']))
    d['s0'] = lin8(w, A, [d['s99']], '0 < S', {'S': d['sr']})
    d['l1p'] = c([d['l1r'], lin8(w, A, [d['l200']], '0 < %s' % L1, {L1: d['l1r']})], 'elrpd', '%s e. RR+' % L1)
    d['ss'] = c([d['sr'], c([d['s99'], d['s1']], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS)
    d['crp'] = c([d['cr'], d['c0']], 'elrpd', 'c e. RR+')
    d['c6r'] = c([c([c([numst(w, A, N3200, 'RR+'), c([numst(w, A, '1', 'RR')], 'rpefcld', '( exp ` 1 ) e. RR+')], 'rpmulcld', '( %s x. ( exp ` 1 ) ) e. RR+' % N3200), numst(w, A, '; 6 0', 'RR+')], 'rpmulcld', '( ( %s x. ( exp ` 1 ) ) x. ; 6 0 ) e. RR+' % N3200)], 'relogcld', '%s e. RR' % C6)
    d['ll1'] = c([c([d['l1r'], lin8(w, A, [d['l200']], '1 < %s' % L1, {L1: d['l1r']})], 'rplogcld', '( log ` %s ) e. RR+' % L1)], 'rpred', '( log ` %s ) e. RR' % L1)
    d['ll1p'] = c([d['l1r'], lin8(w, A, [d['l200']], '1 < %s' % L1, {L1: d['l1r']})], 'rplogcld', '( log ` %s ) e. RR+' % L1)
    d['lamr'] = c([c([numst(w, A, '1', 'RR'), d['sr']], 'resubcld', '( 1 - S ) e. RR'), d['l1r']], 'remulcld', '%s e. RR' % LAM1)
    d['lamgr'] = c([c([d['ll1'], c([numst(w, A, '( 6 / 5 )', 'RR'), d['lamr']], 'remulcld', '( ( 6 / 5 ) x. %s ) e. RR' % LAM1)], 'readdcld', '( ( log ` %s ) + ( ( 6 / 5 ) x. %s ) ) e. RR' % (L1, LAM1)), d['c6r']], 'readdcld', '%s e. RR' % LAMG1)
    return d


def gen_zbe():
    w = W('zd2zbe', 'Theorem Z, band (b) empty (Lean ` zeroCountBox_one_le_density_of_mertens ` , case ` lambda ^ 2 <_ L ` ): the zero-free region ~ zrzf excludes every zero with ` abs Im < Lambda_0 ` , so the band sum vanishes ( ~ zdzc1 ).')
    A0 = ante_of(S['zd2zbe'])[0]
    c = Ctx(w, A0)
    d = zph_facts(w, A0, c)
    zfree, lamsq = c.g(ZFREE), c.g('( %s ^ 2 ) <_ %s' % (LAM1, L1))
    Z1 = tsub(stmt('zdzc1'), {'L': L1, 'A': 'c', 'C': C6})
    z1a, z1c = ante_of(Z1)
    z1 = c([c([c([c([d['l1r'], d['l200']], 'jca', '( %s e. RR /\\ ; ; 2 0 0 <_ %s )' % (L1, L1)), d['ss']], 'jca', top_and(z1a)[0]),
             c([c([d['crp'], d['c6r']], 'jca', '( c e. RR+ /\\ %s e. RR )' % C6), c([c([d['b1'], d['b2'], d['b3']], '3jca', '( %s /\\ %s /\\ %s )' % tuple(strip_ante(formula_of(w, d[k_]), A0) for k_ in ('b1', 'b2', 'b3'))), lamsq], 'jca',
                                                                                        '( ( %s /\\ %s /\\ %s ) /\\ ( %s ^ 2 ) <_ %s )' % (tuple(strip_ante(formula_of(w, d[k_]), A0) for k_ in ('b1', 'b2', 'b3')) + (LAM1, L1)))], 'jca', top_and(z1a)[1])], 'jca', z1a), w.inst('zdzc1')], 'syl', z1c)
    l3 = c([z1], 'simpld', '( %s + 3 ) <_ %s' % (LAMG1, L1)); sl = c([z1], 'simprd', '( ( 1 - S ) x. ( log ` %s ) ) <_ c' % L1)
    ZF_ = ZF1('S', 'T')
    Av = '( %s /\\ v e. %s )' % (A0, ZF_)
    cv = Ctx(w, Av)
    vin = cv([], 'simpr', 'v e. %s' % ZF_)
    zf = zfel(w, Av, cv, 'S', lift(w, d['sr'], Av), lift(w, d['tr'], Av), 'v', vin)
    AI = '( abs ` ( Im ` v ) )'
    Ab = '( %s /\\ %s < %s )' % (Av, AI, LAMG1)
    cb = Ctx(w, Ab)
    Lb = lambda st: lift(w, st, Ab)
    lt = cb([], 'simpr', '%s < %s' % (AI, LAMG1))
    zfr, _ = ral_at(w, Ab, Lb(zfree), 'r', 'v', '( ( %s ` r ) = 0 -> ( Re ` r ) < ( 1 - ( c / ( log ` ( ( abs ` ( Im ` r ) ) + 3 ) ) ) ) )' % E1, Lb(zf['cc']))
    rv = cb([Lb(zf['zero']), zfr], 'mpd', '( Re ` v ) < ( 1 - ( c / ( log ` ( %s + 3 ) ) ) )' % AI)
    A3 = '( %s + 3 )' % AI
    a3r = cb([Lb(zf['absr']), numst(w, Ab, '3', 'RR')], 'readdcld', '%s e. RR' % A3)
    a3p = cb([a3r, lin8(w, Ab, [Lb(zf['abs0'])], '0 < %s' % A3, {AI: Lb(zf['absr'])})], 'elrpd', '%s e. RR+' % A3)
    LI = '( log ` %s )' % A3
    lip = cb([a3r, lin8(w, Ab, [Lb(zf['abs0'])], '1 < %s' % A3, {AI: Lb(zf['absr'])})], 'rplogcld', '%s e. RR+' % LI)
    a3l = lin8(w, Ab, [lt, Lb(l3)], '%s <_ %s' % (A3, L1), {AI: Lb(zf['absr']), LAMG1: Lb(d['lamgr']), L1: Lb(d['l1r'])})
    lil = cb([a3l, cb([a3p, Lb(d['l1p'])], 'logled', '( %s <_ %s <-> %s <_ ( log ` %s ) )' % (A3, L1, LI, L1))], 'mpbid', '%s <_ ( log ` %s )' % (LI, L1))
    dv = cb([lip, Lb(d['ll1p']), Lb(d['cr']), lin8(w, Ab, [Lb(d['c0'])], '0 <_ c', {'c': Lb(d['cr'])}), lil], 'lediv2ad', '( c / ( log ` %s ) ) <_ ( c / %s )' % (L1, LI))
    ms = cb([cb([numst(w, Ab, '1', 'RR'), Lb(d['sr'])], 'resubcld', '( 1 - S ) e. RR'), Lb(d['cr']), Lb(d['ll1p'])], 'lemuldivd', '( ( ( 1 - S ) x. ( log ` %s ) ) <_ c <-> ( 1 - S ) <_ ( c / ( log ` %s ) ) )' % (L1, L1))
    s1s = cb([Lb(sl), ms], 'mpbid', '( 1 - S ) <_ ( c / ( log ` %s ) )' % L1)
    cl1 = cb([Lb(d['cr']), Lb(d['ll1']), cb([Lb(d['ll1p'])], 'rpne0d', '( log ` %s ) =/= 0' % L1)], 'redivcld', '( c / ( log ` %s ) ) e. RR' % L1)
    cli = cb([Lb(d['cr']), cb([lip], 'rpred', '%s e. RR' % LI), cb([lip], 'rpne0d', '%s =/= 0' % LI)], 'redivcld', '( c / %s ) e. RR' % LI)
    lv = {'( Re ` v )': Lb(zf['rer']), 'S': Lb(d['sr']), '( c / ( log ` %s ) )' % L1: cl1, '( c / %s )' % LI: cli}
    res = lin8(w, Ab, [rv, dv, s1s], '( Re ` v ) < S', lv)
    nlt = cb([Lb(zf['re1']), cb([Lb(d['sr']), Lb(zf['rer'])], 'lenltd', '( S <_ ( Re ` v ) <-> -. ( Re ` v ) < S )')], 'mpbid', '-. ( Re ` v ) < S')
    neg = w.s([res, nlt], 'pm2.65da', '( %s -> -. %s < %s )' % (Av, AI, LAMG1))
    ral = c([neg], 'ralrimiva', 'A. v e. %s -. %s < %s' % (ZF_, AI, LAMG1))
    ZB = ZBAND('S', 'T')
    emp = c([ral, w.s([], 'rabeq0', '( %s = (/) <-> A. v e. %s -. %s < %s )' % (ZB, ZF_, AI, LAMG1))], 'sylibr', '%s = (/)' % ZB)
    se = c([emp], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. (/) %s' % (ZB, ORD1(), ORD1()))
    w.qed([se, c.a1(w.s([], 'sum0', 'sum_ q e. (/) %s = 0' % ORD1()), 'sum_ q e. (/) %s = 0' % ORD1())], 'eqtrd', S['zd2zbe'])
    return go(w)


def gen_zbc():
    w = W('zd2zbc', 'Theorem Z, band (b) counted (Lean ` zeroCountBox_one_le_density_of_mertens ` , case ` L < lambda ^ 2 ` ): the zeros with ` abs Im < Lambda_0 ` lie in the box ` [ 1 / 2 , 1 ] x. [ - Lambda_0 , Lambda_0 ] ` , counted by ~ zc1one and absorbed by ~ zdzc2 .')
    A0 = ante_of(S['zd2zbc'])[0]
    c = Ctx(w, A0)
    d = zph_facts(w, A0, c)
    lamsq = c.g('%s < ( %s ^ 2 )' % (L1, LAM1))
    nx, h2 = e1_facts(w, A0, c)
    # 1 <_ log L1 and 0 <_ C6
    e1r = c([numst(w, A0, '1', 'RR')], 'rpefcld', '( exp ` 1 ) e. RR+')
    de = c.a1(w.s([], 'df-e', '_e = ( exp ` 1 )'), '_e = ( exp ` 1 )')
    e3 = c([de, c.a1(w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3'), '_e < 3')], 'eqbrtrrd', '( exp ` 1 ) < 3')
    e2 = c([c.a1(w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e'), '2 < _e'), de], 'breqtrd', '2 < ( exp ` 1 )')
    el = lin8(w, A0, [e3, d['l200']], '( exp ` 1 ) <_ %s' % L1, {'( exp ` 1 )': c([e1r], 'rpred', '( exp ` 1 ) e. RR'), L1: d['l1r']})
    lel = c([el, c([e1r, d['l1p']], 'logled', '( ( exp ` 1 ) <_ %s <-> ( log ` ( exp ` 1 ) ) <_ ( log ` %s ) )' % (L1, L1))], 'mpbid', '( log ` ( exp ` 1 ) ) <_ ( log ` %s )' % L1)
    l1l = c([c([numst(w, A0, '1', 'RR')], 'relogefd', '( log ` ( exp ` 1 ) ) = 1'), lel], 'eqbrtrrd', '1 <_ ( log ` %s )' % L1)
    PR = '( ( %s x. ( exp ` 1 ) ) x. ; 6 0 )' % N3200
    prr = c([c([numst(w, A0, N3200, 'RR'), c([e1r], 'rpred', '( exp ` 1 ) e. RR')], 'remulcld', '( %s x. ( exp ` 1 ) ) e. RR' % N3200), numst(w, A0, '; 6 0', 'RR')], 'remulcld', '%s e. RR' % PR)
    pr1 = lin8(w, A0, [e2], '1 <_ %s' % PR, {'( exp ` 1 )': c([e1r], 'rpred', '( exp ` 1 ) e. RR')}, products=True)
    c60 = c([prr, pr1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % C6)
    Z2 = tsub(stmt('zdzc2'), {'L': L1, 'C': C6})
    z2a, z2c = ante_of(Z2)
    z2 = c([c([c([c([d['l1r'], d['l200']], 'jca', '( %s e. RR /\\ ; ; 2 0 0 <_ %s )' % (L1, L1)), d['ss']], 'jca', top_and(z2a)[0]),
             c([c([d['c6r'], c60], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (C6, C6)), c([c([d['b1'], d['b3']], 'jca', '( %s /\\ %s )' % (strip_ante(formula_of(w, d['b1']), A0), strip_ante(formula_of(w, d['b3']), A0))), c([l1l, lamsq], 'jca', '( 1 <_ ( log ` %s ) /\\ %s < ( %s ^ 2 ) )' % (L1, L1, LAM1))], 'jca',
                                                                                    '( ( %s /\\ %s ) /\\ ( 1 <_ ( log ` %s ) /\\ %s < ( %s ^ 2 ) ) )' % (strip_ante(formula_of(w, d['b1']), A0), strip_ante(formula_of(w, d['b3']), A0), L1, L1, LAM1))], 'jca', top_and(z2a)[1])], 'jca', z2a), w.inst('zdzc2')], 'syl', z2c)
    lam1 = c([z2], 'simpld', '1 <_ %s' % LAMG1)
    EX_ = '( exp ` ( ( 5 / 2 ) x. %s ) )' % LAM1
    LG = '( log ` ( %s + 2 ) )' % LAMG1
    bnd = c([z2], 'simprd', '( ( ; ; ; 1 1 2 0 x. %s ) x. %s ) <_ ( ; ; ; 1 1 2 0 x. %s )' % (LAMG1, LG, EX_))
    # ZBAND C_ ZF1( 1/2 , LAMG1 )
    ZF_ = ZF1('S', 'T'); ZB = ZBAND('S', 'T'); ZH = ZF1(HALF, LAMG1)
    Av = '( %s /\\ v e. %s )' % (A0, ZF_)
    cv = Ctx(w, Av)
    vin = cv([], 'simpr', 'v e. %s' % ZF_)
    zf = zfel(w, Av, cv, 'S', lift(w, d['sr'], Av), lift(w, d['tr'], Av), 'v', vin)
    AI = '( abs ` ( Im ` v ) )'
    Ab = '( %s /\\ %s < %s )' % (Av, AI, LAMG1)
    cb = Ctx(w, Ab)
    Lb = lambda st: lift(w, st, Ab)
    hr = numst(w, Ab, HALF, 'RR')
    ZE = tsub(stmt('t21zfel'), {'F': E1, 'A': HALF, 'T': LAMG1, 'Q': 'v'})
    zea, zec = ante_of(ZE)
    ze = cb([cb([hr, Lb(d['lamgr'])], 'jca', zea), w.inst('t21zfel')], 'syl', zec)
    RHS = zec.split(' <-> ', 1)[1][:-2]
    P = top_and(RHS)
    re_ = cb([lin8(w, Ab, [Lb(d['s99']), Lb(zf['re1'])], '%s <_ ( Re ` v )' % HALF, {'S': Lb(d['sr']), '( Re ` v )': Lb(zf['rer'])}), Lb(zf['re2'])], 'jca', '( %s <_ ( Re ` v ) /\\ ( Re ` v ) <_ 1 )' % HALF)
    im_ = cb([cb([], 'simpr', '%s < %s' % (AI, LAMG1))], 'ltled', '%s <_ %s' % (AI, LAMG1))
    mem = cb([cb([Lb(zf['cc']), cb([re_, im_], 'jca', P[1]), cb([Lb(zf['ne1']), Lb(zf['zero'])], 'jca', P[2])], '3jca', RHS), ze], 'mpbird', 'v e. %s' % ZH)
    ral = c([w.s([mem], 'ex', '( %s -> ( %s < %s -> v e. %s ) )' % (Av, AI, LAMG1, ZH))], 'ralrimiva', 'A. v e. %s ( %s < %s -> v e. %s )' % (ZF_, AI, LAMG1, ZH))
    ss = c([ral, w.s([], 'rabss', '( %s C_ %s <-> A. v e. %s ( %s < %s -> v e. %s ) )' % (ZB, ZH, ZF_, AI, LAMG1, ZH))], 'sylibr', '%s C_ %s' % (ZB, ZH))
    # the count in the big box
    finh, allh = zf1_facts(w, A0, c, nx, HALF, numst(w, A0, HALF, 'RR'), numst(w, A0, HALF, 'gt0'), lin8(w, A0, [], '%s <_ 1' % HALF, {}), d['lamgr'], t_=LAMG1)
    Aq = '( %s /\\ q e. %s )' % (A0, ZH)
    cq = Ctx(w, Aq)
    _, ordr, ord0 = ord_facts(w, Aq, cq, lift(w, allh, Aq), cq([], 'simpr', 'q e. %s' % ZH), ZH)
    less = c([finh, ordr, ord0, ss], 'fsumless', 'sum_ q e. %s %s <_ sum_ q e. %s %s' % (ZB, ORD1(), ZH, ORD1()))
    ONE = tsub(stmt('zc1one'), {'T': LAMG1})
    one = c([c([d['lamgr'], lam1], 'jca', ante_of(ONE)[0]), w.inst('zc1one')], 'syl', ante_of(ONE)[1])
    # 6400 Lambda log <_ 6400 e ^ ( 5/2 lambda )
    lgr = c([c([c([d['lamgr'], numst(w, A0, '2', 'RR')], 'readdcld', '( %s + 2 ) e. RR' % LAMG1), lin8(w, A0, [lam1], '0 < ( %s + 2 )' % LAMG1, {LAMG1: d['lamgr']})], 'elrpd', '( %s + 2 ) e. RR+' % LAMG1)], 'relogcld', '%s e. RR' % LG)
    exr = c([c([numst(w, A0, '( 5 / 2 )', 'RR'), d['lamr']], 'remulcld', '( ( 5 / 2 ) x. %s ) e. RR' % LAM1)], 'reefcld', '%s e. RR' % EX_)
    lv = {LAMG1: d['lamgr'], LG: lgr, EX_: exr}
    sc = lin.linarith(w, A0, [bnd], '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (N6400, LAMG1, LG, N6400, EX_), leaves=lv, products=True, atoms=list(lv))
    # e ^ ( 5/2 lambda ) = TPOW
    t2c = c([d['t2r']], 'recnd', '( T + 2 ) e. CC'); t2n = c([d['t2p']], 'rpne0d', '( T + 2 ) =/= 0')
    ec = c([c([numst(w, A0, '( 5 / 2 )', 'RR'), c([numst(w, A0, '1', 'RR'), d['sr']], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '( ( 5 / 2 ) x. ( 1 - S ) ) e. RR')], 'recnd', '( ( 5 / 2 ) x. ( 1 - S ) ) e. CC')
    cx = c([t2c, t2n, ec], 'cxpefd', '%s = ( exp ` ( ( ( 5 / 2 ) x. ( 1 - S ) ) x. ( log ` ( T + 2 ) ) ) )' % TPOW)
    ma = c([numst(w, A0, '( 5 / 2 )', 'CC'), c([c([numst(w, A0, '1', 'RR'), d['sr']], 'resubcld', '( 1 - S ) e. RR')], 'recnd', '( 1 - S ) e. CC'), c([c([d['t2p']], 'relogcld', '( log ` ( T + 2 ) ) e. RR')], 'recnd', '( log ` ( T + 2 ) ) e. CC')], 'mulassd',
           '( ( ( 5 / 2 ) x. ( 1 - S ) ) x. ( log ` ( T + 2 ) ) ) = ( ( 5 / 2 ) x. ( ( 1 - S ) x. ( log ` ( T + 2 ) ) ) )')
    le_ = c([c([c([d['l1e']], 'oveq2d', '( ( 1 - S ) x. %s ) = ( ( 1 - S ) x. ( log ` ( T + 2 ) ) )' % L1)], 'oveq2d', '( ( 5 / 2 ) x. %s ) = ( ( 5 / 2 ) x. ( ( 1 - S ) x. ( log ` ( T + 2 ) ) ) )' % LAM1)], 'fveq2d',
             '%s = ( exp ` ( ( 5 / 2 ) x. ( ( 1 - S ) x. ( log ` ( T + 2 ) ) ) ) )' % EX_)
    tp1 = c([cx, c([ma], 'fveq2d', '( exp ` ( ( ( 5 / 2 ) x. ( 1 - S ) ) x. ( log ` ( T + 2 ) ) ) ) = ( exp ` ( ( 5 / 2 ) x. ( ( 1 - S ) x. ( log ` ( T + 2 ) ) ) ) )')], 'eqtrd', '%s = ( exp ` ( ( 5 / 2 ) x. ( ( 1 - S ) x. ( log ` ( T + 2 ) ) ) ) )' % TPOW)
    tp = c([le_, tp1], 'eqtr4d', '%s = %s' % (EX_, TPOW))
    sc2 = c([sc, c([tp], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (N6400, EX_, N6400, TPOW))], 'breqtrd', '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (N6400, LAMG1, LG, N6400, TPOW))
    # assemble
    fin_, alln = zf1_facts(w, A0, c, nx, 'S', d['sr'], d['s0'], d['s1'], d['tr'])
    finb = c([fin_, c.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZB, ZF_)), '%s C_ %s' % (ZB, ZF_)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % ZB)
    Aqb = '( %s /\\ q e. %s )' % (A0, ZB)
    cqb = Ctx(w, Aqb)
    qz = cqb([cqb([], 'simpr', 'q e. %s' % ZB), w.inst('elrabi')], 'syl', 'q e. %s' % ZF_)
    _, ordb, _ = ord_facts(w, Aqb, cqb, lift(w, alln, Aqb), qz, ZF_)
    sbr = c([finb, ordb], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (ZB, ORD1()))
    shr = c([finh, ordr], 'fsumrecl', '%s e. RR' % ZC1_(HALF, LAMG1))
    m1 = c([numst(w, A0, N6400, 'RR'), c([d['lamgr'], lgr], 'remulcld', '( %s x. %s ) e. RR' % (LAMG1, LG))], 'remulcld', '( %s x. ( %s x. %s ) ) e. RR' % (N6400, LAMG1, LG))
    k1 = c([sbr, shr, m1, less, one], 'letrd', 'sum_ q e. %s %s <_ ( %s x. ( %s x. %s ) )' % (ZB, ORD1(), N6400, LAMG1, LG))
    tpr = c([c([d['t2p'], c([numst(w, A0, '( 5 / 2 )', 'RR'), c([numst(w, A0, '1', 'RR'), d['sr']], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '( ( 5 / 2 ) x. ( 1 - S ) ) e. RR')], 'rpcxpcld', '%s e. RR+' % TPOW)], 'rpred', '%s e. RR' % TPOW)
    w.qed([sbr, m1, c([numst(w, A0, N6400, 'RR'), tpr], 'remulcld', '( %s x. %s ) e. RR' % (N6400, TPOW)), k1, sc2], 'letrd', S['zd2zbc'])
    return go(w)




def sub1(text):
    return tsub(text, {'N': '1'})


def gen_zbg():
    w = W('zd2zbg', 'Theorem Z, band (c) (Lean ` zeroCountBox_one_le_density_of_mertens ` , ` hgoodc ` ): the zeros with ` Lambda_0 <_ abs Im ` are the good zeros of the machine at modulus ` 1 ` , with mass ` <_ gamma_m ( t + 2 ) ^ ( ( 5 / 2 ) ( 1 - S ) ) ` ( ~ zd2good at ` N = 1 ` , ` Y ` the one character, ` G = { z | Lambda_0 <_ abs Im z } ` ).')
    A0 = ante_of(S['zd2zbg'])[0]
    c = Ctx(w, A0)
    GLAM1 = '{ b e. CC | %s <_ ( abs ` ( Im ` b ) ) }' % LAMG1      # binder b: zd2good has $d G z
    THR1 = sub1(THR0); MK1 = sub1(MK)
    tr, t2, sr, s99, s1, l200, t1g1, t2g1, kr, k0, mer1 = [c.g(x) for x in ('T e. RR', '2 <_ T', 'S e. RR', '%s <_ S' % F99, 'S <_ 1', '; ; 2 0 0 <_ %s' % L1, sub1(T1G), sub1(T2G), 'K e. RR', '0 <_ K', sub1('%s <_ ( K x. ( log ` %s ) )' % (MERTD, RPD)))]
    nx, h2 = e1_facts(w, A0, c)
    one = c([nx], 'simpld', '1 e. NN'); x0 = c([nx], 'simprd', '%s e. %s' % (X01, DB1))
    ss = c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS); t0 = lin8(w, A0, [t2], '0 <_ T', {'T': tr}); tt = c([tr, t0], 'jca', TT)
    d = l1_facts(w, A0, c, tr, t2)
    # HGOOD at N = 1, Y = DB1, G = GLAM1
    AI = lambda z: '( abs ` ( Im ` %s ) )' % z
    BODYZ1 = 'A. z e. %s %s <_ %s' % (GLAM1, LAMG1, AI('z'))
    stz0, _ = w.wcongr('%s <_ %s' % (LAMG1, AI('b')), {'b': 'z'}, 'b = z', {'b': w.s([], 'id', '( b = z -> b = z )')})
    rid = w.s([stz0], 'elrab', '( z e. %s <-> ( z e. CC /\\ %s <_ %s ) )' % (GLAM1, LAMG1, AI('z')))
    imp = w.s([rid], 'simprbi', '( z e. %s -> %s <_ %s )' % (GLAM1, LAMG1, AI('z')))
    alz = w.s([imp], 'rgen', BODYZ1)
    HG1 = tsub(HGOOD, {'N': '1', 'Y': DB1, 'G': GLAM1})
    Ax = '( %s /\\ x e. %s )' % (A0, DB1)
    cx = Ctx(w, Ax)
    impx = cx([cx.a1(alz, BODYZ1)], 'a1d', '( x = %s -> %s )' % (X01, BODYZ1))
    hg = c([impx], 'ralrimiva', HG1)
    assert HG1 == 'A. x e. %s ( x = %s -> %s )' % (DB1, X01, BODYZ1), HG1
    GD = tsub(S['zd2good'], {'N': '1', 'Y': DB1, 'G': GLAM1})
    gda, gdc = ante_of(GD)
    nys1 = c([c([one, c.a1(w.s([], 'ssid', '%s C_ %s' % (DB1, DB1)), '%s C_ %s' % (DB1, DB1))], 'jca', '( 1 e. NN /\\ %s C_ %s )' % (DB1, DB1)), c([ss, tt], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', top_and(gda)[0])
    thr = c([c([l200, t1g1], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (L1, sub1(T1G))), c([t2g1, hg], 'jca', '( %s /\\ %s )' % (sub1(T2G), HG1))], 'jca', top_and(gda)[1])
    mk = c([c([kr, k0], 'jca', '( K e. RR /\\ 0 <_ K )'), mer1], 'jca', top_and(gda)[2])
    gd = c([c([nys1, thr, mk], '3jca', gda), w.inst('zd2good')], 'syl', gdc)
    GOODS1 = tsub(GOODS('Y'), {'N': '1', 'Y': DB1, 'G': GLAM1})
    assert gdc.startswith(GOODS1 + ' <_ '), gdc[:200]
    ZFX1 = lambda x: sub1(ZFX(x)); ORDX1 = lambda x, q: sub1(ORDX(x, q))
    INNER = lambda x: 'sum_ q e. { v e. %s | v e. %s } %s' % (ZFX1(x), GLAM1, ORDX1(x, 'q'))
    assert GOODS1 == 'sum_ x e. %s %s' % (DB1, INNER('x')), GOODS1
    # the inner sums are real and nonnegative
    xb = cx([], 'simpr', 'x e. %s' % DB1)
    EZ = tsub(stmt('ezf'), {'N': '1', 'X': 'x', 'A': 'S'})
    eza, ezc = ante_of(EZ)
    ez = cx([cx([cx([lift(w, one, Ax), xb], 'jca', '( 1 e. NN /\\ x e. %s )' % DB1), cx([cx([lift(w, sr, Ax), lift(w, lin8(w, A0, [s99], '0 < S', {'S': sr}), Ax), lift(w, s1, Ax)], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), lift(w, tr, Ax)], 'jca', '( ( S e. RR /\\ 0 < S /\\ S <_ 1 ) /\\ T e. RR )')], 'jca', eza), w.inst('ezf')], 'syl', ezc)
    GX = '{ v e. %s | v e. %s }' % (ZFX1('x'), GLAM1)
    gfin = cx([cx([ez], 'simpld', '%s e. Fin' % ZFX1('x')), cx.a1(w.s([], 'ssrab2', '%s C_ %s' % (GX, ZFX1('x'))), '%s C_ %s' % (GX, ZFX1('x'))), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % GX)
    Aq = '( %s /\\ q e. %s )' % (Ax, GX)
    cq = Ctx(w, Aq)
    qz = cq([cq([], 'simpr', 'q e. %s' % GX), w.inst('elrabi')], 'syl', 'q e. %s' % ZFX1('x'))
    on = cq([lift(w, cx([ez], 'simprd', 'A. q e. %s %s e. NN' % (ZFX1('x'), ORDX1('x', 'q'))), Aq), qz, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (ZFX1('x'), ORDX1('x', 'q'), ZFX1('x'), ORDX1('x', 'q')))], 'sylc', '%s e. NN' % ORDX1('x', 'q'))
    inr = cx([gfin, cq([on], 'nnred', '%s e. RR' % ORDX1('x', 'q'))], 'fsumrecl', '%s e. RR' % INNER('x'))
    in0 = cx([gfin, cq([on], 'nnred', '%s e. RR' % ORDX1('x', 'q')), cq([cq([on], 'nnrpd', '%s e. RR+' % ORDX1('x', 'q'))], 'rpge0d', '0 <_ %s' % ORDX1('x', 'q'))], 'fsumge0', '0 <_ %s' % INNER('x'))
    g1 = w.s([], 'eqid', '%s = %s' % (G1_, G1_)); b1 = w.s([], 'eqid', '%s = %s' % (DB1, DB1))
    dbf = c([one, w.s([g1, b1], 'dchrfi', '( 1 e. NN -> %s e. Fin )' % DB1)], 'syl', '%s e. Fin' % DB1)
    st, inx0 = w.congr(INNER('x'), {'x': X01}, 'x = %s' % X01, {'x': w.s([], 'id', '( x = %s -> x = %s )' % (X01, X01))})
    assert inx0 == INNER(X01), inx0
    ge1 = c([dbf, inr, in0, st, x0], 'fsumge1', '%s <_ %s' % (INNER(X01), GOODS1))
    # { v e. ZF1 | v e. GLAM1 } = ZGOOD
    ZF_ = ZF1('S', 'T')
    assert ZFX1(X01) == ZF_, ZFX1(X01)
    ZG = ZGOOD('S', 'T')
    Av = '( %s /\\ v e. %s )' % (A0, ZF_)
    cv = Ctx(w, Av)
    vin = cv([], 'simpr', 'v e. %s' % ZF_)
    zf = zfel(w, Av, cv, 'S', lift(w, sr, Av), lift(w, tr, Av), 'v', vin)
    stz, chk = w.wcongr('%s <_ %s' % (LAMG1, AI('b')), {'b': 'v'}, 'b = v', {'b': w.s([], 'id', '( b = v -> b = v )')})
    el = w.s([stz], 'elrab', '( v e. %s <-> ( v e. CC /\\ %s <_ %s ) )' % (GLAM1, LAMG1, AI('v')))
    bt = cv([zf['cc']], 'biantrurd', '( %s <_ %s <-> ( v e. CC /\\ %s <_ %s ) )' % (LAMG1, AI('v'), LAMG1, AI('v')))
    bi = cv([cv.a1(el, formula_of(w, el)), bt], 'bitr4d', '( v e. %s <-> %s <_ %s )' % (GLAM1, LAMG1, AI('v')))
    seteq = c([bi], 'rabbidva', '{ v e. %s | v e. %s } = %s' % (ZF_, GLAM1, ZG))
    se = c([seteq], 'sumeq1d', '%s = sum_ q e. %s %s' % (INNER(X01), ZG, ORD1()))
    # reals for letrd
    fin_, alln = zf1_facts(w, A0, c, nx, 'S', sr, lin8(w, A0, [s99], '0 < S', {'S': sr}), s1, tr)
    ZGfin = c([fin_, c.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZG, ZF_)), '%s C_ %s' % (ZG, ZF_)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % ZG)
    Aqg = '( %s /\\ q e. %s )' % (A0, ZG)
    cqg = Ctx(w, Aqg)
    _, ordg, _ = ord_facts(w, Aqg, cqg, lift(w, alln, Aqg), cqg([cqg([], 'simpr', 'q e. %s' % ZG), w.inst('elrabi')], 'syl', 'q e. %s' % ZF_), ZF_)
    sgr = c([ZGfin, ordg], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (ZG, ORD1()))
    goods = c([dbf, inr], 'fsumrecl', '%s e. RR' % GOODS1)
    kf = cjk_facts(w, A0, c, kr, k0)
    DP1 = gdc[len(GOODS1 + ' <_ '):]
    dpr = c([c([d['d1p'], c([numst(w, A0, F52, 'RR'), c([numst(w, A0, '1', 'RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '( %s x. ( 1 - S ) ) e. RR' % F52)], 'rpcxpcld', '( %s ^c ( %s x. ( 1 - S ) ) ) e. RR+' % (D1, F52))], 'rpred', '( %s ^c ( %s x. ( 1 - S ) ) ) e. RR' % (D1, F52))
    rhs = c([kf['gr'], dpr], 'remulcld', '%s e. RR' % DP1)
    fin = c([sgr, goods, rhs, c([c([se], 'eqcomd', 'sum_ q e. %s %s = %s' % (ZG, ORD1(), INNER(X01))), ge1], 'eqbrtrd', 'sum_ q e. %s %s <_ %s' % (ZG, ORD1(), GOODS1)), gd], 'letrd', ante_of(S['zd2zbg'])[1])
    w.qed([fin], 'idi', S['zd2zbg'])
    return go(w)


def gen_zpt():
    w = W('zd2zpt', 'Theorem Z at a point (Lean ` zeroCountBox_one_le_density_of_mertens ` , the large heights): ` N_zeta ( S , T ) <_ ( gamma_m + 6400 ) ( T + 2 ) ^ ( ( 5 / 2 ) ( 1 - S ) ) ` from the band split at ` Lambda_0 ` ( ~ zd2zbg , ~ zd2zbe , ~ zd2zbc ).')
    A0 = ante_of(S['zd2zpt'])[0]
    c = Ctx(w, A0)
    d = zph_facts(w, A0, c)
    THR1 = sub1(THR0); MK1 = sub1(MK)
    zfree, thr1, mk1 = c.g(ZFREE), c.g(THR1), c.g(MK1)
    kr, k0 = c.g('K e. RR'), c.g('0 <_ K')
    nx, h2 = e1_facts(w, A0, c)
    ZF_ = ZF1('S', 'T'); ZG = ZGOOD('S', 'T'); ZB = ZBAND('S', 'T')
    AI = '( abs ` ( Im ` v ) )'
    ZBn = '{ v e. %s | -. %s <_ %s }' % (ZF_, LAMG1, AI)
    fin_, alln = zf1_facts(w, A0, c, nx, 'S', d['sr'], d['s0'], d['s1'], d['tr'])
    Av = '( %s /\\ v e. %s )' % (A0, ZF_)
    cv = Ctx(w, Av)
    zf = zfel(w, Av, cv, 'S', lift(w, d['sr'], Av), lift(w, d['tr'], Av), 'v', cv([], 'simpr', 'v e. %s' % ZF_))
    bi = cv([zf['absr'], lift(w, d['lamgr'], Av)], 'ltnled', '( %s < %s <-> -. %s <_ %s )' % (AI, LAMG1, LAMG1, AI))
    zbeq = c([bi], 'rabbidva', '%s = %s' % (ZB, ZBn))
    Aq = '( %s /\\ q e. %s )' % (A0, ZF_)
    cq = Ctx(w, Aq)
    _, ordr, _ = ord_facts(w, Aq, cq, lift(w, alln, Aq), cq([], 'simpr', 'q e. %s' % ZF_), ZF_)
    sp = c([c.a1(w.s([], 'rabnc', '( %s i^i %s ) = (/)' % (ZG, ZBn)), '( %s i^i %s ) = (/)' % (ZG, ZBn)), c.a1(w.s([], 'rabxm', '%s = ( %s u. %s )' % (ZF_, ZG, ZBn)), '%s = ( %s u. %s )' % (ZF_, ZG, ZBn)), fin_, cq([ordr], 'recnd', '%s e. CC' % ORD1())],
           'fsumsplit', '%s = ( sum_ q e. %s %s + sum_ q e. %s %s )' % (ZC1_('S', 'T'), ZG, ORD1(), ZBn, ORD1()))
    sp2 = c([sp, c([c([c([zbeq], 'eqcomd', '%s = %s' % (ZBn, ZB))], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (ZBn, ORD1(), ZB, ORD1()))], 'oveq2d', '( sum_ q e. %s %s + sum_ q e. %s %s ) = ( sum_ q e. %s %s + sum_ q e. %s %s )' % (ZG, ORD1(), ZBn, ORD1(), ZG, ORD1(), ZB, ORD1()))], 'eqtrd',
             '%s = ( sum_ q e. %s %s + sum_ q e. %s %s )' % (ZC1_('S', 'T'), ZG, ORD1(), ZB, ORD1()))
    # good part
    BG = ante_of(S['zd2zbg'])
    bg = c([c([c([c([d['tr'], d['t2']], 'jca', '( T e. RR /\\ 2 <_ T )'), d['ss']], 'jca', '( ( T e. RR /\\ 2 <_ T ) /\\ %s )' % SS), thr1, mk1], '3jca', BG[0]), w.inst('zd2zbg')], 'syl', BG[1])
    E_ = '( %s x. ( 1 - S ) )' % F52
    d1e = c([d['d1e']], 'oveq1d', '( %s ^c %s ) = %s' % (D1, E_, TPOW))
    bg2 = c([bg, c([d1e], 'oveq2d', '( %s x. ( %s ^c %s ) ) = ( %s x. %s )' % (GAMK1, D1, E_, GAMK1, TPOW))], 'breqtrd', 'sum_ q e. %s %s <_ ( %s x. %s )' % (ZG, ORD1(), GAMK1, TPOW))
    # band part by cases
    tpr = c([c([d['t2p'], c([numst(w, A0, F52, 'RR'), c([numst(w, A0, '1', 'RR'), d['sr']], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '%s e. RR' % E_)], 'rpcxpcld', '%s e. RR+' % TPOW)], 'rpred', '%s e. RR' % TPOW)
    tp0 = c([c([d['t2p'], c([numst(w, A0, F52, 'RR'), c([numst(w, A0, '1', 'RR'), d['sr']], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '%s e. RR' % E_)], 'rpcxpcld', '%s e. RR+' % TPOW)], 'rpge0d', '0 <_ %s' % TPOW)
    LAMSQ = '( %s ^ 2 )' % LAM1
    zph = c.g(ZPH)
    Ale = '( %s /\\ %s <_ %s )' % (A0, LAMSQ, L1)
    cle = Ctx(w, Ale)
    BE = ante_of(S['zd2zbe'])
    be = cle([cle([lift(w, zph, Ale), cle([lift(w, zfree, Ale), cle([], 'simpr', '%s <_ %s' % (LAMSQ, L1))], 'jca', '( %s /\\ %s <_ %s )' % (ZFREE, LAMSQ, L1))], 'jca', BE[0]), w.inst('zd2zbe')], 'syl', BE[1])
    b0 = cle([be, lift(w, c([numst(w, A0, N6400, 'RR'), tpr, numst(w, A0, N6400, 'ge0'), tp0], 'mulge0d', '0 <_ ( %s x. %s )' % (N6400, TPOW)), Ale)], 'eqbrtrd', 'sum_ q e. %s %s <_ ( %s x. %s )' % (ZB, ORD1(), N6400, TPOW))
    Alt = '( %s /\\ %s < %s )' % (A0, L1, LAMSQ)
    clt = Ctx(w, Alt)
    BC = ante_of(S['zd2zbc'])
    bc = clt([clt([lift(w, zph, Alt), clt([], 'simpr', '%s < %s' % (L1, LAMSQ))], 'jca', BC[0]), w.inst('zd2zbc')], 'syl', BC[1])
    tri = c([c([d['lamr']], 'resqcld', '%s e. RR' % LAMSQ), d['l1r'], w.inst('lelttric')], 'syl2anc', '( %s <_ %s \\/ %s < %s )' % (LAMSQ, L1, L1, LAMSQ))
    band = c([b0, bc, tri], 'mpjaodan', 'sum_ q e. %s %s <_ ( %s x. %s )' % (ZB, ORD1(), N6400, TPOW))
    # assemble
    ZGfin = c([fin_, c.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZG, ZF_)), '%s C_ %s' % (ZG, ZF_)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % ZG)
    ZBfin = c([fin_, c.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZB, ZF_)), '%s C_ %s' % (ZB, ZF_)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % ZB)
    def sumre(Z, fin):
        Az = '( %s /\\ q e. %s )' % (A0, Z)
        cz = Ctx(w, Az)
        _, o, _ = ord_facts(w, Az, cz, lift(w, alln, Az), cz([cz([], 'simpr', 'q e. %s' % Z), w.inst('elrabi')], 'syl', 'q e. %s' % ZF_), ZF_)
        return c([fin, o], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (Z, ORD1()))
    sgr, sbr = sumre(ZG, ZGfin), sumre(ZB, ZBfin)
    zr = c([fin_, ordr], 'fsumrecl', '%s e. RR' % ZC1_('S', 'T'))
    kf = cjk_facts(w, A0, c, kr, k0)
    lv = {ZC1_('S', 'T'): zr, 'sum_ q e. %s %s' % (ZG, ORD1()): sgr, 'sum_ q e. %s %s' % (ZB, ORD1()): sbr, GAMK1: kf['gr'], TPOW: tpr}
    fin = lin.linarith(w, A0, [sp2, bg2, band], '%s <_ ( ( %s + %s ) x. %s )' % (ZC1_('S', 'T'), GAMK1, N6400, TPOW), leaves=lv, products=True, atoms=list(lv))
    w.qed([fin], 'idi', S['zd2zpt'])
    return go(w)




def d0_facts(w, A, c, ur, u1, lr, kr, k0, U='U', L='L', K='K'):
    """V0, D0 (with the letters U, L, K substituted): V0 e. RR, U <_ V0, exp L <_ V0, 1 <_ V0, D0 e. RR, 1 <_ D0, and the pieces"""
    V0_ = tsub(V0, {'U': U, 'L': L}); D0_ = tsub(D0Z, {'U': U, 'L': L, 'K': K})
    EL = '( exp ` %s )' % L
    elr = c([lr], 'reefcld', '%s e. RR' % EL); elp = c([lr], 'rpefcld', '%s e. RR+' % EL)
    v0r = c([elr, ur], 'ifcld', '%s e. RR' % V0_)
    uv0 = c([ur, elr, w.inst('max1')], 'syl2anc', '%s <_ %s' % (U, V0_))
    ev0 = c([ur, elr, w.inst('max2')], 'syl2anc', '%s <_ %s' % (EL, V0_))
    v01 = lin8(w, A, [u1, uv0], '1 <_ %s' % V0_, {U: ur, V0_: v0r})
    V2 = '( %s + 2 )' % V0_
    v2p = c([c([v0r, numst(w, A, '2', 'RR')], 'readdcld', '%s e. RR' % V2), lin8(w, A, [v01], '0 < %s' % V2, {V0_: v0r})], 'elrpd', '%s e. RR+' % V2)
    LV = '( log ` %s )' % V2
    lvr = c([v2p], 'relogcld', '%s e. RR' % LV)
    lv0 = c([c([v2p], 'rpred', '%s e. RR' % V2), lin8(w, A, [v01], '1 <_ %s' % V2, {V0_: v0r}), w.inst('logge0')], 'syl2anc', '0 <_ %s' % LV)
    VL = '( %s x. %s )' % (V0_, LV)
    vlr = c([v0r, lvr], 'remulcld', '%s e. RR' % VL); vl0 = c([v0r, lvr, lin8(w, A, [v01], '0 <_ %s' % V0_, {V0_: v0r}), lv0], 'mulge0d', '0 <_ %s' % VL)
    kf = cjk_facts(w, A, c, kr, k0, Kt=K)
    GK = tsub(GAMK, {'K': K})
    P1 = '( 1 + ( %s x. %s ) )' % (N6400, VL)
    p1r = c([numst(w, A, '1', 'RR'), c([numst(w, A, N6400, 'RR'), vlr], 'remulcld', '( %s x. %s ) e. RR' % (N6400, VL))], 'readdcld', '%s e. RR' % P1)
    d0r = c([c([p1r, kf['gr']], 'readdcld', '( %s + %s ) e. RR' % (P1, GK)), numst(w, A, N6400, 'RR')], 'readdcld', '%s e. RR' % D0_)
    lv = {VL: vlr, GK: kf['gr']}
    d01 = lin8(w, A, [vl0, kf['g0']], '1 <_ %s' % D0_, lv)
    d00 = lin8(w, A, [vl0, kf['g0']], '0 <_ %s' % D0_, lv)
    return dict(V0=V0_, D0=D0_, v0r=v0r, uv0=uv0, ev0=ev0, v01=v01, elp=elp, elr=elr, LV=LV, lvr=lvr, VL=VL, vlr=vlr, vl0=vl0, kf=kf, GK=GK, d0r=d0r, d01=d01, d00=d00)


def gen_tzpt():
    w = W('zd2tzpt', 'Theorem Z at a point with the constants ` D_0 ` , ` c_zeta ` , ` L_0 ` , ` C_M ` as class variables (Lean ` zeroCountBox_one_le_density_of_mertens ` , the case split at ` nu_0 = max ( D_0 , exp L_0 ) ` ): ` N_zeta ( S , T ) <_ gamma_zeta ( T + 2 ) ^ ( ( 5 / 2 ) ( 1 - S ) ) ` ( ~ zd2zsm , ~ zd2zpt ).')
    A0 = ante_of(S['zd2tzpt'])[0]
    c = Ctx(w, A0)
    ur, u1, cr, c0, lr, l200, tr, t2, sr, s99, s1, thrc, bandc, zfree, kr, k0 = [c.g(x) for x in (
        'U e. RR', '1 <_ U', 'c e. RR', '0 < c', 'L e. RR', '; ; 2 0 0 <_ L', 'T e. RR', '2 <_ T', 'S e. RR', '%s <_ S' % F99, 'S <_ 1', THRC, BANDC, ZFREE, 'K e. RR', '0 <_ K')]
    d = l1_facts(w, A0, c, tr, t2)
    f = d0_facts(w, A0, c, ur, u1, lr, kr, k0)
    ss = c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS)
    E_ = '( %s x. ( 1 - S ) )' % F52
    er = c([numst(w, A0, F52, 'RR'), c([numst(w, A0, '1', 'RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '%s e. RR' % E_)
    tpp = c([d['t2p'], er], 'rpcxpcld', '%s e. RR+' % TPOW)
    tpr = c([tpp], 'rpred', '%s e. RR' % TPOW); tp0 = c([tpp], 'rpge0d', '0 <_ %s' % TPOW)
    tp1 = c([d['t2r'], lin8(w, A0, [t2], '1 <_ ( T + 2 )', {'T': tr}), er, lin8(w, A0, [s1], '0 <_ %s' % E_, {'S': sr})], 'a5ge1cxp', '1 <_ %s' % TPOW)
    ZC = ZC1_('S', 'T')
    GOAL = '%s <_ ( %s x. %s )' % (ZC, f['D0'], TPOW)
    nx, h2 = e1_facts(w, A0, c)
    fin_, alln = zf1_facts(w, A0, c, nx, 'S', sr, lin8(w, A0, [s99], '0 < S', {'S': sr}), s1, tr)
    Aq = '( %s /\\ q e. %s )' % (A0, ZF1('S', 'T'))
    cq = Ctx(w, Aq)
    _, ordr, _ = ord_facts(w, Aq, cq, lift(w, alln, Aq), cq([], 'simpr', 'q e. %s' % ZF1('S', 'T')), ZF1('S', 'T'))
    zr = c([fin_, ordr], 'fsumrecl', '%s e. RR' % ZC)
    # case A: T + 2 <_ V0
    AA = '( %s /\\ ( T + 2 ) <_ %s )' % (A0, f['V0'])
    ca = Ctx(w, AA)
    La = lambda st: lift(w, st, AA)
    SM = tsub(S['zd2zsm'], {'V': f['V0']})
    sma, smc = ante_of(SM)
    sm = ca([ca([ca([ca([La(tr), La(t2)], 'jca', '( T e. RR /\\ 2 <_ T )'), La(ss)], 'jca', '( ( T e. RR /\\ 2 <_ T ) /\\ %s )' % SS), ca([La(f['v0r']), ca([], 'simpr', '( T + 2 ) <_ %s' % f['V0'])], 'jca', '( %s e. RR /\\ ( T + 2 ) <_ %s )' % (f['V0'], f['V0']))], 'jca', sma), w.inst('zd2zsm')], 'syl', smc)
    M6 = '( %s x. %s )' % (N6400, f['VL'])
    assert smc == '%s <_ %s' % (ZC, M6), smc
    le1 = lin8(w, AA, [La(f['vl0']), La(f['kf']['g0'])], '%s <_ %s' % (M6, f['D0']), {f['VL']: La(f['vlr']), f['GK']: La(f['kf']['gr'])})
    le2a = ca([numst(w, AA, '1', 'RR'), La(tpr), La(f['d0r']), La(f['d00']), La(tp1)], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (f['D0'], f['D0'], TPOW))
    le2 = ca([ca([ca([La(f['d0r'])], 'recnd', '%s e. CC' % f['D0'])], 'mulridd', '( %s x. 1 ) = %s' % (f['D0'], f['D0'])), le2a], 'eqbrtrrd', '%s <_ ( %s x. %s )' % (f['D0'], f['D0'], TPOW))
    m6r = ca([numst(w, AA, N6400, 'RR'), La(f['vlr'])], 'remulcld', '%s e. RR' % M6)
    dtp = ca([La(f['d0r']), La(tpr)], 'remulcld', '( %s x. %s ) e. RR' % (f['D0'], TPOW))
    ka = ca([La(zr), m6r, La(f['d0r']), sm, le1], 'letrd', '%s <_ %s' % (ZC, f['D0']))
    casea = ca([La(zr), La(f['d0r']), dtp, ka, le2], 'letrd', GOAL)
    # case B: V0 < T + 2
    AB = '( %s /\\ %s < ( T + 2 ) )' % (A0, f['V0'])
    cb = Ctx(w, AB)
    Lb = lambda st: lift(w, st, AB)
    ud = lin8(w, AB, [Lb(f['uv0']), cb([], 'simpr', '%s < ( T + 2 )' % f['V0'])], 'U <_ ( T + 2 )', {'U': Lb(ur), f['V0']: Lb(f['v0r']), 'T': Lb(tr)})
    ud1 = cb([ud, Lb(d['d1e'])], 'breqtrrd', 'U <_ %s' % D1)
    thr = cb([ud1, Lb(thrc)], 'mpd', THRC.split(' -> ', 1)[1][:-2])
    el = lin8(w, AB, [Lb(f['ev0']), cb([], 'simpr', '%s < ( T + 2 )' % f['V0'])], '( exp ` L ) <_ ( T + 2 )', {'( exp ` L )': Lb(f['elr']), f['V0']: Lb(f['v0r']), 'T': Lb(tr)})
    lel = cb([el, cb([Lb(f['elp']), Lb(d['t2p'])], 'logled', '( ( exp ` L ) <_ ( T + 2 ) <-> ( log ` ( exp ` L ) ) <_ ( log ` ( T + 2 ) ) )')], 'mpbid', '( log ` ( exp ` L ) ) <_ ( log ` ( T + 2 ) )')
    lle = cb([lel, cb([Lb(lr)], 'relogefd', '( log ` ( exp ` L ) ) = L'), cb([Lb(d['l1e'])], 'eqcomd', '( log ` ( T + 2 ) ) = %s' % L1)], '3brtr3d', 'L <_ %s' % L1)
    bandh = cb([lle, Lb(bandc)], 'mpd', BANDH)
    T3 = '( ; ; 2 0 0 <_ %s /\\ %s /\\ %s )' % (L1, sub1(T1G), sub1(T2G))
    t3 = cb([thr], 'simpld', T3); mert = cb([thr], 'simprd', '%s <_ ( K x. ( log ` %s ) )' % (MERT1, RPD1))
    l200_1 = cb([t3], 'simp1d', '; ; 2 0 0 <_ %s' % L1); t1g = cb([t3], 'simp2d', sub1(T1G)); t2g = cb([t3], 'simp3d', sub1(T2G))
    zph = cb([cb([cb([Lb(tr), Lb(t2)], 'jca', '( T e. RR /\\ 2 <_ T )'), Lb(ss)], 'jca', '( ( T e. RR /\\ 2 <_ T ) /\\ %s )' % SS), cb([cb([Lb(cr), Lb(c0)], 'jca', '( c e. RR /\\ 0 < c )'), cb([l200_1, bandh], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (L1, BANDH))], 'jca', '( ( c e. RR /\\ 0 < c ) /\\ ( ; ; 2 0 0 <_ %s /\\ %s ) )' % (L1, BANDH))], 'jca', ZPH)
    thr1 = cb([cb([l200_1, t1g], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (L1, sub1(T1G))), t2g], 'jca', sub1(THR0))
    mk1 = cb([cb([Lb(kr), Lb(k0)], 'jca', '( K e. RR /\\ 0 <_ K )'), mert], 'jca', sub1(MK))
    ZP = ante_of(S['zd2zpt'])
    zpt = cb([cb([cb([zph, Lb(zfree)], 'jca', '( %s /\\ %s )' % (ZPH, ZFREE)), cb([thr1, mk1], 'jca', '( %s /\\ %s )' % (sub1(THR0), sub1(MK)))], 'jca', ZP[0]), w.inst('zd2zpt')], 'syl', ZP[1])
    GK6 = '( %s + %s )' % (f['GK'], N6400)
    gk6r = cb([Lb(f['kf']['gr']), numst(w, AB, N6400, 'RR')], 'readdcld', '%s e. RR' % GK6)
    le3 = lin8(w, AB, [Lb(f['vl0'])], '%s <_ %s' % (GK6, f['D0']), {f['VL']: Lb(f['vlr']), f['GK']: Lb(f['kf']['gr'])})
    le4 = cb([gk6r, Lb(f['d0r']), Lb(tpr), Lb(tp0), le3], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (GK6, TPOW, f['D0'], TPOW))
    caseb = cb([Lb(zr), cb([gk6r, Lb(tpr)], 'remulcld', '( %s x. %s ) e. RR' % (GK6, TPOW)), cb([Lb(f['d0r']), Lb(tpr)], 'remulcld', '( %s x. %s ) e. RR' % (f['D0'], TPOW)), zpt, le4], 'letrd', GOAL)
    tri = c([d['t2r'], f['v0r'], w.inst('lelttric')], 'syl2anc', '( ( T + 2 ) <_ %s \\/ %s < ( T + 2 ) )' % (f['V0'], f['V0']))
    w.qed([casea, caseb, tri], 'mpjaodan', S['zd2tzpt'])
    return go(w)


def gen_tz1():
    w = W('zd2tz1', 'Theorem Z, modulus 1, the frozen form (Lean ` zeroCountBox_one_le_density_of_mertens ` ): there is ` gamma_zeta >_ 1 ` with ` N_zeta ( s , t ) <_ gamma_zeta ( t + 2 ) ^ ( ( 5 / 2 ) ( 1 - s ) ) ` for ` t >_ 2 ` , ` 99 / 100 <_ s <_ 1 ` ; the constants come from ~ zd2thr , ~ zrzf , ~ zdband and ~ zdmert ( ~ zd2tzpt ).')
    THRB = S['zd2thr'][len('E. u e. RR ( 1 <_ u /\\ '):-2]
    assert S['zd2thr'] == 'E. u e. RR ( 1 <_ u /\\ %s )' % THRB
    AU = '( u e. RR /\\ ( 1 <_ u /\\ %s ) )' % THRB
    ZRZF = stmt('zrzf')
    assert ZRZF == 'E. c e. RR ( ( 0 < c /\\ c <_ ( 1 / 2 ) ) /\\ %s )' % ZFREE, ZRZF
    AC = '( c e. RR /\\ ( ( 0 < c /\\ c <_ ( 1 / 2 ) ) /\\ %s ) )' % ZFREE
    ZBD = tsub(stmt('zdband'), {'A': 'c', 'B': C6})
    zba, zbc = ante_of(ZBD)
    BANDBu = zbc[len('E. u e. RR ( ; ; 2 0 0 <_ u /\\ '):-2]
    assert zbc == 'E. u e. RR ( ; ; 2 0 0 <_ u /\\ %s )' % BANDBu, zbc
    BANDBl = tsub(BANDBu, {'u': 'l'})
    AL = '( l e. RR /\\ ( ; ; 2 0 0 <_ l /\\ %s ) )' % BANDBl
    A0 = '( ( %s /\\ %s ) /\\ %s )' % (AU, AC, AL)
    c = Ctx(w, A0)
    ur, u1, thrb, cr, c0, zfree, lr, l200, bandb = [c.g(x) for x in ('u e. RR', '1 <_ u', THRB, 'c e. RR', '0 < c', ZFREE, 'l e. RR', '; ; 2 0 0 <_ l', BANDBl)]
    PT = '( 2 <_ t /\\ ( %s <_ s /\\ s <_ 1 ) )' % F99
    A3 = '( ( ( %s /\\ t e. RR ) /\\ s e. RR ) /\\ %s )' % (A0, PT)
    c3 = Ctx(w, A3)
    L3 = lambda st: lift(w, st, A3)
    tr, sr, t2, s99, s1 = [c3.g(x) for x in ('t e. RR', 's e. RR', '2 <_ t', '%s <_ s' % F99, 's <_ 1')]
    SUB = {'U': 'u', 'L': 'l', 'T': 't', 'S': 's', 'K': CMX}
    D1t = tsub(D1, SUB); L1t = tsub(L1, SUB); RPD1t = tsub(RPD1, SUB); MERT1t = tsub(MERT1, SUB)
    t2r = c3([tr, numst(w, A3, '2', 'RR')], 'readdcld', '( t + 2 ) e. RR')
    t2p = c3([t2r, lin8(w, A3, [t2], '0 < ( t + 2 )', {'t': tr})], 'elrpd', '( t + 2 ) e. RR+')
    d1e = c3([c3([t2r], 'recnd', '( t + 2 ) e. CC')], 'mullidd', '%s = ( t + 2 )' % D1t)
    d1p = c3([d1e, t2p], 'eqeltrd', '%s e. RR+' % D1t); d1r = c3([d1p], 'rpred', '%s e. RR' % D1t)
    l1r = c3([d1p], 'relogcld', '%s e. RR' % L1t)
    # THRC at the point
    TB3 = '( ; ; 2 0 0 <_ ( log ` v ) /\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 7 9 / ; ; ; 4 0 0 0 ) ) /\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 1 3 / ; ; 5 0 0 ) ) )' % (A1C, B2C)
    at, newt = ral_at(w, A3, L3(thrb), 'v', D1t, '( u <_ v -> %s )' % TB3, d1r)
    T3t = tsub('( ; ; 2 0 0 <_ %s /\\ %s /\\ %s )' % (L1, sub1(T1G), sub1(T2G)), SUB)
    assert newt == '( u <_ %s -> %s )' % (D1t, T3t), newt[:300]
    Au = '( %s /\\ u <_ %s )' % (A3, D1t)
    cu = Ctx(w, Au)
    t3 = cu([cu([], 'simpr', 'u <_ %s' % D1t), lift(w, at, Au)], 'mpd', T3t)
    l200t = cu([t3], 'simp1d', '; ; 2 0 0 <_ %s' % L1t)
    rpr = cu([lift(w, d1p, Au), numst(w, Au, '( 1 / ; ; 1 0 0 )', 'RR')], 'rpcxpcld', '%s e. RR+' % RPD1t)
    two = cu([cu([lift(w, d1p, Au), l200t], 'jca', '( %s e. RR+ /\\ ; ; 2 0 0 <_ %s )' % (D1t, L1t)), w.inst('zd2rpar')], 'syl', '2 <_ %s' % RPD1t)
    MT = tsub(stmt('zdmert'), {'R': RPD1t})
    mta, mtc = ante_of(MT)
    mt = cu([cu([cu([rpr], 'rpred', '%s e. RR' % RPD1t), two], 'jca', mta), w.inst('zdmert')], 'syl', mtc)
    both = cu([t3, mt], 'jca', '( %s /\\ %s )' % (T3t, mtc))
    thrc = w.s([both], 'ex', '( %s -> ( u <_ %s -> ( %s /\\ %s ) ) )' % (A3, D1t, T3t, mtc))
    THRCt = tsub(THRC, SUB)
    assert formula_of(w, thrc) == '( %s -> %s )' % (A3, THRCt), (formula_of(w, thrc)[-400:], THRCt[-400:])
    # BANDC at the point
    BB3 = BANDBl[len('A. v e. RR '):]
    assert BANDBl == 'A. v e. RR %s' % BB3
    bt, newb = ral_at(w, A3, L3(bandb), 'v', L1t, BB3, l1r)
    BANDCt = tsub(BANDC, SUB)
    assert newb == BANDCt, (newb[:300], BANDCt[:300])
    cmr, cm0 = cmx_facts(w, A3, c3)
    TP = tsub(S['zd2tzpt'], SUB)
    tpa, tpc = ante_of(TP)
    tp = c3([c3([c3([c3([c3([L3(ur), L3(u1)], 'jca', '( u e. RR /\\ 1 <_ u )'), c3([c3([L3(cr), L3(c0)], 'jca', '( c e. RR /\\ 0 < c )'), c3([L3(lr), L3(l200)], 'jca', '( l e. RR /\\ ; ; 2 0 0 <_ l )')], 'jca', '( ( c e. RR /\\ 0 < c ) /\\ ( l e. RR /\\ ; ; 2 0 0 <_ l ) )')], 'jca',
                          '( ( u e. RR /\\ 1 <_ u ) /\\ ( ( c e. RR /\\ 0 < c ) /\\ ( l e. RR /\\ ; ; 2 0 0 <_ l ) ) )'),
                       c3([c3([tr, t2], 'jca', '( t e. RR /\\ 2 <_ t )'), c3([sr, c3([s99, s1], 'jca', '( %s <_ s /\\ s <_ 1 )' % F99)], 'jca', tsub(SS, SUB))], 'jca', '( ( t e. RR /\\ 2 <_ t ) /\\ %s )' % tsub(SS, SUB))], 'jca', top_and(tpa)[0]),
                   c3([c3([thrc, bt], 'jca', '( %s /\\ %s )' % (THRCt, BANDCt)), c3([L3(zfree), c3([cmr, cm0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (CMX, CMX))], 'jca', '( %s /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (ZFREE, CMX, CMX))], 'jca', top_and(tpa)[1])], 'jca', tpa), w.inst('zd2tzpt')], 'syl', tpc)
    D0t = tsub(D0Z, SUB)
    BODY = tsub(ZBODY1('t', 's'), {'d': D0t})
    assert BODY == '( %s -> %s )' % (PT, tpc), (BODY[-300:], tpc[-300:])
    A2 = '( ( %s /\\ t e. RR ) /\\ s e. RR )' % A0
    st = w.s([tp], 'ex', '( %s -> %s )' % (A2, BODY))
    r1 = w.s([st], 'ralrimiva', '( ( %s /\\ t e. RR ) -> A. s e. RR %s )' % (A0, BODY))
    r2 = w.s([r1], 'ralrimiva', '( %s -> A. t e. RR A. s e. RR %s )' % (A0, BODY))
    cmr0, cm00 = cmx_facts(w, A0, c)
    f = d0_facts(w, A0, c, ur, u1, lr, cmr0, cm00, U='u', L='l', K=CMX)
    assert f['D0'] == D0t
    MAT = S['zd2tz1'][len('E. d '):]
    MAT_d = tsub(MAT, {'d': D0t})
    full = c([c([f['d0r'], f['d01']], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (D0t, D0t)), r2], 'jca', MAT_d)
    st_d, chk = w.wcongr(MAT, {'d': D0t}, 'd = %s' % D0t, {'d': w.s([], 'id', '( d = %s -> d = %s )' % (D0t, D0t))})
    assert chk == MAT_d, chk[:200]
    exd = w.s([w.s([], 'ovex', '%s e. _V' % D0t), st_d], 'spcev', '( %s -> E. d %s )' % (MAT_d, MAT))
    e1 = c([full, c.a1(exd, formula_of(w, exd))], 'mpd', 'E. d %s' % MAT)
    GOAL = 'E. d %s' % MAT
    # eliminate l (zdband, renamed u -> l), then c (zrzf), then u (zd2thr)
    AUC = '( %s /\\ %s )' % (AU, AC)
    r_l = w.s([e1], 'rexlimdvaa', '( %s -> ( E. l e. RR ( ; ; 2 0 0 <_ l /\\ %s ) -> %s ) )' % (AUC, BANDBl, GOAL))
    cuc = Ctx(w, AUC)
    crp = cuc([cuc.g('c e. RR'), cuc.g('0 < c')], 'elrpd', 'c e. RR+')
    c6r = cuc([cuc([cuc([numst(w, AUC, N3200, 'RR+'), cuc([numst(w, AUC, '1', 'RR')], 'rpefcld', '( exp ` 1 ) e. RR+')], 'rpmulcld', '( %s x. ( exp ` 1 ) ) e. RR+' % N3200), numst(w, AUC, '; 6 0', 'RR+')], 'rpmulcld', '( ( %s x. ( exp ` 1 ) ) x. ; 6 0 ) e. RR+' % N3200)], 'relogcld', '%s e. RR' % C6)
    zb = cuc([cuc([crp, c6r], 'jca', zba), w.inst('zdband')], 'syl', zbc)
    stl, chkl = w.wcongr('( ; ; 2 0 0 <_ u /\\ %s )' % BANDBu, {'u': 'l'}, 'u = l', {'u': w.s([], 'id', '( u = l -> u = l )')})
    assert chkl == '( ; ; 2 0 0 <_ l /\\ %s )' % BANDBl, chkl[:200]
    cbv = w.s([stl], 'cbvrexvw', '( %s <-> E. l e. RR ( ; ; 2 0 0 <_ l /\\ %s ) )' % (zbc, BANDBl))
    zbl = cuc([zb, cuc.a1(cbv, formula_of(w, cbv))], 'mpbid', 'E. l e. RR ( ; ; 2 0 0 <_ l /\\ %s )' % BANDBl)
    e2 = cuc([zbl, r_l], 'mpd', GOAL)
    r_c = w.s([e2], 'rexlimdvaa', '( %s -> ( %s -> %s ) )' % (AU, ZRZF, GOAL))
    e3 = w.s([w.s([w.s([], 'zrzf', ZRZF)], 'a1i', '( %s -> %s )' % (AU, ZRZF)), r_c], 'mpd', '( %s -> %s )' % (AU, GOAL))
    r_u = w.s([e3], 'rexlimiva', '( %s -> %s )' % (S['zd2thr'], GOAL))
    w.qed([w.s([], 'zd2thr', S['zd2thr']), r_u], 'ax-mp', S['zd2tz1'])
    return go(w)


def gen_tz():
    w = W('zd2tz', 'Theorem Z, every modulus, the frozen form (Lean ` zeroCountBox_trivChar_le_density ` ): ` N ( s , t , chi_0 ) <_ gamma_zeta ( t + 2 ) ^ ( ( 5 / 2 ) ( 1 - s ) ) ` for every modulus ` n ` ( ~ zd2tz1 , the principal box count equals zeta\'s by ~ zc1teq ).')
    MAT1 = S['zd2tz1'][len('E. d '):]
    MAT = S['zd2tz'][len('E. d '):]
    c = Ctx(w, MAT1)
    dr, d1, al = c.g('d e. RR'), c.g('1 <_ d'), c.g('A. t e. RR A. s e. RR %s' % ZBODY1('t', 's'))
    PT = '( 2 <_ t /\\ ( %s <_ s /\\ s <_ 1 ) )' % F99
    A4 = '( ( ( ( %s /\\ n e. NN ) /\\ t e. RR ) /\\ s e. RR ) /\\ %s )' % (MAT1, PT)
    c4 = Ctx(w, A4)
    L4 = lambda st: lift(w, st, A4)
    nn_, tr, sr, t2, s99, s1 = [c4.g(x) for x in ('n e. NN', 't e. RR', 's e. RR', '2 <_ t', '%s <_ s' % F99, 's <_ 1')]
    a1 = c4([L4(al), tr, w.s([], 'rspa', '( ( A. t e. RR A. s e. RR %s /\\ t e. RR ) -> A. s e. RR %s )' % (ZBODY1('t', 's'), ZBODY1('t', 's')))], 'syl2anc', 'A. s e. RR %s' % ZBODY1('t', 's'))
    a2 = c4([a1, sr, w.s([], 'rspa', '( ( A. s e. RR %s /\\ s e. RR ) -> %s )' % (ZBODY1('t', 's'), ZBODY1('t', 's')))], 'syl2anc', ZBODY1('t', 's'))
    b1 = c4([c4.g(PT), a2], 'mpd', ZBODY1('t', 's').split(' -> ', 1)[1][:-2])
    X0n = '( 0g ` ( DChr ` n ) )'; DBn = '( Base ` ( DChr ` n ) )'; Gn = '( DChr ` n )'
    g = w.s([], 'eqid', '%s = %s' % (Gn, Gn)); b = w.s([], 'eqid', '%s = %s' % (DBn, DBn)); o = w.s([], 'eqid', '%s = %s' % (X0n, X0n))
    grp = c4([c4([nn_, w.s([g], 'dchrabl', '( n e. NN -> %s e. Abel )' % Gn)], 'syl', '%s e. Abel' % Gn), w.inst('ablgrp')], 'syl', '%s e. Grp' % Gn)
    x0 = c4([grp, w.s([b, o], 'grpidcl', '( %s e. Grp -> %s e. %s )' % (Gn, X0n, DBn))], 'syl', '%s e. %s' % (X0n, DBn))
    TE = tsub(stmt('zc1teq'), {'N': 'n', 'X': X0n, 'A': 's', 'T': 't'})
    tea, tec = ante_of(TE)
    te = c4([c4([c4([c4([nn_, x0], 'jca', '( n e. NN /\\ %s e. %s )' % (X0n, DBn)), c4([], 'eqidd', '%s = %s' % (X0n, X0n))], 'jca', top_and(tea)[0]), c4([c4([sr, lin8(w, A4, [s99], '0 < s', {'s': sr}), s1], '3jca', '( s e. RR /\\ 0 < s /\\ s <_ 1 )'), tr], 'jca', top_and(tea)[1])], 'jca', tea), w.inst('zc1teq')], 'syl', tec)
    assert tec == '%s = %s' % (ZC0('n', 's', 't'), ZC1_('s', 't')), tec[:200]
    b2 = c4([te, b1], 'eqbrtrd', ZBODY('n', 't', 's').split(' -> ', 1)[1][:-2])
    A3 = '( ( ( %s /\\ n e. NN ) /\\ t e. RR ) /\\ s e. RR )' % MAT1
    st = w.s([b2], 'ex', '( %s -> %s )' % (A3, ZBODY('n', 't', 's')))
    r1 = ralrimi_nf(w, st, 's', 'RR', '( ( %s /\\ n e. NN ) /\\ t e. RR )' % MAT1, ZBODY('n', 't', 's'))
    r2 = ralrimi_nf(w, r1, 't', 'RR', '( %s /\\ n e. NN )' % MAT1, 'A. s e. RR %s' % ZBODY('n', 't', 's'))
    r3 = w.s([r2], 'ralrimiva', '( %s -> A. n e. NN A. t e. RR A. s e. RR %s )' % (MAT1, ZBODY('n', 't', 's')))
    full = c([c([dr, d1], 'jca', '( d e. RR /\\ 1 <_ d )'), r3], 'jca', MAT)
    ex = w.s([full], 'eximi', '( E. d %s -> E. d %s )' % (MAT1, MAT))
    w.qed([w.s([], 'zd2tz1', S['zd2tz1']), ex], 'ax-mp', S['zd2tz'])
    return go(w)


GENS = {'zd2zsm': gen_zsm, 'zd2zbe': gen_zbe, 'zd2zbc': gen_zbc, 'zd2zbg': gen_zbg, 'zd2zpt': gen_zpt, 'zd2tzpt': gen_tzpt, 'zd2tz1': gen_tz1, 'zd2tz': gen_tz}

if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
