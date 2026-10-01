"""Sortie GF2, section R: Lemma 6.4, the row sums of the main term (Lean binWeight, sum_Ioc_inv_sq_le,
sum_binWeight_le, norm_G1_le_binWeight, row_sum_le).
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_r.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L
from mvlib import ringeq, ringeqp

S_ = L.S
F400 = '; ; 4 0 0'
F401 = '; ; 4 0 1'
BWB = lambda m: 'if ( %s = 0 , 1 , if ( %s <_ %s , ( 1 / %s ) , ( %s / ( %s ^ 2 ) ) ) )' % (m, m, F400, m, F400, m)
BWF = '( z e. NN0 |-> %s )' % BWB('z')
BW = lambda x: '( %s ` %s )' % (BWF, x)
L.BWF = BWF
S_['gf2bsum'] = '( M e. NN0 -> sum_ m e. ( 1 ... M ) %s <_ ( 2 + ( log ` %s ) ) )' % (BW('m'), F400)


def bwv(w, ante, x, mem):
    """( ante -> ( BWF ` x ) = BWB(x) ) from mem ( ante -> x e. NN0 )"""
    st = mkst(w, ante)
    inner = 'if ( %s <_ %s , ( 1 / %s ) , ( %s / ( %s ^ 2 ) ) )' % (x, F400, x, F400, x)
    ea = a1(w, ante, w.s([], '1ex', '1 e. _V'), '1 e. _V')
    eb = st([st([], 'ovexd', '( 1 / %s ) e. _V' % x), st([], 'ovexd', '( %s / ( %s ^ 2 ) ) e. _V' % (F400, x))], 'ifexd', '%s e. _V' % inner)
    ex = st([ea, eb], 'ifexd', '%s e. _V' % BWB(x))
    v, _ = mpv(w, ante, 'z', 'NN0', BWB('z'), x, mem, exs=ex)
    return v


def uzd(w, ante, mz, nz, le, M, N):
    """( ante -> N e. ( ZZ>= ` M ) ) (eluz2, main body)"""
    st = mkst(w, ante)
    c = st([mz, nz, le], '3jca', '( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s )' % (M, N, M, N))
    return st([c, w.inst('eluz2')], 'sylibr', '%s e. ( ZZ>= ` %s )' % (N, M))


def bwpos(w, ante, x, nnst):
    """under ante with nnst ( ante -> x e. NN ): BW(x) = inner if, BW(x) e. RR, 0 <_ BW(x)"""
    st = mkst(w, ante)
    inner = 'if ( %s <_ %s , ( 1 / %s ) , ( %s / ( %s ^ 2 ) ) )' % (x, F400, x, F400, x)
    v = bwv(w, ante, x, st([nnst], 'nnnn0d', '%s e. NN0' % x))
    ne = st([nnst], 'nnne0d', '%s =/= 0' % x)
    v2 = st([v, st([ne, w.inst('ifnefalse')], 'syl', '%s = %s' % (BWB(x), inner))], 'eqtrd', '%s = %s' % (BW(x), inner))
    xrp = st([nnst], 'nnrpd', '%s e. RR+' % x)
    r1 = st([xrp], 'rpreccld', '( 1 / %s ) e. RR+' % x)
    r2 = st([a1(w, ante, num.rp_nat(w, 400), '%s e. RR+' % F400), st([xrp, a1(w, ante, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % x)],
            'rpdivcld', '( %s / ( %s ^ 2 ) ) e. RR+' % (F400, x))
    ip = st([r1, r2], 'ifcld', '%s e. RR+' % inner)
    bp = st([v2, ip], 'eqeltrd', '%s e. RR+' % BW(x))
    return v2, st([bp], 'rpred', '%s e. RR' % BW(x)), st([bp], 'rpge0d', '0 <_ %s' % BW(x)), inner


def gf2bsum():
    w = W('gf2bsum', 'The bin weights have bounded partial sums: ` sum_ ( 1 <_ m <_ M ) beta ( m ) <_ 2 + log 400 ` (Lean ` sum_binWeight_le ` , '
                     '` sum_Ioc_inv_sq_le ` ; ~ harmonicubnd , ~ telfsum ).')
    a = 'M e. NN0'
    st = mkst(w, a)
    MP = '( M + %s )' % F400
    m0 = st([], 'id', 'M e. NN0')
    c400n0 = a1(w, a, num.nn0(w, 400), '%s e. NN0' % F400)
    c400z = a1(w, a, num.z_nat(w, 400), '%s e. ZZ' % F400)
    c400r = a1(w, a, num.re_nat(w, 400), '%s e. RR' % F400)
    mpn0 = st([m0, c400n0], 'nn0addcld', '%s e. NN0' % MP)
    mpz = st([mpn0], 'nn0zd', '%s e. ZZ' % MP); mpr = st([mpn0], 'nn0red', '%s e. RR' % MP)
    mz = st([m0], 'nn0zd', 'M e. ZZ'); mr = st([m0], 'nn0red', 'M e. RR'); mg0 = st([m0], 'nn0ge0d', '0 <_ M')
    lv = {'M': mr}
    le1 = lin.linarith(w, a, [mg0], 'M <_ %s' % MP, leaves=lv)
    mpuz = uzd(w, a, mz, mpz, le1, 'M', MP)
    sub1 = st([mpuz, w.inst('fzss2')], 'syl', '( 1 ... M ) C_ ( 1 ... %s )' % MP)
    U = '( 1 ... %s )' % MP
    am = '( %s /\\ m e. %s )' % (a, U)
    sm = mkst(w, am)
    mnn = sm([sm([], 'simpr', 'm e. %s' % U), w.inst('elfznn')], 'syl', 'm e. NN')
    v2, bwr, bw0, inner = bwpos(w, am, 'm', mnn)
    fz = st([], 'fzfid', '%s e. Fin' % U)
    s1 = st([fz, sub1, bwr, bw0], 'fsumless', 'sum_ m e. ( 1 ... M ) %s <_ sum_ m e. %s %s' % (BW('m'), U, BW('m')))
    one_z = a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')
    in400 = st([one_z, mpz, c400z, a1(w, a, num.le_lit(w, '1', F400), '1 <_ %s' % F400), lin.linarith(w, a, [mg0], '%s <_ %s' % (F400, MP), leaves=lv)], 'elfzd',
               '%s e. %s' % (F400, U))
    spl = st([in400, w.inst('fzsplit')], 'syl', '%s = ( ( 1 ... %s ) u. ( ( %s + 1 ) ... %s ) )' % (U, F400, F400, MP))
    e401 = a1(w, a, num.add_nat(w, 400, 1), '( %s + 1 ) = %s' % (F400, F401))
    rg = st([e401], 'oveq1d', '( ( %s + 1 ) ... %s ) = ( %s ... %s )' % (F400, MP, F401, MP))
    spl2 = st([spl, st([rg], 'uneq2d', '( ( 1 ... %s ) u. ( ( %s + 1 ) ... %s ) ) = ( ( 1 ... %s ) u. ( %s ... %s ) )' % (F400, F400, MP, F400, F401, MP))], 'eqtrd',
              '%s = ( ( 1 ... %s ) u. ( %s ... %s ) )' % (U, F400, F401, MP))
    dj = st([a1(w, a, num.le_lit(w, F400, F401, strict=True), '%s < %s' % (F400, F401)), w.inst('fzdisj')], 'syl', '( ( 1 ... %s ) i^i ( %s ... %s ) ) = (/)' % (F400, F401, MP))
    bwc = sm([bwr], 'recnd', '%s e. CC' % BW('m'))
    fs = st([dj, spl2, fz, bwc], 'fsumsplit', 'sum_ m e. %s %s = ( sum_ m e. ( 1 ... %s ) %s + sum_ m e. ( %s ... %s ) %s )' % (U, BW('m'), F400, BW('m'), F401, MP, BW('m')))
    # the head: 1 / m, harmonic
    H = '( 1 ... %s )' % F400
    ah = '( %s /\\ m e. %s )' % (a, H)
    sh = mkst(w, ah)
    mh = sh([], 'simpr', 'm e. %s' % H)
    mhn = sh([mh, w.inst('elfznn')], 'syl', 'm e. NN')
    v2h, _, _, _ = bwpos(w, ah, 'm', mhn)
    mle = sh([mh, w.inst('elfzle2')], 'syl', 'm <_ %s' % F400)
    hv = sh([v2h, sh([mle, w.inst('iftrue')], 'syl', '%s = ( 1 / m )' % inner)], 'eqtrd', '%s = ( 1 / m )' % BW('m'))
    hs = st([hv], 'sumeq2dv', 'sum_ m e. %s %s = sum_ m e. %s ( 1 / m )' % (H, BW('m'), H))
    hu = w.s([num.re_nat(w, 400), num.le_lit(w, '1', F400), w.inst('harmonicubnd')], 'mp2an',
             'sum_ m e. ( 1 ... ( |_ ` %s ) ) ( 1 / m ) <_ ( ( log ` %s ) + 1 )' % (F400, F400))
    fl = w.s([num.z_nat(w, 400), w.inst('flid')], 'ax-mp', '( |_ ` %s ) = %s' % (F400, F400))
    hr = w.s([w.s([fl], 'oveq2i', '( 1 ... ( |_ ` %s ) ) = %s' % (F400, H))], 'sumeq1i', 'sum_ m e. ( 1 ... ( |_ ` %s ) ) ( 1 / m ) = sum_ m e. %s ( 1 / m )' % (F400, H))
    hu2 = w.s([hr, hu], 'eqbrtrri', 'sum_ m e. %s ( 1 / m ) <_ ( ( log ` %s ) + 1 )' % (H, F400))
    hd = st([hs, a1(w, a, hu2, 'sum_ m e. %s ( 1 / m ) <_ ( ( log ` %s ) + 1 )' % (H, F400))], 'eqbrtrd', 'sum_ m e. %s %s <_ ( ( log ` %s ) + 1 )' % (H, BW('m'), F400))
    # the tail: 400 / m ^ 2 <_ 400 ( 1 / ( m - 1 ) - 1 / m ), telescoping
    T_ = '( %s ... %s )' % (F401, MP)
    at = '( %s /\\ m e. %s )' % (a, T_)
    stt = mkst(w, at)
    mt = stt([], 'simpr', 'm e. %s' % T_)
    mtz = stt([mt, w.inst('elfzelz')], 'syl', 'm e. ZZ')
    mtr = stt([mtz], 'zred', 'm e. RR')
    m401 = stt([mt, w.inst('elfzle1')], 'syl', '%s <_ m' % F401)
    lvt = {'m': mtr}
    m1 = lin.linarith(w, at, [m401], '1 <_ m', leaves=lvt)
    mtn = stt([mtz, lin.linarith(w, at, [m401], '0 < m', leaves=lvt), w.inst('elnnz')], 'sylanbrc', 'm e. NN')
    v2t, _, _, _ = bwpos(w, at, 'm', mtn)
    nle = lin.linarith(w, at, [m401], '%s < m' % F400, leaves=lvt)
    nle2 = stt([nle, stt([a1(w, at, num.re_nat(w, 400), '%s e. RR' % F400), mtr], 'ltnled', '( %s < m <-> -. m <_ %s )' % (F400, F400))], 'mpbid', '-. m <_ %s' % F400)
    tv = stt([v2t, stt([nle2, w.inst('iffalse')], 'syl', '%s = ( %s / ( m ^ 2 ) )' % (inner, F400))], 'eqtrd', '%s = ( %s / ( m ^ 2 ) )' % (BW('m'), F400))
    M1 = '( m - 1 )'
    m1r = stt([mtr, stt([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % M1)
    m1g = stt([lin.linarith(w, at, [m401], '1 < m', leaves=lvt), stt([stt([], '1red', '1 e. RR'), mtr], 'posdifd', '( 1 < m <-> 0 < %s )' % M1)], 'mpbid', '0 < %s' % M1)
    m1rp = stt([m1r, m1g], 'elrpd', '%s e. RR+' % M1)
    mrp = stt([mtn], 'nnrpd', 'm e. RR+')
    mc = stt([mtr], 'recnd', 'm e. CC'); m1c = stt([m1r], 'recnd', '%s e. CC' % M1)
    D1 = '( ( 1 / %s ) - ( 1 / m ) )' % M1
    sr = stt([m1c, mc, stt([m1rp], 'rpne0d', '%s =/= 0' % M1), stt([mrp], 'rpne0d', 'm =/= 0')], 'subrecd', '%s = ( ( m - %s ) / ( %s x. m ) )' % (D1, M1, M1))
    nc = stt([mc, stt([], '1cnd', '1 e. CC')], 'nncand', '( m - %s ) = 1' % M1)
    d1v = stt([sr, stt([nc], 'oveq1d', '( ( m - %s ) / ( %s x. m ) ) = ( 1 / ( %s x. m ) )' % (M1, M1, M1))], 'eqtrd', '%s = ( 1 / ( %s x. m ) )' % (D1, M1))
    m1le = lin.linarith(w, at, [], '%s <_ m' % M1, leaves={'m': mtr})
    pr = stt([m1r, mtr, mtr, stt([mrp], 'rpge0d', '0 <_ m'), m1le], 'lemul1ad', '( %s x. m ) <_ ( m x. m )' % M1)
    sqv = stt([mc], 'sqvald', '( m ^ 2 ) = ( m x. m )')
    pr2 = stt([pr, sqv], 'breqtrrd', '( %s x. m ) <_ ( m ^ 2 )' % M1)
    rec = stt([pr2, stt([stt([m1rp, mrp], 'rpmulcld', '( %s x. m ) e. RR+' % M1), stt([mrp, a1(w, at, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '( m ^ 2 ) e. RR+')],
                        'lerecd', '( ( %s x. m ) <_ ( m ^ 2 ) <-> ( 1 / ( m ^ 2 ) ) <_ ( 1 / ( %s x. m ) ) )' % (M1, M1))], 'mpbid', '( 1 / ( m ^ 2 ) ) <_ ( 1 / ( %s x. m ) )' % M1)
    rec2 = stt([rec, d1v], 'breqtrrd', '( 1 / ( m ^ 2 ) ) <_ %s' % D1)
    m2rp = stt([mrp, a1(w, at, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '( m ^ 2 ) e. RR+')
    d1r = stt([stt([stt([m1rp], 'rpreccld', '( 1 / %s ) e. RR+' % M1)], 'rpred', '( 1 / %s ) e. RR' % M1),
               stt([stt([mrp], 'rpreccld', '( 1 / m ) e. RR+')], 'rpred', '( 1 / m ) e. RR')], 'resubcld', '%s e. RR' % D1)
    c4r = a1(w, at, num.re_nat(w, 400), '%s e. RR' % F400)
    ml = stt([stt([stt([m2rp], 'rpreccld', '( 1 / ( m ^ 2 ) ) e. RR+')], 'rpred', '( 1 / ( m ^ 2 ) ) e. RR'), d1r, c4r, a1(w, at, num.ge0_nat(w, 400), '0 <_ %s' % F400), rec2],
             'lemul2ad', '( %s x. ( 1 / ( m ^ 2 ) ) ) <_ ( %s x. %s )' % (F400, F400, D1))
    dr_ = stt([stt([c4r], 'recnd', '%s e. CC' % F400), stt([m2rp], 'rpcnd', '( m ^ 2 ) e. CC'), stt([m2rp], 'rpne0d', '( m ^ 2 ) =/= 0')], 'divrecd',
              '( %s / ( m ^ 2 ) ) = ( %s x. ( 1 / ( m ^ 2 ) ) )' % (F400, F400))
    tb = stt([stt([tv, dr_], 'eqtrd', '%s = ( %s x. ( 1 / ( m ^ 2 ) ) )' % (BW('m'), F400)), ml], 'eqbrtrd', '%s <_ ( %s x. %s )' % (BW('m'), F400, D1))
    fzt = st([], 'fzfid', '%s e. Fin' % T_)
    tl1 = st([fzt, stt([tv, stt([c4r, stt([m2rp], 'rpred', '( m ^ 2 ) e. RR'), stt([m2rp], 'rpne0d', '( m ^ 2 ) =/= 0')], 'redivcld', '( %s / ( m ^ 2 ) ) e. RR' % F400)], 'eqeltrd',
                           '%s e. RR' % BW('m')), stt([c4r, d1r], 'remulcld', '( %s x. %s ) e. RR' % (F400, D1)), tb], 'fsumle',
              'sum_ m e. %s %s <_ sum_ m e. %s ( %s x. %s )' % (T_, BW('m'), T_, F400, D1))
    fm = st([fzt, a1(w, a, num.cc_nat(w, 400), '%s e. CC' % F400), stt([d1r], 'recnd', '%s e. CC' % D1)], 'fsummulc2',
            '( %s x. sum_ m e. %s %s ) = sum_ m e. %s ( %s x. %s )' % (F400, T_, D1, T_, F400, D1))
    # telescoping: A ( k ) = 1 / ( k - 1 ), summand in the j-form, then back to m
    Ak = lambda k: '( 1 / ( %s - 1 ) )' % k
    cgk = lambda X: cg(w, Ak('k'), 'k', X)
    t1 = cgk('j'); t2 = cgk('( j + 1 )'); t3 = cgk(F401); t4 = cgk('( %s + 1 )' % MP)
    ak = '( %s /\\ k e. ( %s ... ( %s + 1 ) ) )' % (a, F401, MP)
    sak = mkst(w, ak)
    kin = sak([], 'simpr', 'k e. ( %s ... ( %s + 1 ) )' % (F401, MP))
    kr = sak([sak([kin, w.inst('elfzelz')], 'syl', 'k e. ZZ')], 'zred', 'k e. RR')
    k4 = sak([kin, w.inst('elfzle1')], 'syl', '%s <_ k' % F401)
    km1r = sak([kr, sak([], '1red', '1 e. RR')], 'resubcld', '( k - 1 ) e. RR')
    km1p = lin.linarith(w, ak, [k4], '0 < ( k - 1 )', leaves={'k': kr, '( k - 1 )': km1r})
    akc = sak([sak([sak([km1r, km1p], 'elrpd', '( k - 1 ) e. RR+')], 'rpreccld', '%s e. RR+' % Ak('k'))], 'rpcnd', '%s e. CC' % Ak('k'))
    mp1 = st([mpz], 'peano2zd', '( %s + 1 ) e. ZZ' % MP)
    uz4 = uzd(w, a, a1(w, a, num.z_nat(w, 401), '%s e. ZZ' % F401), mp1, lin.linarith(w, a, [mg0], '%s <_ ( %s + 1 )' % (F401, MP), leaves=lv), F401, '( %s + 1 )' % MP)
    TJ = '( %s - %s )' % (Ak('j'), Ak('( j + 1 )'))
    tel = st([t1, t2, t3, t4, mpz, uz4, akc], 'telfsum', 'sum_ j e. %s %s = ( %s - %s )' % (T_, TJ, Ak(F401), Ak('( %s + 1 )' % MP)))
    # the m-form summand equals the j-form: ( ( j + 1 ) - 1 ) = j
    aj = '( %s /\\ j e. %s )' % (a, T_)
    sj = mkst(w, aj)
    jc = sj([sj([sj([sj([], 'simpr', 'j e. %s' % T_), w.inst('elfzelz')], 'syl', 'j e. ZZ')], 'zred', 'j e. RR')], 'recnd', 'j e. CC')
    pj = sj([jc, sj([], '1cnd', '1 e. CC')], 'pncand', '( ( j + 1 ) - 1 ) = j')
    tj = sj([sj([pj], 'oveq2d', '%s = ( 1 / j )' % Ak('( j + 1 )'))], 'oveq2d', '%s = ( %s - ( 1 / j ) )' % (TJ, Ak('j')))
    tjs = st([tj], 'sumeq2dv', 'sum_ j e. %s %s = sum_ j e. %s ( %s - ( 1 / j ) )' % (T_, TJ, T_, Ak('j')))
    cbm = w.s([cg(w, '( %s - ( 1 / j ) )' % Ak('j'), 'j', 'm')], 'cbvsumv', 'sum_ j e. %s ( %s - ( 1 / j ) ) = sum_ m e. %s %s' % (T_, Ak('j'), T_, D1))
    tsum = st([st([tjs, tel], 'eqtr3d', 'sum_ j e. %s ( %s - ( 1 / j ) ) = ( %s - %s )' % (T_, Ak('j'), Ak(F401), Ak('( %s + 1 )' % MP))),
               a1(w, a, cbm, 'sum_ j e. %s ( %s - ( 1 / j ) ) = sum_ m e. %s %s' % (T_, Ak('j'), T_, D1))], 'eqtr3d',
              'sum_ m e. %s %s = ( %s - %s )' % (T_, D1, Ak(F401), Ak('( %s + 1 )' % MP)))
    # 400 ( 1 / 400 - 1 / MP ) <_ 1
    e40 = a1(w, a, num.sub_nat(w, 401, 1), '( %s - 1 ) = %s' % (F401, F400))
    a40 = st([e40], 'oveq2d', '%s = ( 1 / %s )' % (Ak(F401), F400))
    MQ = Ak('( %s + 1 )' % MP)
    mqp = st([st([st([mp1], 'zred', '( %s + 1 ) e. RR' % MP), st([], '1red', '1 e. RR')], 'resubcld', '( ( %s + 1 ) - 1 ) e. RR' % MP),
              lin.linarith(w, a, [mg0], '0 < ( ( %s + 1 ) - 1 )' % MP, leaves={'M': mr, '( ( %s + 1 ) - 1 )' % MP: st([st([st([mp1], 'zred', '( %s + 1 ) e. RR' % MP), st([], '1red', '1 e. RR')], 'resubcld', '( ( %s + 1 ) - 1 ) e. RR' % MP)], 'idi', '( ( %s + 1 ) - 1 ) e. RR' % MP)})], 'elrpd', '( ( %s + 1 ) - 1 ) e. RR+' % MP)
    mq0 = st([st([mqp], 'rpreccld', '%s e. RR+' % MQ)], 'rpge0d', '0 <_ %s' % MQ)
    mqr = st([st([mqp], 'rpreccld', '%s e. RR+' % MQ)], 'rpred', '%s e. RR' % MQ)
    SD = 'sum_ m e. %s %s' % (T_, D1)
    mqr_ = st([st([mp1], 'zred', '( %s + 1 ) e. RR' % MP), st([], '1red', '1 e. RR')], 'resubcld', '( ( %s + 1 ) - 1 ) e. RR' % MP)
    r400 = a1(w, a, num.re_nat(w, 400), '%s e. RR' % F400)
    i400 = st([r400, a1(w, a, num.ne0_nat(w, 400), '%s =/= 0' % F400)], 'rereccld', '( 1 / %s ) e. RR' % F400)
    a401r = st([a40, i400], 'eqeltrd', '%s e. RR' % Ak(F401))
    SM = 'sum_ m e. ( 1 ... M ) %s' % BW('m'); SP = 'sum_ m e. %s %s' % (U, BW('m')); SH = 'sum_ m e. %s %s' % (H, BW('m'))
    ST = 'sum_ m e. %s %s' % (T_, BW('m')); S4 = 'sum_ m e. %s ( %s x. %s )' % (T_, F400, D1)
    LG = '( log ` %s )' % F400
    # reals of the sums
    am2 = '( %s /\\ m e. ( 1 ... M ) )' % a
    sm2 = mkst(w, am2)
    mnn2 = sm2([sm2([], 'simpr', 'm e. ( 1 ... M )'), w.inst('elfznn')], 'syl', 'm e. NN')
    _, bwr2, _, _ = bwpos(w, am2, 'm', mnn2)
    smr = st([st([], 'fzfid', '( 1 ... M ) e. Fin'), bwr2], 'fsumrecl', '%s e. RR' % SM)
    spr = st([fz, bwr], 'fsumrecl', '%s e. RR' % SP)
    _, bwrh, _, _ = bwpos(w, ah, 'm', mhn)
    shr = st([st([], 'fzfid', '%s e. Fin' % H), bwrh], 'fsumrecl', '%s e. RR' % SH)
    _, bwrt, _, _ = bwpos(w, at, 'm', mtn)
    str_ = st([fzt, bwrt], 'fsumrecl', '%s e. RR' % ST)
    s4r = st([fzt, stt([c4r, d1r], 'remulcld', '( %s x. %s ) e. RR' % (F400, D1))], 'fsumrecl', '%s e. RR' % S4)
    sdr = st([fzt, d1r], 'fsumrecl', '%s e. RR' % SD)
    lgr = st([a1(w, a, num.rp_nat(w, 400), '%s e. RR+' % F400)], 'relogcld', '%s e. RR' % LG)
    leaves = {SM: smr, SP: spr, SH: shr, ST: str_, S4: s4r, SD: sdr, LG: lgr, MQ: mqr, Ak(F401): a401r}
    fin = lin.linarith(w, a, [s1, fs, hd, tl1, fm, tsum, a40, mq0], '%s <_ ( 2 + %s )' % (SM, LG), leaves=leaves)
    w.qed([fin], 'idi', S_['gf2bsum'])
    return w


FIB = lambda m: '{ j e. S | ( G ` j ) = %s }' % m
S_['gf2fib'] = ('( ( ( S e. Fin /\\ G : S --> NN0 ) /\\ ( ( # ` %s ) <_ 1 /\\ A. x e. NN ( # ` %s ) <_ 2 ) ) -> '
                'sum_ k e. S %s <_ ( 5 + ( 2 x. ( log ` %s ) ) ) )') % (FIB('0'), FIB('x'), BW('( G ` k )'), F400)


def bwnn0(w, ante, x, nn0st):
    """( ante -> BW(x) e. RR ), ( ante -> 0 <_ BW(x) ) for x e. NN0"""
    st = mkst(w, ante)
    inner = 'if ( %s <_ %s , ( 1 / %s ) , ( %s / ( %s ^ 2 ) ) )' % (x, F400, x, F400, x)
    v = bwv(w, ante, x, nn0st)
    a0 = '( %s /\\ %s = 0 )' % (ante, x)
    t = a1(w, a0, w.s([], '1rp', '1 e. RR+'), '1 e. RR+')
    an = '( %s /\\ -. %s = 0 )' % (ante, x)
    sa = mkst(w, an)
    ne = sa([sa([], 'simpr', '-. %s = 0' % x)], 'neqned', '%s =/= 0' % x)
    xn = sa([sa([lift(w, nn0st, an), ne], 'jca', '( %s e. NN0 /\\ %s =/= 0 )' % (x, x)), w.inst('elnnne0')], 'sylibr', '%s e. NN' % x)
    xrp = sa([xn], 'nnrpd', '%s e. RR+' % x)
    r1 = sa([xrp], 'rpreccld', '( 1 / %s ) e. RR+' % x)
    r2 = sa([a1(w, an, num.rp_nat(w, 400), '%s e. RR+' % F400), sa([xrp, a1(w, an, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % x)],
            'rpdivcld', '( %s / ( %s ^ 2 ) ) e. RR+' % (F400, x))
    f = sa([r1, r2], 'ifcld', '%s e. RR+' % inner)
    ic = st([t, f], 'ifclda', '%s e. RR+' % BWB(x))
    bp = st([v, ic], 'eqeltrd', '%s e. RR+' % BW(x))
    return st([bp], 'rpred', '%s e. RR' % BW(x)), st([bp], 'rpge0d', '0 <_ %s' % BW(x))


def gf2fib():
    w = W('gf2fib', 'Row sum of bin weights over a set of points, at most one in bin 0 and at most two in every other bin: '
                    '` sum_ k beta ( g ( k ) ) <_ 5 + 2 log 400 ` (the fibre count of Lean ` row_sum_le ` ; ~ sumite , ~ fsumcom , ~ sumhash , ~ gf2bsum ).')
    a = split_imp(S_['gf2fib'])[0]
    st = mkst(w, a)
    sf = st([], 'simpll', 'S e. Fin'); gf = st([], 'simplr', 'G : S --> NN0')
    h0 = st([], 'simprl', '( # ` %s ) <_ 1' % FIB('0')); h2 = st([], 'simprr', 'A. x e. NN ( # ` %s ) <_ 2' % FIB('x'))
    MS = 'sum_ i e. S ( G ` i )'
    ai = '( %s /\\ i e. S )' % a
    si = mkst(w, ai)
    gi = si([lift(w, gf, ai), si([], 'simpr', 'i e. S')], 'ffvelcdmd', '( G ` i ) e. NN0')
    mn0 = st([sf, gi], 'fsumnn0cl', '%s e. NN0' % MS)
    R = '( 0 ... %s )' % MS
    ak = '( %s /\\ k e. S )' % a
    sk = mkst(w, ak)
    kin = sk([], 'simpr', 'k e. S')
    gk = sk([lift(w, gf, ak), kin], 'ffvelcdmd', '( G ` k ) e. NN0')
    aki = '( %s /\\ i e. S )' % ak
    ski = mkst(w, aki)
    gki = ski([lift(w, gf, aki), ski([], 'simpr', 'i e. S')], 'ffvelcdmd', '( G ` i ) e. NN0')
    sub_i = w.s([], 'fveq2', '( i = k -> ( G ` i ) = ( G ` k ) )')
    gle = sk([lift(w, sf, ak), ski([gki], 'nn0red', '( G ` i ) e. RR'), ski([gki], 'nn0ge0d', '0 <_ ( G ` i )'), sub_i, kin], 'fsumge1', '( G ` k ) <_ %s' % MS)
    gkin = sk([a1(w, ak, w.s([], '0z', '0 e. ZZ'), '0 e. ZZ'), sk([lift(w, mn0, ak)], 'nn0zd', '%s e. ZZ' % MS), sk([gk], 'nn0zd', '( G ` k ) e. ZZ'),
               sk([gk], 'nn0ge0d', '0 <_ ( G ` k )'), gle], 'elfzd', '( G ` k ) e. %s' % R)
    fz = st([], 'fzfid', '%s e. Fin' % R)
    BWm = BW('m'); BWG = BW('( G ` k )')
    IF = 'if ( m = ( G ` k ) , %s , 0 )' % BWm
    bgr, bg0 = bwnn0(w, ak, '( G ` k )', gk)
    se = sk([w.s([], 'fveq2', '( m = ( G ` k ) -> %s = %s )' % (BWm, BWG)), lift(w, fz, ak), gkin, sk([bgr], 'recnd', '%s e. CC' % BWG)], 'sumite',
            'sum_ m e. %s %s = %s' % (R, IF, BWG))
    s3 = st([sk([se], 'eqcomd', '%s = sum_ m e. %s %s' % (BWG, R, IF))], 'sumeq2dv', 'sum_ k e. S %s = sum_ k e. S sum_ m e. %s %s' % (BWG, R, IF))
    akm = '( %s /\\ ( k e. S /\\ m e. %s ) )' % (a, R)
    skm = mkst(w, akm)
    mn0k = skm([skm([], 'simprr', 'm e. %s' % R), w.inst('elfznn0')], 'syl', 'm e. NN0')
    bmr, _ = bwnn0(w, akm, 'm', mn0k)
    ifc = skm([skm([bmr], 'recnd', '%s e. CC' % BWm), skm([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF)
    s4 = st([sf, fz, ifc], 'fsumcom', 'sum_ k e. S sum_ m e. %s %s = sum_ m e. %s sum_ k e. S %s' % (R, IF, R, IF))
    # (5) per m: sum_ k IF = BW ( m ) # Fm
    am = '( %s /\\ m e. %s )' % (a, R)
    sm = mkst(w, am)
    mn0m = sm([sm([], 'simpr', 'm e. %s' % R), w.inst('elfznn0')], 'syl', 'm e. NN0')
    bmr_m, bm0_m = bwnn0(w, am, 'm', mn0m)
    bmc_m = sm([bmr_m], 'recnd', '%s e. CC' % BWm)
    FM = FIB('m'); IND = 'if ( k e. %s , 1 , 0 )' % FM
    amk = '( %s /\\ k e. S )' % am
    smk = mkst(w, amk)
    rsub = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( G ` j ) = ( G ` k ) )')], 'eqeq1d', '( j = k -> ( ( G ` j ) = m <-> ( G ` k ) = m ) )')], 'idi',
               '( j = k -> ( ( G ` j ) = m <-> ( G ` k ) = m ) )')
    rb = w.s([rsub], 'elrab', '( k e. %s <-> ( k e. S /\\ ( G ` k ) = m ) )' % FM)
    ib = smk([smk([], 'simpr', 'k e. S'), w.inst('ibar')], 'syl', '( ( G ` k ) = m <-> ( k e. S /\\ ( G ` k ) = m ) )')
    e1 = smk([a1(w, amk, rb, '( k e. %s <-> ( k e. S /\\ ( G ` k ) = m ) )' % FM), ib], 'bitr4d', '( k e. %s <-> ( G ` k ) = m )' % FM)
    e2 = a1(w, amk, w.s([], 'eqcom', '( m = ( G ` k ) <-> ( G ` k ) = m )'), '( m = ( G ` k ) <-> ( G ` k ) = m )')
    e3 = smk([e2, e1], 'bitr4d', '( m = ( G ` k ) <-> k e. %s )' % FM)
    ib2 = smk([e3], 'ifbid', '%s = if ( k e. %s , %s , 0 )' % (IF, FM, BWm))
    bmc_mk = lift(w, bmc_m, amk)
    at = '( %s /\\ k e. %s )' % (amk, FM)
    sat = mkst(w, at)
    ct = sat([sat([sat([], 'simpr', 'k e. %s' % FM), w.inst('iftrue')], 'syl', 'if ( k e. %s , %s , 0 ) = %s' % (FM, BWm, BWm)),
              sat([sat([sat([sat([], 'simpr', 'k e. %s' % FM), w.inst('iftrue')], 'syl', '%s = 1' % IND)], 'oveq2d', '( %s x. %s ) = ( %s x. 1 )' % (BWm, IND, BWm)),
                   sat([lift(w, bmc_m, at)], 'mulridd', '( %s x. 1 ) = %s' % (BWm, BWm))], 'eqtrd', '( %s x. %s ) = %s' % (BWm, IND, BWm))], 'eqtr4d',
             'if ( k e. %s , %s , 0 ) = ( %s x. %s )' % (FM, BWm, BWm, IND))
    af = '( %s /\\ -. k e. %s )' % (amk, FM)
    saf = mkst(w, af)
    cf = saf([saf([saf([], 'simpr', '-. k e. %s' % FM), w.inst('iffalse')], 'syl', 'if ( k e. %s , %s , 0 ) = 0' % (FM, BWm)),
              saf([saf([saf([saf([], 'simpr', '-. k e. %s' % FM), w.inst('iffalse')], 'syl', '%s = 0' % IND)], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (BWm, IND, BWm)),
                   saf([lift(w, bmc_m, af)], 'mul01d', '( %s x. 0 ) = 0' % BWm)], 'eqtrd', '( %s x. %s ) = 0' % (BWm, IND))], 'eqtr4d',
             'if ( k e. %s , %s , 0 ) = ( %s x. %s )' % (FM, BWm, BWm, IND))
    cc = w.s([ct, cf], 'pm2.61dan', '( %s -> if ( k e. %s , %s , 0 ) = ( %s x. %s ) )' % (amk, FM, BWm, BWm, IND))
    pw = smk([ib2, cc], 'eqtrd', '%s = ( %s x. %s )' % (IF, BWm, IND))
    sw = sm([pw], 'sumeq2dv', 'sum_ k e. S %s = sum_ k e. S ( %s x. %s )' % (IF, BWm, IND))
    indc = smk([smk([], '1cnd', '1 e. CC'), smk([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IND)
    fm = sm([lift(w, sf, am), bmc_m, indc], 'fsummulc2', '( %s x. sum_ k e. S %s ) = sum_ k e. S ( %s x. %s )' % (BWm, IND, BWm, IND))
    sh = sm([lift(w, sf, am), a1(w, am, w.s([], 'ssrab2', '%s C_ S' % FM), '%s C_ S' % FM), w.inst('sumhash')], 'syl2anc', 'sum_ k e. S %s = ( # ` %s )' % (IND, FM))
    XM = '( %s x. ( # ` %s ) )' % (BWm, FM)
    pm = sm([sm([sw, fm], 'eqtr4d', 'sum_ k e. S %s = ( %s x. sum_ k e. S %s )' % (IF, BWm, IND)), sm([sh], 'oveq2d', '( %s x. sum_ k e. S %s ) = %s' % (BWm, IND, XM))], 'eqtrd',
            'sum_ k e. S %s = %s' % (IF, XM))
    s6 = st([pm], 'sumeq2dv', 'sum_ m e. %s sum_ k e. S %s = sum_ m e. %s %s' % (R, IF, R, XM))
    # (7) split off m = 0
    hfin = lambda ante, m: mkst(w, ante)([lift(w, sf, ante), a1(w, ante, w.s([], 'ssrab2', '%s C_ S' % FIB(m)), '%s C_ S' % FIB(m))], 'ssfid', '%s e. Fin' % FIB(m))
    hr = lambda ante, m: mkst(w, ante)([mkst(w, ante)([hfin(ante, m), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % FIB(m))], 'nn0red', '( # ` %s ) e. RR' % FIB(m))
    xmc = sm([bmr_m, hr(am, 'm')], 'remulcld', '%s e. RR' % XM)
    X0 = '( %s x. ( # ` %s ) )' % (BW('0'), FIB('0'))
    s0sub = cg(w, XM, 'm', '0')
    uz0 = st([mn0, w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '%s e. ( ZZ>= ` 0 )' % MS)
    f1p = st([uz0, sm([xmc], 'recnd', '%s e. CC' % XM), s0sub], 'fsum1p', 'sum_ m e. %s %s = ( %s + sum_ m e. ( ( 0 + 1 ) ... %s ) %s )' % (R, XM, X0, MS, XM))
    R1 = '( 1 ... %s )' % MS
    rr = st([a1(w, a, w.s([], '0p1e1', '( 0 + 1 ) = 1'), '( 0 + 1 ) = 1')], 'oveq1d', '( ( 0 + 1 ) ... %s ) = %s' % (MS, R1))
    f1p2 = st([f1p, st([st([rr], 'sumeq1d', 'sum_ m e. ( ( 0 + 1 ) ... %s ) %s = sum_ m e. %s %s' % (MS, XM, R1, XM))], 'oveq2d',
                       '( %s + sum_ m e. ( ( 0 + 1 ) ... %s ) %s ) = ( %s + sum_ m e. %s %s )' % (X0, MS, XM, X0, R1, XM))], 'eqtrd',
              'sum_ m e. %s %s = ( %s + sum_ m e. %s %s )' % (R, XM, X0, R1, XM))
    # (8) the zero bin
    b0v = bwv(w, a, '0', a1(w, a, w.s([], '0nn0', '0 e. NN0'), '0 e. NN0'))
    b01 = st([b0v, st([a1(w, a, w.s([], 'eqid', '0 = 0'), '0 = 0'), w.inst('iftrue')], 'syl', '%s = 1' % BWB('0'))], 'eqtrd', '%s = 1' % BW('0'))
    x0v = st([st([b01], 'oveq1d', '%s = ( 1 x. ( # ` %s ) )' % (X0, FIB('0'))), st([st([hr(a, '0')], 'recnd', '( # ` %s ) e. CC' % FIB('0'))], 'mullidd',
                                                                                                             '( 1 x. ( # ` %s ) ) = ( # ` %s )' % (FIB('0'), FIB('0')))], 'eqtrd',
             '%s = ( # ` %s )' % (X0, FIB('0')))
    # (9) the other bins
    a1m = '( %s /\\ m e. %s )' % (a, R1)
    s1m = mkst(w, a1m)
    m1n = s1m([s1m([], 'simpr', 'm e. %s' % R1), w.inst('elfznn')], 'syl', 'm e. NN')
    idxm = w.s([], 'id', '( x = m -> x = m )')
    xs, _ = w.wcongr('( # ` %s ) <_ 2' % FIB('x'), {'x': 'm'}, 'x = m', {'x': idxm})
    hb = s1m([xs, lift(w, h2, a1m), m1n], 'rspcdva', '( # ` %s ) <_ 2' % FM)
    b1r, b10 = bwnn0(w, a1m, 'm', s1m([m1n], 'nnnn0d', 'm e. NN0'))
    xm2 = s1m([hr(a1m, 'm'), a1(w, a1m, w.s([], '2re', '2 e. RR'), '2 e. RR'), b1r, b10, hb], 'lemul2ad', '%s <_ ( %s x. 2 )' % (XM, BWm))
    fz1 = st([], 'fzfid', '%s e. Fin' % R1)
    sl = st([fz1, s1m([b1r, hr(a1m, 'm')], 'remulcld', '%s e. RR' % XM), s1m([b1r, a1(w, a1m, w.s([], '2re', '2 e. RR'), '2 e. RR')], 'remulcld', '( %s x. 2 ) e. RR' % BWm), xm2],
            'fsumle', 'sum_ m e. %s %s <_ sum_ m e. %s ( %s x. 2 )' % (R1, XM, R1, BWm))
    SW = 'sum_ m e. %s %s' % (R1, BWm)
    fm1 = st([fz1, a1(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), s1m([b1r], 'recnd', '%s e. CC' % BWm)], 'fsummulc1', '( %s x. 2 ) = sum_ m e. %s ( %s x. 2 )' % (SW, R1, BWm))
    bs = st([mn0, w.inst('gf2bsum')], 'syl', '%s <_ ( 2 + ( log ` %s ) )' % (SW, F400))
    # (10) linear combination
    SB = 'sum_ k e. S %s' % BWG; SC = 'sum_ k e. S sum_ m e. %s %s' % (R, IF); SC2 = 'sum_ m e. %s sum_ k e. S %s' % (R, IF)
    SX = 'sum_ m e. %s %s' % (R, XM); SX1 = 'sum_ m e. %s %s' % (R1, XM); S2 = 'sum_ m e. %s ( %s x. 2 )' % (R1, BWm)
    LG = '( log ` %s )' % F400
    sbr = st([sf, bgr], 'fsumrecl', '%s e. RR' % SB)
    sxr = st([fz, xmc], 'fsumrecl', '%s e. RR' % SX)
    sx1r = st([fz1, s1m([b1r, hr(a1m, 'm')], 'remulcld', '%s e. RR' % XM)], 'fsumrecl', '%s e. RR' % SX1)
    s2r = st([fz1, s1m([b1r, a1(w, a1m, w.s([], '2re', '2 e. RR'), '2 e. RR')], 'remulcld', '( %s x. 2 ) e. RR' % BWm)], 'fsumrecl', '%s e. RR' % S2)
    swr = st([fz1, b1r], 'fsumrecl', '%s e. RR' % SW)
    x0r = st([st([x0v], 'eqcomd', '( # ` %s ) = %s' % (FIB('0'), X0)), hr(a, '0')], 'eqeltrrd', '%s e. RR' % X0)
    lgr = st([a1(w, a, num.rp_nat(w, 400), '%s e. RR+' % F400)], 'relogcld', '%s e. RR' % LG)
    eqs = st([st([s3, s4], 'eqtrd', '%s = %s' % (SB, SC2)), s6], 'eqtrd', '%s = %s' % (SB, SX))
    leaves = {SB: sbr, SX: sxr, SX1: sx1r, S2: s2r, SW: swr, X0: x0r, LG: lgr, '( # ` %s )' % FIB('0'): hr(a, '0')}
    fin = lin.linarith(w, a, [eqs, f1p2, x0v, h0, sl, fm1, bs], '%s <_ ( 5 + ( 2 x. %s ) )' % (SB, LG), leaves=leaves)
    w.qed([fin], 'idi', S_['gf2fib'])
    return w


YD = '( log ` D )'
TH = '( abs ` ( Im ` V ) )'
FLM = '( |_ ` ( %s x. %s ) )' % (TH, YD)
G1V = L.G1F('-u V')
S_['gf2g1bw'] = ('( ( ( D e. RR /\\ 1 < D /\\ 1 <_ %s ) /\\ ( V e. CC /\\ ( 0 <_ ( Re ` V ) /\\ ( Re ` V ) <_ ( 1 / ; 5 0 ) ) ) ) -> '
                 '( abs ` %s ) <_ ( ( %s x. %s ) x. %s ) )') % (YD, G1V, L.C7, YD, BW(FLM))


def gf2g1bw():
    w = W('gf2g1bw', 'Each ` G_1 ` -value of a row is bounded through its bin: with ` m = |_ ( | Im s | L ) ` , ` | G_1 ( - s ) | <_ C_7 L beta ( m ) ` '
                     '(Lean ` norm_G1_le_binWeight ` ; ~ gf1g1b ).')
    a = split_imp(S_['gf2g1bw'])[0]
    st = mkst(w, a)
    C7 = L.C7
    h = st([], 'simpl', '( D e. RR /\\ 1 < D /\\ 1 <_ %s )' % YD)
    dr = st([h], 'simp1d', 'D e. RR'); d1 = st([h], 'simp2d', '1 < D'); y1 = st([h], 'simp3d', '1 <_ %s' % YD)
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    yr = st([drp], 'relogcld', '%s e. RR' % YD)
    vp = st([], 'simpr', '( V e. CC /\\ ( 0 <_ ( Re ` V ) /\\ ( Re ` V ) <_ ( 1 / ; 5 0 ) ) )')
    vc = st([vp], 'simpld', 'V e. CC')
    rv0 = st([st([vp], 'simprd', '( 0 <_ ( Re ` V ) /\\ ( Re ` V ) <_ ( 1 / ; 5 0 ) )')], 'simpld', '0 <_ ( Re ` V )')
    rv1 = st([st([vp], 'simprd', '( 0 <_ ( Re ` V ) /\\ ( Re ` V ) <_ ( 1 / ; 5 0 ) )')], 'simprd', '( Re ` V ) <_ ( 1 / ; 5 0 )')
    lm0v = st([drp, litr(w, a, '( 3 / 5 )')], 'logcxpd', '%s = ( ( 3 / 5 ) x. %s )' % (L.LM0, YD))
    lxpv = st([drp, litr(w, a, '( 6 / 5 )')], 'logcxpd', '%s = ( ( 6 / 5 ) x. %s )' % (L.LXP, YD))
    lmr = st([lm0v, st([litr(w, a, '( 3 / 5 )'), yr], 'remulcld', '( ( 3 / 5 ) x. %s ) e. RR' % YD)], 'eqeltrd', '%s e. RR' % L.LM0)
    lxr = st([lxpv, st([litr(w, a, '( 6 / 5 )'), yr], 'remulcld', '( ( 6 / 5 ) x. %s ) e. RR' % YD)], 'eqeltrd', '%s e. RR' % L.LXP)
    ypos = lin.linarith(w, a, [y1], '0 < %s' % YD, leaves={YD: yr})
    yrp = st([yr, ypos], 'elrpd', '%s e. RR+' % YD)
    ELLD = L.ELLD
    elr = st([litr(w, a, '( 1 / ; ; 1 0 0 )'), yr], 'remulcld', '%s e. RR' % ELLD)
    elrp = st([st([litr(w, a, '( 1 / ; ; 1 0 0 )'), litle(w, a, '0', '( 1 / ; ; 1 0 0 )', strict=True)], 'elrpd', '( 1 / ; ; 1 0 0 ) e. RR+'), yrp], 'rpmulcld', '%s e. RR+' % ELLD)
    lv = {YD: yr, L.LM0: lmr, L.LXP: lxr}
    a0 = lin.linarith(w, a, [lm0v, y1], '0 <_ %s' % L.LM0, leaves=lv)
    ab = lin.linarith(w, a, [lm0v, lxpv, y1], '%s <_ %s' % (L.LM0, L.LXP), leaves=lv)
    sm = lin.linarith(w, a, [lm0v, lxpv, y1], '( ( %s + %s ) + ( 2 x. %s ) ) <_ ( ( 5 / 2 ) x. %s )' % (L.LXP, L.LM0, ELLD, YD), leaves=lv)
    zc = st([vc], 'negcld', '-u V e. CC')
    rz = st([vc, w.inst('reneg')], 'syl', '( Re ` -u V ) = -u ( Re ` V )')
    rvr = st([vc], 'recld', '( Re ` V ) e. RR')
    rzr = st([zc], 'recld', '( Re ` -u V ) e. RR')
    lvz = {'( Re ` V )': rvr, '( Re ` -u V )': rzr}
    z1 = lin.linarith(w, a, [rz, rv1], '-u ( 1 / ; 5 0 ) <_ ( Re ` -u V )', leaves=lvz)
    z2 = lin.linarith(w, a, [rz, rv0], '( Re ` -u V ) <_ 0', leaves=lvz)
    H1 = '( ( ( %s e. RR /\\ %s e. RR ) /\\ ( 0 <_ %s /\\ %s <_ %s ) ) /\\ ( %s e. RR+ /\\ ( %s e. RR /\\ 1 <_ %s ) /\\ ( ( %s + %s ) + ( 2 x. %s ) ) <_ ( ( 5 / 2 ) x. %s ) ) )' % (
        L.LM0, L.LXP, L.LM0, L.LM0, L.LXP, ELLD, YD, YD, L.LXP, L.LM0, ELLD, YD)
    hh = st([st([st([st([lmr, lxr], 'jca', '( %s e. RR /\\ %s e. RR )' % (L.LM0, L.LXP)), st([a0, ab], 'jca', '( 0 <_ %s /\\ %s <_ %s )' % (L.LM0, L.LM0, L.LXP))], 'jca',
                    '( ( %s e. RR /\\ %s e. RR ) /\\ ( 0 <_ %s /\\ %s <_ %s ) )' % (L.LM0, L.LXP, L.LM0, L.LM0, L.LXP)),
                 st([elrp, st([yr, y1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (YD, YD)), sm], '3jca',
                    '( %s e. RR+ /\\ ( %s e. RR /\\ 1 <_ %s ) /\\ ( ( %s + %s ) + ( 2 x. %s ) ) <_ ( ( 5 / 2 ) x. %s ) )' % (ELLD, YD, YD, L.LXP, L.LM0, ELLD, YD))], 'jca', H1),
             st([zc, z1, z2], '3jca', '( -u V e. CC /\\ -u ( 1 / ; 5 0 ) <_ ( Re ` -u V ) /\\ ( Re ` -u V ) <_ 0 )')], 'jca',
            '( %s /\\ ( -u V e. CC /\\ -u ( 1 / ; 5 0 ) <_ ( Re ` -u V ) /\\ ( Re ` -u V ) <_ 0 ) )' % H1)
    G = G1V; g = '( abs ` %s )' % G
    TZ = '( abs ` ( Im ` -u V ) )'
    E = '( exp ` ( -u %s / 2 ) )' % TZ
    gb = st([hh, w.inst('gf1g1b')], 'syl', '( %s <_ ( ( %s x. %s ) x. %s ) /\\ ( %s x. %s ) <_ ( %s x. %s ) /\\ ( ( ( ( Im ` -u V ) ^ 2 ) x. %s ) x. %s ) <_ ( ( 4 x. %s ) x. %s ) )' % (
        g, C7, E, YD, TZ, g, C7, E, ELLD, g, C7, E))
    b1 = st([gb], 'simp1d', '%s <_ ( ( %s x. %s ) x. %s )' % (g, C7, E, YD))
    b2 = st([gb], 'simp2d', '( %s x. %s ) <_ ( %s x. %s )' % (TZ, g, C7, E))
    b3 = st([gb], 'simp3d', '( ( ( ( Im ` -u V ) ^ 2 ) x. %s ) x. %s ) <_ ( ( 4 x. %s ) x. %s )' % (ELLD, g, C7, E))
    ivr = st([vc], 'imcld', '( Im ` V ) e. RR')
    imz = st([vc, w.inst('imneg')], 'syl', '( Im ` -u V ) = -u ( Im ` V )')
    tz = st([st([imz], 'fveq2d', '%s = ( abs ` -u ( Im ` V ) )' % TZ), st([st([ivr], 'recnd', '( Im ` V ) e. CC'), w.inst('absneg')], 'syl', '( abs ` -u ( Im ` V ) ) = %s' % TH)],
            'eqtrd', '%s = %s' % (TZ, TH))
    iz2 = st([st([imz], 'oveq1d', '( ( Im ` -u V ) ^ 2 ) = ( -u ( Im ` V ) ^ 2 )'), st([st([ivr], 'recnd', '( Im ` V ) e. CC')], 'sqnegd', '( -u ( Im ` V ) ^ 2 ) = ( ( Im ` V ) ^ 2 )')],
             'eqtrd', '( ( Im ` -u V ) ^ 2 ) = ( ( Im ` V ) ^ 2 )')
    b2t = st([st([st([tz], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (TZ, g, TH, g)), b2], 'eqbrtrrd', '( %s x. %s ) <_ ( %s x. %s )' % (TH, g, C7, E))], 'idi', '( %s x. %s ) <_ ( %s x. %s )' % (TH, g, C7, E))
    Q = '( ( ( ( Im ` V ) ^ 2 ) x. %s ) x. %s )' % (ELLD, g)
    b3t = st([st([st([st([iz2], 'oveq1d', '( ( ( Im ` -u V ) ^ 2 ) x. %s ) = ( ( ( Im ` V ) ^ 2 ) x. %s )' % (ELLD, ELLD))], 'oveq1d',
                     '( ( ( ( Im ` -u V ) ^ 2 ) x. %s ) x. %s ) = %s' % (ELLD, g, Q))], 'eqcomd', '%s = ( ( ( ( Im ` -u V ) ^ 2 ) x. %s ) x. %s )' % (Q, ELLD, g)), b3],
              'eqbrtrd', '%s <_ ( ( 4 x. %s ) x. %s )' % (Q, C7, E))
    # E <_ 1, C7 >_ 0
    tzr = st([st([zc], 'imcld', '( Im ` -u V ) e. RR')], 'recnd', '( Im ` -u V ) e. CC')
    tzre = st([tzr], 'abscld', '%s e. RR' % TZ)
    tz0 = st([tzr], 'absge0d', '0 <_ %s' % TZ)
    arg = '( -u %s / 2 )' % TZ
    argr = st([st([tzre], 'renegcld', '-u %s e. RR' % TZ), a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), a1(w, a, w.s([], '2ne0', '2 =/= 0'), '2 =/= 0')], 'redivcld', '%s e. RR' % arg)
    arg0 = lin.linarith(w, a, [tz0], '%s <_ 0' % arg, leaves={TZ: tzre})
    el = st([arg0, st([argr, st([], '0red', '0 e. RR'), w.inst('efle')], 'syl2anc', '( %s <_ 0 <-> %s <_ ( exp ` 0 ) )' % (arg, E))], 'mpbid', '%s <_ ( exp ` 0 )' % E)
    e1 = st([el, a1(w, a, w.s([], 'ef0', '( exp ` 0 ) = 1'), '( exp ` 0 ) = 1')], 'breqtrd', '%s <_ 1' % E)
    er = st([argr], 'reefcld', '%s e. RR' % E)
    c7r = a1(w, a, num.re_nat(w, 8337480), '%s e. RR' % C7)
    c70 = a1(w, a, num.ge0_nat(w, 8337480), '0 <_ %s' % C7)
    ce = st([er, st([], '1red', '1 e. RR'), c7r, c70, e1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 1 )' % (C7, E, C7))
    c71 = st([st([c7r], 'recnd', '%s e. CC' % C7)], 'mulridd', '( %s x. 1 ) = %s' % (C7, C7))
    ce2 = st([ce, c71], 'breqtrd', '( %s x. %s ) <_ %s' % (C7, E, C7))
    # g facts
    gcc = st([b1, w.inst('z6absle')], 'syl', '%s e. CC' % G)
    gr = st([gcc], 'abscld', '%s e. RR' % g); g0 = st([gcc], 'absge0d', '0 <_ %s' % g)
    thre = st([st([ivr], 'recnd', '( Im ` V ) e. CC')], 'abscld', '%s e. RR' % TH)
    th0 = st([st([ivr], 'recnd', '( Im ` V ) e. CC')], 'absge0d', '0 <_ %s' % TH)
    TY = '( %s x. %s )' % (TH, YD)
    tyr = st([thre, yr], 'remulcld', '%s e. RR' % TY)
    ty0 = st([thre, yr, th0, st([yrp], 'rpge0d', '0 <_ %s' % YD)], 'mulge0d', '0 <_ %s' % TY)
    mn0 = st([st([tyr, ty0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (TY, TY)), w.inst('flge0nn0')], 'syl', '%s e. NN0' % FLM)
    mle = st([tyr, w.inst('flle')], 'syl', '%s <_ %s' % (FLM, TY))
    mr = st([mn0], 'nn0red', '%s e. RR' % FLM); m0 = st([mn0], 'nn0ge0d', '0 <_ %s' % FLM)
    bv = bwv(w, a, FLM, mn0)
    TT = lambda X: '( ( %s x. %s ) x. %s )' % (C7, YD, X)
    c7y = st([c7r, yr], 'remulcld', '( %s x. %s ) e. RR' % (C7, YD))
    # case m = 0
    aA = '( %s /\\ %s = 0 )' % (a, FLM)
    sA = mkst(w, aA); LA = lambda s_: lift(w, s_, aA)
    bvA = sA([LA(bv), sA([sA([], 'simpr', '%s = 0' % FLM), w.inst('iftrue')], 'syl', '%s = 1' % BWB(FLM))], 'eqtrd', '%s = 1' % BW(FLM))
    tA = sA([sA([bvA], 'oveq2d', '%s = %s' % (TT(BW(FLM)), TT('1'))), sA([sA([LA(c7y)], 'recnd', '( %s x. %s ) e. CC' % (C7, YD))], 'mulridd', '%s = ( %s x. %s )' % (TT('1'), C7, YD))],
            'eqtrd', '%s = ( %s x. %s )' % (TT(BW(FLM)), C7, YD))
    cey = sA([LA(st([c7r, er], 'remulcld', '( %s x. %s ) e. RR' % (C7, E))), LA(c7r), LA(yr), LA(st([yrp], 'rpge0d', '0 <_ %s' % YD)), LA(ce2)], 'lemul1ad',
             '( ( %s x. %s ) x. %s ) <_ ( %s x. %s )' % (C7, E, YD, C7, YD))
    cA = sA([sA([LA(gr), LA(st([st([c7r, er], 'remulcld', '( %s x. %s ) e. RR' % (C7, E)), yr], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (C7, E, YD))), LA(c7y), LA(b1), cey], 'letrd', '%s <_ ( %s x. %s )' % (g, C7, YD)), tA], 'breqtrrd', '%s <_ %s' % (g, TT(BW(FLM))))
    # m =/= 0 : m e. RR+
    aN = '( %s /\\ -. %s = 0 )' % (a, FLM)
    sN = mkst(w, aN); LN = lambda s_: lift(w, s_, aN)
    mnn = sN([sN([LN(mn0), sN([sN([], 'simpr', '-. %s = 0' % FLM)], 'neqned', '%s =/= 0' % FLM)], 'jca', '( %s e. NN0 /\\ %s =/= 0 )' % (FLM, FLM)), w.inst('elnnne0')], 'sylibr',
             '%s e. NN' % FLM)
    mrp = sN([mnn], 'nnrpd', '%s e. RR+' % FLM)
    inner = 'if ( %s <_ %s , ( 1 / %s ) , ( %s / ( %s ^ 2 ) ) )' % (FLM, F400, FLM, F400, FLM)
    bvN = sN([LN(bv), sN([sN([], 'simpr', '-. %s = 0' % FLM), w.inst('iffalse')], 'syl', '%s = %s' % (BWB(FLM), inner))], 'eqtrd', '%s = %s' % (BW(FLM), inner))
    # case m <_ 400
    aB = '( %s /\\ %s <_ %s )' % (aN, FLM, F400)
    sB = mkst(w, aB); LB = lambda s_: lift(w, s_, aB)
    bvB = sB([LB(bvN), sB([sB([], 'simpr', '%s <_ %s' % (FLM, F400)), w.inst('iftrue')], 'syl', '%s = ( 1 / %s )' % (inner, FLM))], 'eqtrd', '%s = ( 1 / %s )' % (BW(FLM), FLM))
    tg = sB([LB(st([thre, gr], 'remulcld', '( %s x. %s ) e. RR' % (TH, g))), LB(st([c7r, er], 'remulcld', '( %s x. %s ) e. RR' % (C7, E))), LB(c7r), LB(b2t), LB(ce2)], 'letrd', '( %s x. %s ) <_ %s' % (TH, g, C7))
    mg = sB([LB(mr), LB(tyr), LB(gr), LB(g0), LB(mle)], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (FLM, g, TY, g))
    clB = Closure(w, aB, {TH: LB(thre), YD: LB(yr), g: LB(gr)})
    rq = ringeq(w, aB, '( %s x. %s )' % (TY, g), '( %s x. ( %s x. %s ) )' % (YD, TH, g), clB)
    yg = sB([LB(st([thre, gr], 'remulcld', '( %s x. %s ) e. RR' % (TH, g))), LB(c7r), LB(yr), LB(st([yrp], 'rpge0d', '0 <_ %s' % YD)), tg], 'lemul2ad',
            '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (YD, TH, g, YD, C7))
    mgy = sB([sB([LB(mr), LB(gr)], 'remulcld', '( %s x. %s ) e. RR' % (FLM, g)), sB([LB(yr), LB(st([thre, gr], 'remulcld', '( %s x. %s ) e. RR' % (TH, g)))], 'remulcld', '( %s x. ( %s x. %s ) ) e. RR' % (YD, TH, g)), sB([LB(yr), LB(c7r)], 'remulcld', '( %s x. %s ) e. RR' % (YD, C7)), sB([mg, rq], 'breqtrd', '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (FLM, g, YD, TH, g)), yg], 'letrd', '( %s x. %s ) <_ ( %s x. %s )' % (FLM, g, YD, C7))
    gq = sB([mgy, sB([LB(gr), sB([LB(yr), LB(c7r)], 'remulcld', '( %s x. %s ) e. RR' % (YD, C7)), LB(mrp)], 'lemuldiv2d',
                     '( ( %s x. %s ) <_ ( %s x. %s ) <-> %s <_ ( ( %s x. %s ) / %s ) )' % (FLM, g, YD, C7, g, YD, C7, FLM))], 'mpbid',
            '%s <_ ( ( %s x. %s ) / %s )' % (g, YD, C7, FLM))
    ycc = sB([sB([LB(yr), LB(c7r)], 'remulcld', '( %s x. %s ) e. RR' % (YD, C7))], 'recnd', '( %s x. %s ) e. CC' % (YD, C7))
    dq = sB([ycc, sB([LB(mrp)], 'rpcnd', '%s e. CC' % FLM), sB([LB(mrp)], 'rpne0d', '%s =/= 0' % FLM)], 'divrecd', '( ( %s x. %s ) / %s ) = ( ( %s x. %s ) x. ( 1 / %s ) )' % (YD, C7, FLM, YD, C7, FLM))
    ycm = sB([sB([LB(yr)], 'recnd', '%s e. CC' % YD), sB([LB(c7r)], 'recnd', '%s e. CC' % C7)], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (YD, C7, C7, YD))
    tB = sB([sB([bvB], 'oveq2d', '%s = %s' % (TT(BW(FLM)), TT('( 1 / %s )' % FLM))), sB([dq, sB([ycm], 'oveq1d', '( ( %s x. %s ) x. ( 1 / %s ) ) = %s' % (YD, C7, FLM, TT('( 1 / %s )' % FLM)))], 'eqtrd',
                                                                                                    '( ( %s x. %s ) / %s ) = %s' % (YD, C7, FLM, TT('( 1 / %s )' % FLM)))], 'eqtr4d',
            '%s = ( ( %s x. %s ) / %s )' % (TT(BW(FLM)), YD, C7, FLM))
    cB = sB([gq, tB], 'breqtrrd', '%s <_ %s' % (g, TT(BW(FLM))))
    # case -. m <_ 400
    aC = '( %s /\\ -. %s <_ %s )' % (aN, FLM, F400)
    sC = mkst(w, aC); LC = lambda s_: lift(w, s_, aC)
    Q400 = '( %s / ( %s ^ 2 ) )' % (F400, FLM)
    bvC = sC([LC(bvN), sC([sC([], 'simpr', '-. %s <_ %s' % (FLM, F400)), w.inst('iffalse')], 'syl', '%s = %s' % (inner, Q400))], 'eqtrd', '%s = %s' % (BW(FLM), Q400))
    m2 = sC([LC(mle), sC([LC(mr), LC(tyr), LC(m0), LC(ty0)], 'le2sqd', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (FLM, TY, FLM, TY))], 'mpbid', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (FLM, TY))
    sq1 = sC([sC([LC(thre)], 'recnd', '%s e. CC' % TH), sC([LC(yr)], 'recnd', '%s e. CC' % YD)], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (TY, TH, YD))
    ab2 = sC([LC(ivr), w.inst('absresq')], 'syl', '( %s ^ 2 ) = ( ( Im ` V ) ^ 2 )' % TH)
    IY = '( ( ( Im ` V ) ^ 2 ) x. ( %s ^ 2 ) )' % YD
    sq2 = sC([sq1, sC([ab2], 'oveq1d', '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) = %s' % (TH, YD, IY))], 'eqtrd', '( %s ^ 2 ) = %s' % (TY, IY))
    m2b = sC([m2, sq2], 'breqtrd', '( %s ^ 2 ) <_ %s' % (FLM, IY))
    iyr = sC([sC([LC(ivr)], 'resqcld', '( ( Im ` V ) ^ 2 ) e. RR'), sC([LC(yr)], 'resqcld', '( %s ^ 2 ) e. RR' % YD)], 'remulcld', '%s e. RR' % IY)
    m2g = sC([sC([LC(mr)], 'resqcld', '( %s ^ 2 ) e. RR' % FLM), iyr, LC(gr), LC(g0), m2b], 'lemul1ad', '( ( %s ^ 2 ) x. %s ) <_ ( %s x. %s )' % (FLM, g, IY, g))
    Y100 = '( ; ; 1 0 0 x. %s )' % YD
    clC = Closure(w, aC, {'( Im ` V )': LC(ivr), YD: LC(yr), g: LC(gr)})
    rq2 = ringeqp(w, aC, '( %s x. %s )' % (IY, g), '( %s x. %s )' % (Y100, Q), clC)
    c4 = st([a1(w, a, num.re_nat(w, 4), '4 e. RR'), c7r], 'remulcld', '( 4 x. %s ) e. RR' % C7)
    c40 = st([a1(w, a, num.re_nat(w, 4), '4 e. RR'), c7r, a1(w, a, num.ge0_nat(w, 4), '0 <_ 4'), c70], 'mulge0d', '0 <_ ( 4 x. %s )' % C7)
    ce4 = st([er, st([], '1red', '1 e. RR'), c4, c40, e1], 'lemul2ad', '( ( 4 x. %s ) x. %s ) <_ ( ( 4 x. %s ) x. 1 )' % (C7, E, C7))
    ce4b = st([ce4, st([st([c4], 'recnd', '( 4 x. %s ) e. CC' % C7)], 'mulridd', '( ( 4 x. %s ) x. 1 ) = ( 4 x. %s )' % (C7, C7))], 'breqtrd', '( ( 4 x. %s ) x. %s ) <_ ( 4 x. %s )' % (C7, E, C7))
    qr = sC([sC([sC([LC(ivr)], 'resqcld', '( ( Im ` V ) ^ 2 ) e. RR'), LC(elr)], 'remulcld', '( ( ( Im ` V ) ^ 2 ) x. %s ) e. RR' % ELLD), LC(gr)], 'remulcld', '%s e. RR' % Q)
    q4 = sC([qr, LC(st([c4, er], 'remulcld', '( ( 4 x. %s ) x. %s ) e. RR' % (C7, E))), LC(c4), LC(b3t), LC(ce4b)], 'letrd', '%s <_ ( 4 x. %s )' % (Q, C7))
    y100r = sC([a1(w, aC, num.re_nat(w, 100), '; ; 1 0 0 e. RR'), LC(yr)], 'remulcld', '%s e. RR' % Y100)
    y1000 = sC([a1(w, aC, num.re_nat(w, 100), '; ; 1 0 0 e. RR'), LC(yr), a1(w, aC, num.ge0_nat(w, 100), '0 <_ ; ; 1 0 0'), LC(st([yrp], 'rpge0d', '0 <_ %s' % YD))], 'mulge0d',
               '0 <_ %s' % Y100)
    yq = sC([qr, LC(c4), y100r, y1000, q4], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 4 x. %s ) )' % (Y100, Q, Y100, C7))
    RHS = '( %s x. ( 4 x. %s ) )' % (Y100, C7)
    rhr = sC([y100r, LC(c4)], 'remulcld', '%s e. RR' % RHS)
    mgc = sC([sC([sC([LC(mr)], 'resqcld', '( %s ^ 2 ) e. RR' % FLM), LC(gr)], 'remulcld', '( ( %s ^ 2 ) x. %s ) e. RR' % (FLM, g)), sC([y100r, qr], 'remulcld', '( %s x. %s ) e. RR' % (Y100, Q)), rhr, sC([m2g, rq2], 'breqtrd', '( ( %s ^ 2 ) x. %s ) <_ ( %s x. %s )' % (FLM, g, Y100, Q)), yq], 'letrd', '( ( %s ^ 2 ) x. %s ) <_ %s' % (FLM, g, RHS))
    m2rp = sC([LC(sN([mrp, a1(w, aN, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '( %s ^ 2 ) e. RR+' % FLM))], 'idi', '( %s ^ 2 ) e. RR+' % FLM)
    gq2 = sC([mgc, sC([LC(gr), rhr, m2rp], 'lemuldiv2d', '( ( ( %s ^ 2 ) x. %s ) <_ %s <-> %s <_ ( %s / ( %s ^ 2 ) ) )' % (FLM, g, RHS, g, RHS, FLM))], 'mpbid',
             '%s <_ ( %s / ( %s ^ 2 ) )' % (g, RHS, FLM))
    IM = '( 1 / ( %s ^ 2 ) )' % FLM
    m2c = sC([m2rp], 'rpcnd', '( %s ^ 2 ) e. CC' % FLM); m2n = sC([m2rp], 'rpne0d', '( %s ^ 2 ) =/= 0' % FLM)
    d1_ = sC([sC([rhr], 'recnd', '%s e. CC' % RHS), m2c, m2n], 'divrecd', '( %s / ( %s ^ 2 ) ) = ( %s x. %s )' % (RHS, FLM, RHS, IM))
    d2_ = sC([a1(w, aC, num.cc_nat(w, 400), '%s e. CC' % F400), m2c, m2n], 'divrecd', '%s = ( %s x. %s )' % (Q400, F400, IM))
    imr = sC([sC([m2rp], 'rpreccld', '%s e. RR+' % IM)], 'rpred', '%s e. RR' % IM)
    clC2 = Closure(w, aC, {YD: LC(yr), IM: imr})
    rq3 = ringeq(w, aC, '( %s x. %s )' % (RHS, IM), TT('( %s x. %s )' % (F400, IM)), clC2)
    tC = sC([sC([bvC], 'oveq2d', '%s = %s' % (TT(BW(FLM)), TT(Q400))), sC([d2_], 'oveq2d', '%s = %s' % (TT(Q400), TT('( %s x. %s )' % (F400, IM))))], 'eqtrd',
            '%s = %s' % (TT(BW(FLM)), TT('( %s x. %s )' % (F400, IM))))
    tC2 = sC([sC([d1_, rq3], 'eqtrd', '( %s / ( %s ^ 2 ) ) = %s' % (RHS, FLM, TT('( %s x. %s )' % (F400, IM)))), tC], 'eqtr4d', '( %s / ( %s ^ 2 ) ) = %s' % (RHS, FLM, TT(BW(FLM))))
    cC = sC([gq2, tC2], 'breqtrd', '%s <_ %s' % (g, TT(BW(FLM))))
    cN = w.s([cB, cC], 'pm2.61dan', '( %s -> %s <_ %s )' % (aN, g, TT(BW(FLM))))
    fin = w.s([cA, cN], 'pm2.61dan', '( %s -> %s <_ %s )' % (a, g, TT(BW(FLM))))
    w.qed([fin], 'idi', S_['gf2g1bw'])
    return w


QRR = 'prod_ p e. { q e. Prime | ( q || N /\\ q <_ R ) } ( 1 - ( 1 / p ) )'
MRR = 'prod_ p e. ( ( 1 ... ( |_ ` R ) ) i^i Prime ) ( 1 / ( 1 - ( 1 / p ) ) )'
S_['gf2qm'] = '( ( N e. NN /\\ R e. RR ) -> ( %s e. RR /\\ %s e. RR ) )' % (QRR, MRR)


def gf2qm():
    w = W('gf2qm', 'The two Euler products of Lemma 6.4 are real: ` Q_R = prod_ ( p | N , p <_ R ) ( 1 - 1 / p ) ` and the Mertens product (~ fprodrecl , ~ prmdvdsfi ).')
    a = '( N e. NN /\\ R e. RR )'
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN')
    QS = '{ q e. Prime | ( q || N /\\ q <_ R ) }'; PFN = '{ q e. Prime | q || N }'
    ssq = w.s([w.s([w.s([], 'simpl', '( ( q || N /\\ q <_ R ) -> q || N )')], 'a1i', '( q e. Prime -> ( ( q || N /\\ q <_ R ) -> q || N ) )')], 'ss2rabi', '%s C_ %s' % (QS, PFN))
    pfn = st([nn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PFN)
    qfi = st([pfn, a1(w, a, ssq, '%s C_ %s' % (QS, PFN))], 'ssfid', '%s e. Fin' % QS)
    ap = '( %s /\\ p e. %s )' % (a, QS)
    sp = mkst(w, ap)
    ppr = sp([a1(w, ap, w.s([], 'ssrab2', '%s C_ Prime' % QS), '%s C_ Prime' % QS), sp([], 'simpr', 'p e. %s' % QS)], 'sseldd', 'p e. Prime')
    pn = sp([ppr, w.inst('prmnn')], 'syl', 'p e. NN')
    t1 = sp([sp([], '1red', '1 e. RR'), sp([pn], 'nnrecred', '( 1 / p ) e. RR')], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    q1 = st([qfi, t1], 'fprodrecl', '%s e. RR' % QRR)
    MS = '( ( 1 ... ( |_ ` R ) ) i^i Prime )'
    mfi = st([st([], 'fzfid', '( 1 ... ( |_ ` R ) ) e. Fin'), a1(w, a, w.s([], 'inss1', '%s C_ ( 1 ... ( |_ ` R ) )' % MS), '%s C_ ( 1 ... ( |_ ` R ) )' % MS)], 'ssfid', '%s e. Fin' % MS)
    am = '( %s /\\ p e. %s )' % (a, MS)
    sm = mkst(w, am)
    pm = sm([sm([], 'simpr', 'p e. %s' % MS), w.inst('elinel2')], 'syl', 'p e. Prime')
    pmn = sm([pm, w.inst('prmnn')], 'syl', 'p e. NN')
    pmr = sm([pmn], 'nnred', 'p e. RR')
    g1 = sm([pm, w.inst('prmgt1')], 'syl', '1 < p')
    rl = sm([g1, sm([sm([pmr, sm([pmn], 'nngt0d', '0 < p')], 'jca', '( p e. RR /\\ 0 < p )'), w.inst('recgt1')], 'syl', '( 1 < p <-> ( 1 / p ) < 1 )')], 'mpbid', '( 1 / p ) < 1')
    ipr = sm([pmn], 'nnrecred', '( 1 / p ) e. RR')
    dpos = lin.linarith(w, am, [rl], '0 < ( 1 - ( 1 / p ) )', leaves={'( 1 / p )': ipr})
    dr = sm([sm([], '1red', '1 e. RR'), ipr], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    t2 = sm([dr, sm([dpos], 'gt0ne0d', '( 1 - ( 1 / p ) ) =/= 0')], 'rereccld', '( 1 / ( 1 - ( 1 / p ) ) ) e. RR')
    m1 = st([mfi, t2], 'fprodrecl', '%s e. RR' % MRR)
    w.qed([st([q1, m1], 'jca', '( %s e. RR /\\ %s e. RR )' % (QRR, MRR))], 'idi', S_['gf2qm'])
    return w


_U = '( Q x. ( Q x. ( K x. ( ( 1 / ; ; 1 0 0 ) x. Y ) ) ) )'
_Z = '( ( %s x. Y ) x. ( 5 + ( 2 x. ( log ` %s ) ) ) )' % (L.C7, F400)
_R = '( ( ( %s x. ( Q ^ 2 ) ) x. ( 1 / ; ; 1 0 0 ) ) x. ( Y ^ 2 ) )' % L.C9('K')
S_['gf2alg'] = '( ( Q e. RR /\\ K e. RR /\\ Y e. RR ) -> ( %s x. %s ) = %s )' % (_U, _Z, _R)


def gf2alg():
    w = W('gf2alg', 'The constant bookkeeping of Lemma 6.4: ` Q ( Q K L / 100 ) C_7 L ( 5 + 2 log 400 ) = C_9 ( K ) Q ^ 2 ( 1 / 100 ) L ^ 2 ` (ring normal form).')
    a, c = split_imp(S_['gf2alg'])
    st = mkst(w, a)
    LG = '( log ` %s )' % F400
    lv = {'Q': st([], 'simp1', 'Q e. RR'), 'K': st([], 'simp2', 'K e. RR'), 'Y': st([], 'simp3', 'Y e. RR')}
    cl = Closure(w, a, lv)
    l = '( %s x. %s )' % (_U, _Z); r = _R
    e1 = st([st([lv['Q']], 'recnd', 'Q e. CC')], 'sqvald', '( Q ^ 2 ) = ( Q x. Q )')
    e2 = st([st([lv['Y']], 'recnd', 'Y e. CC')], 'sqvald', '( Y ^ 2 ) = ( Y x. Y )')
    rw, r2 = w.rewrite(r, {'( Q ^ 2 )': ('( Q x. Q )', e1), '( Y ^ 2 )': ('( Y x. Y )', e2)}, a)
    e = ringeq(w, a, l, r2, cl)
    w.qed([e, rw], 'eqtr4d', S_['gf2alg'])
    return w


VI = lambda i: '( V ` %s )' % i
THI = lambda i: '( abs ` ( Im ` ( V ` %s ) ) )' % i
P1 = lambda i: '( %s e. CC /\\ ( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) ) )' % (VI(i), VI(i), VI(i))
P2 = lambda i: '( %s =/= J -> ( 1 / %s ) <_ %s )' % (i, YD, THI(i))
BIN = lambda j, x: '( ( %s / %s ) <_ %s /\\ %s < ( ( %s + 1 ) / %s ) )' % (x, YD, THI(j), THI(j), x, YD)
P3 = lambda y, u: '( # ` { %s e. S | %s } ) <_ 2' % (y, BIN(y, u))
FLI = lambda i: '( |_ ` ( %s x. %s ) )' % (THI(i), YD)
GG = '( v e. S |-> %s )' % FLI('v')
FB = lambda x: '{ j e. S | ( %s ` j ) = %s }' % (GG, x)


def gf2row():
    w = W('gf2row', 'Blueprint Lemma 6.4 (Lean ` row_sum_le ` ): with the spacing of one parity system (at most one point in bin 0, at most two per bin '
                    '` m >_ 1 ` ), ` sum_k | ( phi ( N ) / N ) Phi_R G_1 ( - s_k ) | <_ C_9 ( K ) Q_R ^ 2 ( 1 / 100 ) L ^ 2 ` '
                    '(~ gf2g1bw , ~ gf2fib , ~ z5dtotqr , ~ z5phip1 , ~ z5dp1mert ).')
    A0, CONC = split_imp(S_['gf2row'])
    HD = '( D e. RR /\\ 1 < D /\\ 1 <_ %s )' % YD
    QK = '( K e. RR /\\ %s <_ ( K x. ( log ` %s ) ) )' % (L.MERT, RP)
    X1 = '( S e. Fin /\\ A. i e. S %s )' % P1('i')
    X2 = '( A. i e. S %s /\\ A. u e. NN %s )' % (P2('i'), P3('y', 'u'))
    a = '( ( %s /\\ N e. NN ) /\\ ( %s /\\ %s /\\ %s ) )' % (HD, X1, X2, QK)
    st = mkst(w, a)
    hdn = st([], 'simpl', '( %s /\\ N e. NN )' % HD)
    hd = st([hdn], 'simpld', HD); nnn = st([hdn], 'simprd', 'N e. NN')
    rest = st([], 'simpr', '( %s /\\ %s /\\ %s )' % (X1, X2, QK))
    x1 = st([rest], 'simp1d', X1); x2 = st([rest], 'simp2d', X2); qk = st([rest], 'simp3d', QK)
    sf = st([x1], 'simpld', 'S e. Fin'); al1 = st([x1], 'simprd', 'A. i e. S %s' % P1('i'))
    al2 = st([x2], 'simpld', 'A. i e. S %s' % P2('i')); al3 = st([x2], 'simprd', 'A. u e. NN %s' % P3('y', 'u'))
    kr = st([qk], 'simpld', 'K e. RR'); mert = st([qk], 'simprd', '%s <_ ( K x. ( log ` %s ) )' % (L.MERT, RP))
    dr = st([hd], 'simp1d', 'D e. RR'); d1 = st([hd], 'simp2d', '1 < D'); y1 = st([hd], 'simp3d', '1 <_ %s' % YD)
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    yr = st([drp], 'relogcld', '%s e. RR' % YD)
    yrp = st([yr, lin.linarith(w, a, [y1], '0 < %s' % YD, leaves={YD: yr})], 'elrpd', '%s e. RR+' % YD)

    def pk(ante, al, P, i, k):
        idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (i, k, i, k))
        sub, _ = w.wcongr(P(i), {i: k}, '%s = %s' % (i, k), {i: idx})
        return sub

    def theta(ante, vc, i):
        sa = mkst(w, ante)
        ic = sa([sa([vc], 'imcld', '( Im ` %s ) e. RR' % VI(i))], 'recnd', '( Im ` %s ) e. CC' % VI(i))
        return sa([ic], 'abscld', '%s e. RR' % THI(i)), sa([ic], 'absge0d', '0 <_ %s' % THI(i))

    # ---- G : S --> NN0
    ai = '( %s /\\ v e. S )' % a
    si = mkst(w, ai)
    p1i = si([pk(ai, al1, P1, 'i', 'v'), lift(w, al1, ai), si([], 'simpr', 'v e. S')], 'rspcdva', P1('v'))
    vci = si([p1i], 'simpld', '%s e. CC' % VI('v'))
    thi, th0i = theta(ai, vci, 'v')
    tyi = si([thi, lift(w, yr, ai)], 'remulcld', '( %s x. %s ) e. RR' % (THI('v'), YD))
    ty0i = si([thi, lift(w, yr, ai), th0i, lift(w, st([yrp], 'rpge0d', '0 <_ %s' % YD), ai)], 'mulge0d', '0 <_ ( %s x. %s )' % (THI('v'), YD))
    fli = si([si([tyi, ty0i], 'jca', '( ( %s x. %s ) e. RR /\\ 0 <_ ( %s x. %s ) )' % (THI('v'), YD, THI('v'), YD)), w.inst('flge0nn0')], 'syl', '%s e. NN0' % FLI('v'))
    gf = st([fli], 'fmptd', '%s : S --> NN0' % GG)

    def gval(ante, jin, j):
        v, _ = mpv(w, ante, 'v', 'S', FLI('v'), j, jin)
        return v

    FT = lambda x: '{ t e. S | ( %s ` t ) = %s }' % (GG, x)

    def tsub(x):
        return w.s([w.s([], 'fveq2', '( t = j -> ( %s ` t ) = ( %s ` j ) )' % (GG, GG))], 'eqeq1d', '( t = j -> ( ( %s ` t ) = %s <-> ( %s ` j ) = %s ) )' % (GG, x, GG, x))

    def ftfb(x):
        """FT ( x ) = FB ( x )"""
        return w.s([w.s([w.s([], 'fveq2', '( t = j -> ( %s ` t ) = ( %s ` j ) )' % (GG, GG))], 'eqeq1d', '( t = j -> ( ( %s ` t ) = %s <-> ( %s ` j ) = %s ) )' % (GG, x, GG, x))],
                   'cbvrabv', '%s = %s' % (FT(x), FB(x)))

    # ---- the zero bin: F ( 0 ) C_ { J }
    aj0 = '( %s /\\ j e. %s )' % (a, FT('0'))
    s0 = mkst(w, aj0)
    rb0 = s0([s0([], 'simpr', 'j e. %s' % FT('0')), w.s([tsub('0')], 'elrab', '( j e. %s <-> ( j e. S /\\ ( %s ` j ) = 0 ) )' % (FT('0'), GG))], 'sylib',
             '( j e. S /\\ ( %s ` j ) = 0 )' % GG)
    js0 = s0([rb0], 'simpld', 'j e. S'); gj0 = s0([rb0], 'simprd', '( %s ` j ) = 0' % GG)
    gv0 = gval(aj0, js0, 'j')
    p1j = s0([pk(aj0, al1, P1, 'i', 'j'), lift(w, al1, aj0), js0], 'rspcdva', P1('j'))
    p2j = s0([pk(aj0, al2, P2, 'i', 'j'), lift(w, al2, aj0), js0], 'rspcdva', P2('j'))
    vcj = s0([p1j], 'simpld', '%s e. CC' % VI('j'))
    thj, th0j = theta(aj0, vcj, 'j')
    TYJ = '( %s x. %s )' % (THI('j'), YD)
    tyj = s0([thj, lift(w, yr, aj0)], 'remulcld', '%s e. RR' % TYJ)
    ajn = '( %s /\\ j =/= J )' % aj0
    sn = mkst(w, ajn)
    iy = sn([sn([], 'simpr', 'j =/= J'), lift(w, p2j, ajn)], 'mpd', '( 1 / %s ) <_ %s' % (YD, THI('j')))
    i1 = sn([iy, sn([sn([], '1red', '1 e. RR'), lift(w, thj, ajn), lift(w, yrp, ajn)], 'ledivmuld', '( ( 1 / %s ) <_ %s <-> 1 <_ ( %s x. %s ) )' % (YD, THI('j'), YD, THI('j')))],
            'mpbid', '1 <_ ( %s x. %s )' % (YD, THI('j')))
    i2 = sn([i1, sn([sn([lift(w, yr, ajn)], 'recnd', '%s e. CC' % YD), sn([lift(w, thj, ajn)], 'recnd', '%s e. CC' % THI('j'))], 'mulcomd',
                    '( %s x. %s ) = %s' % (YD, THI('j'), TYJ))], 'breqtrd', '1 <_ %s' % TYJ)
    i3 = sn([i2, sn([lift(w, tyj, ajn), a1(w, ajn, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), w.inst('flge')], 'syl2anc', '( 1 <_ %s <-> 1 <_ %s )' % (TYJ, FLI('j')))], 'mpbid',
            '1 <_ %s' % FLI('j'))
    flr = s0([s0([tyj], 'flcld', '%s e. ZZ' % FLI('j'))], 'zred', '%s e. RR' % FLI('j'))
    fgt = lin.linarith(w, ajn, [i3], '0 < %s' % FLI('j'), leaves={FLI('j'): lift(w, flr, ajn)})
    fne = sn([fgt], 'gt0ne0d', '%s =/= 0' % FLI('j'))
    gne = sn([lift(w, gv0, ajn), fne], 'eqnetrd', '( %s ` j ) =/= 0' % GG)
    imp = s0([gne], 'ex', '( j =/= J -> ( %s ` j ) =/= 0 )' % GG)
    jj = s0([gj0, s0([imp], 'necon4d', '( ( %s ` j ) = 0 -> j = J )' % GG)], 'mpd', 'j = J')
    jsn = s0([jj, w.s([], 'velsn', '( j e. { J } <-> j = J )')], 'sylibr', 'j e. { J }')
    ss0 = st([st([jsn], 'ex', '( j e. %s -> j e. { J } )' % FT('0'))], 'ssrdv', '%s C_ { J }' % FT('0'))
    fin0 = st([sf, a1(w, a, w.s([], 'ssrab2', '%s C_ S' % FT('0')), '%s C_ S' % FT('0'))], 'ssfid', '%s e. Fin' % FT('0'))
    hf0 = st([st([fin0, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % FT('0'))], 'nn0red', '( # ` %s ) e. RR' % FT('0'))
    hsj = a1(w, a, w.s([w.s([], 'hashsnlei', '( { J } e. Fin /\\ ( # ` { J } ) <_ 1 )')], 'simpli', '{ J } e. Fin'), '{ J } e. Fin')
    hsr = st([st([hsj, w.inst('hashcl')], 'syl', '( # ` { J } ) e. NN0')], 'nn0red', '( # ` { J } ) e. RR')
    hss = st([a1(w, a, w.s([], 'snex', '{ J } e. _V'), '{ J } e. _V'), ss0, w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` { J } )' % FT('0'))
    h0 = st([hf0, hsr, st([], '1red', '1 e. RR'), hss, a1(w, a, w.s([], 'hashsnle1', '( # ` { J } ) <_ 1'), '( # ` { J } ) <_ 1')], 'letrd', '( # ` %s ) <_ 1' % FT('0'))
    # ---- the other bins
    ax = '( %s /\\ x e. NN )' % a
    sx = mkst(w, ax)
    xn = sx([], 'simpr', 'x e. NN')
    axj = '( %s /\\ j e. %s )' % (ax, FT('x'))
    sxj = mkst(w, axj)
    rbx = sxj([sxj([], 'simpr', 'j e. %s' % FT('x')), w.s([tsub('x')], 'elrab', '( j e. %s <-> ( j e. S /\\ ( %s ` j ) = x ) )' % (FT('x'), GG))], 'sylib',
              '( j e. S /\\ ( %s ` j ) = x )' % GG)
    jsx = sxj([rbx], 'simpld', 'j e. S'); gjx = sxj([rbx], 'simprd', '( %s ` j ) = x' % GG)
    gvx = gval(axj, jsx, 'j')
    flx = sxj([gvx, gjx], 'eqtr3d', '%s = x' % FLI('j'))
    p1x = sxj([pk(axj, al1, P1, 'i', 'j'), lift(w, al1, axj), jsx], 'rspcdva', P1('j'))
    thx, th0x = theta(axj, sxj([p1x], 'simpld', '%s e. CC' % VI('j')), 'j')
    tyx = sxj([thx, lift(w, yr, axj)], 'remulcld', '%s e. RR' % TYJ)
    xz = sxj([lift(w, xn, axj)], 'nnzd', 'x e. ZZ'); xr = sxj([lift(w, xn, axj)], 'nnred', 'x e. RR')
    fb = sxj([flx, sxj([tyx, xz, w.inst('flbi')], 'syl2anc', '( %s = x <-> ( x <_ %s /\\ %s < ( x + 1 ) ) )' % (FLI('j'), TYJ, TYJ))], 'mpbid',
             '( x <_ %s /\\ %s < ( x + 1 ) )' % (TYJ, TYJ))
    yrx = lift(w, yrp, axj)
    cm = sxj([sxj([lift(w, yr, axj)], 'recnd', '%s e. CC' % YD), sxj([thx], 'recnd', '%s e. CC' % THI('j'))], 'mulcomd', '( %s x. %s ) = %s' % (YD, THI('j'), TYJ))
    lo = sxj([sxj([sxj([fb], 'simpld', 'x <_ %s' % TYJ), cm], 'breqtrrd', 'x <_ ( %s x. %s )' % (YD, THI('j'))),
              sxj([xr, thx, yrx], 'ledivmuld', '( ( x / %s ) <_ %s <-> x <_ ( %s x. %s ) )' % (YD, THI('j'), YD, THI('j')))], 'mpbird', '( x / %s ) <_ %s' % (YD, THI('j')))
    x1r = sxj([xr, sxj([], '1red', '1 e. RR')], 'readdcld', '( x + 1 ) e. RR')
    hi = sxj([sxj([fb], 'simprd', '%s < ( x + 1 )' % TYJ), sxj([thx, x1r, yrx], 'ltmuldivd', '( %s < ( x + 1 ) <-> %s < ( ( x + 1 ) / %s ) )' % (TYJ, THI('j'), YD))], 'mpbid',
             '%s < ( ( x + 1 ) / %s )' % (THI('j'), YD))
    idy = w.s([], 'id', '( y = j -> y = j )')
    ysub, _ = w.wcongr(BIN('y', 'x'), {'y': 'j'}, 'y = j', {'y': idy})
    BX = '{ y e. S | %s }' % BIN('y', 'x')
    elb = sxj([sxj([jsx, sxj([lo, hi], 'jca', BIN('j', 'x'))], 'jca', '( j e. S /\\ %s )' % BIN('j', 'x')), w.s([ysub], 'elrab', '( j e. %s <-> ( j e. S /\\ %s ) )' % (BX, BIN('j', 'x')))],
              'sylibr', 'j e. %s' % BX)
    ssx = sx([sx([elb], 'ex', '( j e. %s -> j e. %s )' % (FT('x'), BX))], 'ssrdv', '%s C_ %s' % (FT('x'), BX))
    bxf = sx([lift(w, sf, ax), a1(w, ax, w.s([], 'ssrab2', '%s C_ S' % BX), '%s C_ S' % BX)], 'ssfid', '%s e. Fin' % BX)
    hsx = sx([bxf, ssx, w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` %s )' % (FT('x'), BX))
    idu = w.s([], 'id', '( u = x -> u = x )')
    usub, _ = w.wcongr(P3('y', 'u'), {'u': 'x'}, 'u = x', {'u': idu})
    p3x = sx([usub, lift(w, al3, ax), xn], 'rspcdva', P3('y', 'x'))
    finx = sx([lift(w, sf, ax), a1(w, ax, w.s([], 'ssrab2', '%s C_ S' % FT('x')), '%s C_ S' % FT('x'))], 'ssfid', '%s e. Fin' % FT('x'))
    hfx = sx([sx([finx, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % FT('x'))], 'nn0red', '( # ` %s ) e. RR' % FT('x'))
    hbx = sx([sx([bxf, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % BX)], 'nn0red', '( # ` %s ) e. RR' % BX)
    h2x = sx([hfx, hbx, a1(w, ax, w.s([], '2re', '2 e. RR'), '2 e. RR'), hsx, p3x], 'letrd', '( # ` %s ) <_ 2' % FT('x'))
    h2 = st([h2x], 'ralrimiva', 'A. x e. NN ( # ` %s ) <_ 2' % FT('x'))
    h0 = st([a1(w, a, w.s([ftfb('0')], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (FT('0'), FB('0'))), '( # ` %s ) = ( # ` %s )' % (FT('0'), FB('0'))), h0], 'eqbrtrrd',
            '( # ` %s ) <_ 1' % FB('0'))
    h2 = st([h2, a1(w, a, w.s([w.s([w.s([ftfb('x')], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (FT('x'), FB('x')))], 'breq1i',
                                     '( ( # ` %s ) <_ 2 <-> ( # ` %s ) <_ 2 )' % (FT('x'), FB('x')))], 'ralbii',
                              '( A. x e. NN ( # ` %s ) <_ 2 <-> A. x e. NN ( # ` %s ) <_ 2 )' % (FT('x'), FB('x'))),
                   '( A. x e. NN ( # ` %s ) <_ 2 <-> A. x e. NN ( # ` %s ) <_ 2 )' % (FT('x'), FB('x')))], 'mpbid', 'A. x e. NN ( # ` %s ) <_ 2' % FB('x'))
    W5 = '( 5 + ( 2 x. ( log ` %s ) ) )' % F400
    fibc = st([st([sf, gf], 'jca', '( S e. Fin /\\ %s : S --> NN0 )' % GG), st([h0, h2], 'jca', '( ( # ` %s ) <_ 1 /\\ A. x e. NN ( # ` %s ) <_ 2 )' % (FB('0'), FB('x')))],
              'jca', '( ( S e. Fin /\\ %s : S --> NN0 ) /\\ ( ( # ` %s ) <_ 1 /\\ A. x e. NN ( # ` %s ) <_ 2 ) )' % (GG, FB('0'), FB('x')))
    fib = st([fibc, w.inst('gf2fib')], 'syl', 'sum_ k e. S %s <_ %s' % (BW('( %s ` k )' % GG), W5))
    # ---- per k
    ak = '( %s /\\ k e. S )' % a
    sk = mkst(w, ak)
    ks = sk([], 'simpr', 'k e. S')
    gvk = gval(ak, ks, 'k')
    bwk = sk([gvk], 'fveq2d', '%s = %s' % (BW('( %s ` k )' % GG), BW(FLI('k'))))
    SBG = 'sum_ k e. S %s' % BW('( %s ` k )' % GG); SB = 'sum_ k e. S %s' % BW(FLI('k'))
    sbe = st([bwk], 'sumeq2dv', '%s = %s' % (SBG, SB))
    p1k = sk([pk(ak, al1, P1, 'i', 'k'), lift(w, al1, ak), ks], 'rspcdva', P1('k'))
    G1K = L.G1F('-u %s' % VI('k'))
    gb = sk([sk([lift(w, hd, ak), p1k], 'jca', '( %s /\\ %s )' % (HD, P1('k'))), w.inst('gf2g1bw')], 'syl',
            '( abs ` %s ) <_ ( ( %s x. %s ) x. %s )' % (G1K, L.C7, YD, BW(FLI('k'))))
    g1c = sk([gb, w.inst('z6absle')], 'syl', '%s e. CC' % G1K)
    gar = sk([g1c], 'abscld', '( abs ` %s ) e. RR' % G1K)
    cN = '( ( phi ` N ) / N )'
    PH_ = L.PHI('N', RP)
    nrp = st([nnn], 'nnrpd', 'N e. RR+')
    crp = st([st([st([nnn, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nnrpd', '( phi ` N ) e. RR+'), nrp], 'rpdivcld', '%s e. RR+' % cN)
    rps = st([drp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % RP)
    rpr = st([rps], 'rpred', '%s e. RR' % RP)
    nv = st([nnn], 'elexd', 'N e. _V')
    RS_ = '( N RSet %s )' % RP
    rsv = st([nv, rpr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS_, RP, RS_))
    rfi = st([rsv], 'simprd', '%s e. Fin' % RS_)
    ar = '( %s /\\ r e. %s )' % (a, RS_)
    sr_ = mkst(w, ar)
    rn = sr_([sr_([lift(w, st([rsv], 'simpld', '%s C_ ( 1 ... ( |_ ` %s ) )' % (RS_, RP)), ar), sr_([], 'simpr', 'r e. %s' % RS_)], 'sseldd', 'r e. ( 1 ... ( |_ ` %s ) )' % RP),
              w.inst('elfznn')], 'syl', 'r e. NN')
    trp = sr_([sr_([sr_([rn, w.inst('phicl')], 'syl', '( phi ` r ) e. NN')], 'nnrpd', '( phi ` r ) e. RR+'), sr_([sr_([rn], 'nnrpd', 'r e. RR+'), a1(w, ar, w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')],
                                                                                                             'rpexpcld', '( r ^ 2 ) e. RR+')], 'rpdivcld', '( ( phi ` r ) / ( r ^ 2 ) ) e. RR+')
    phr = st([rfi, sr_([trp], 'rpred', '( ( phi ` r ) / ( r ^ 2 ) ) e. RR')], 'fsumrecl', '%s e. RR' % PH_)
    ph0 = st([rfi, sr_([trp], 'rpred', '( ( phi ` r ) / ( r ^ 2 ) ) e. RR'), sr_([trp], 'rpge0d', '0 <_ ( ( phi ` r ) / ( r ^ 2 ) )')], 'fsumge0', '0 <_ %s' % PH_)
    P_ = '( %s x. %s )' % (cN, PH_)
    pr_ = st([st([crp], 'rpred', '%s e. RR' % cN), phr], 'remulcld', '%s e. RR' % P_)
    p0_ = st([st([crp], 'rpred', '%s e. RR' % cN), phr, st([crp], 'rpge0d', '0 <_ %s' % cN), ph0], 'mulge0d', '0 <_ %s' % P_)
    MK = '( %s x. %s )' % (P_, G1K)
    am_ = sk([sk([lift(w, pr_, ak)], 'recnd', '%s e. CC' % P_), g1c], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (MK, P_, G1K))
    am2 = sk([am_, sk([sk([lift(w, pr_, ak), lift(w, p0_, ak)], 'absidd', '( abs ` %s ) = %s' % (P_, P_))], 'oveq1d',
                      '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (P_, G1K, P_, G1K))], 'eqtrd', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (MK, P_, G1K))
    C7Y = '( %s x. %s )' % (L.C7, YD)
    c7yr = st([a1(w, a, num.re_nat(w, 8337480), '%s e. RR' % L.C7), yr], 'remulcld', '%s e. RR' % C7Y)
    vck = sk([p1k], 'simpld', '%s e. CC' % VI('k'))
    thk, th0k = theta(ak, vck, 'k')
    TYK = '( %s x. %s )' % (THI('k'), YD)
    tyk = sk([thk, lift(w, yr, ak)], 'remulcld', '%s e. RR' % TYK)
    ty0k = sk([thk, lift(w, yr, ak), th0k, lift(w, st([yrp], 'rpge0d', '0 <_ %s' % YD), ak)], 'mulge0d', '0 <_ %s' % TYK)
    flk = sk([sk([tyk, ty0k], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (TYK, TYK)), w.inst('flge0nn0')], 'syl', '%s e. NN0' % FLI('k'))
    bwkr, bwk0 = bwnn0(w, ak, FLI('k'), flk)
    TK = '( %s x. %s )' % (C7Y, BW(FLI('k')))
    tkr = sk([lift(w, c7yr, ak), bwkr], 'remulcld', '%s e. RR' % TK)
    mk = sk([gar, tkr, lift(w, pr_, ak), lift(w, p0_, ak), gb], 'lemul2ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. %s )' % (P_, G1K, P_, TK))
    mk2 = sk([am2, mk], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. %s )' % (MK, P_, TK))
    mkr = sk([sk([sk([lift(w, pr_, ak)], 'recnd', '%s e. CC' % P_), g1c], 'mulcld', '%s e. CC' % MK)], 'abscld', '( abs ` %s ) e. RR' % MK)
    ptr = sk([lift(w, pr_, ak), tkr], 'remulcld', '( %s x. %s ) e. RR' % (P_, TK))
    SA = 'sum_ k e. S ( abs ` %s )' % MK; SP = 'sum_ k e. S ( %s x. %s )' % (P_, TK); STK = 'sum_ k e. S %s' % TK
    sa = st([sf, mkr, ptr, mk2], 'fsumle', '%s <_ %s' % (SA, SP))
    fm1 = st([sf, st([pr_], 'recnd', '%s e. CC' % P_), sk([tkr], 'recnd', '%s e. CC' % TK)], 'fsummulc2', '( %s x. %s ) = %s' % (P_, STK, SP))
    fm2 = st([sf, st([c7yr], 'recnd', '%s e. CC' % C7Y), sk([bwkr], 'recnd', '%s e. CC' % BW(FLI('k')))], 'fsummulc2', '( %s x. %s ) = %s' % (C7Y, SB, STK))
    sbr = st([sf, bwkr], 'fsumrecl', '%s e. RR' % SB)
    sbw = st([sbe, fib], 'eqbrtrrd', '%s <_ %s' % (SB, W5))
    LG = '( log ` %s )' % F400
    lgr = st([a1(w, a, num.rp_nat(w, 400), '%s e. RR+' % F400)], 'relogcld', '%s e. RR' % LG)
    lg0 = st([a1(w, a, num.re_nat(w, 400), '%s e. RR' % F400), a1(w, a, num.le_lit(w, '1', F400), '1 <_ %s' % F400), w.inst('logge0')], 'syl2anc', '0 <_ %s' % LG)
    w5r = st([a1(w, a, num.re_nat(w, 5), '5 e. RR'), st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), lgr], 'remulcld', '( 2 x. %s ) e. RR' % LG)], 'readdcld', '%s e. RR' % W5)
    w50 = lin.linarith(w, a, [lg0], '0 <_ %s' % W5, leaves={LG: lgr})
    c7y0 = st([a1(w, a, num.re_nat(w, 8337480), '%s e. RR' % L.C7), yr, a1(w, a, num.ge0_nat(w, 8337480), '0 <_ %s' % L.C7), st([yrp], 'rpge0d', '0 <_ %s' % YD)], 'mulge0d', '0 <_ %s' % C7Y)
    Z1_ = '( %s x. %s )' % (C7Y, SB); Z5 = '( %s x. %s )' % (C7Y, W5)
    zz = st([sbr, w5r, c7yr, c7y0, sbw], 'lemul2ad', '%s <_ %s' % (Z1_, Z5))
    z1r = st([c7yr, sbr], 'remulcld', '%s e. RR' % Z1_); z5r = st([c7yr, w5r], 'remulcld', '%s e. RR' % Z5)
    pz = st([z1r, z5r, pr_, p0_, zz], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (P_, Z1_, P_, Z5))
    # the Euler products
    qm = st([nnn, rpr, w.inst('gf2qm')], 'syl2anc', '( %s e. RR /\\ %s e. RR )' % (L.QRP, L.MERT))
    qrr = st([qm], 'simpld', '%s e. RR' % L.QRP); mtr = st([qm], 'simprd', '%s e. RR' % L.MERT)
    cq = st([nnn, w.inst('z5dtotqr')], 'syl', '%s <_ %s' % (cN, L.QRP))
    P1_ = 'sum_ r e. %s ( 1 / r )' % RS_
    pp1 = st([nv, rpr, w.inst('z5phip1')], 'syl2anc', '%s <_ %s' % (PH_, P1_))
    r1 = st([st([dr, lin.linarith(w, a, [d1], '1 <_ D', leaves={'D': dr})], 'jca', '( D e. RR /\\ 1 <_ D )'),
             st([st([], '0red', '0 e. RR'), litr(w, a, '( 1 / ; ; 1 0 0 )')], 'jca', '( 0 e. RR /\\ ( 1 / ; ; 1 0 0 ) e. RR )'),
             litle(w, a, '0', '( 1 / ; ; 1 0 0 )'), w.inst('cxplea')], 'syl3anc', '( D ^c 0 ) <_ %s' % RP)
    c0 = st([st([dr], 'recnd', 'D e. CC'), w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1')
    rp1 = st([c0, r1], 'eqbrtrrd', '1 <_ %s' % RP)
    p1m = st([nnn, st([rpr, rp1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (RP, RP)), w.inst('z5dp1mert')], 'syl2anc', '%s <_ ( %s x. %s )' % (P1_, L.QRP, L.MERT))
    cr = st([crp], 'rpred', '%s e. RR' % cN)
    qr0 = st([st([], '0red', '0 e. RR'), cr, qrr, st([crp], 'rpge0d', '0 <_ %s' % cN), cq], 'letrd', '0 <_ %s' % L.QRP)
    KL = '( K x. ( log ` %s ) )' % RP
    klr = st([kr, st([rps], 'relogcld', '( log ` %s ) e. RR' % RP)], 'remulcld', '%s e. RR' % KL)
    qml = st([mtr, klr, qrr, qr0, mert], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (L.QRP, L.MERT, L.QRP, KL))
    lrp = st([drp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'logcxpd', '( log ` %s ) = ( ( 1 / ; ; 1 0 0 ) x. %s )' % (RP, YD))
    KL2 = '( K x. ( ( 1 / ; ; 1 0 0 ) x. %s ) )' % YD
    kle = st([lrp], 'oveq2d', '%s = %s' % (KL, KL2))
    qk2 = st([qml, st([kle], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (L.QRP, KL, L.QRP, KL2))], 'breqtrd', '( %s x. %s ) <_ ( %s x. %s )' % (L.QRP, L.MERT, L.QRP, KL2))
    p1r = st([rfi, sr_([sr_([rn], 'nnrecred', '( 1 / r ) e. RR')], 'idi', '( 1 / r ) e. RR')], 'fsumrecl', '%s e. RR' % P1_)
    qmr = st([qrr, mtr], 'remulcld', '( %s x. %s ) e. RR' % (L.QRP, L.MERT))
    X_ = '( %s x. %s )' % (L.QRP, KL2)
    xr_ = st([qrr, st([kr, st([litr(w, a, '( 1 / ; ; 1 0 0 )'), yr], 'remulcld', '( ( 1 / ; ; 1 0 0 ) x. %s ) e. RR' % YD)], 'remulcld', '%s e. RR' % KL2)], 'remulcld', '%s e. RR' % X_)
    phx = st([phr, p1r, xr_, pp1, st([p1r, qmr, xr_, p1m, qk2], 'letrd', '%s <_ %s' % (P1_, X_))], 'letrd', '%s <_ %s' % (PH_, X_))
    U_ = '( %s x. %s )' % (L.QRP, X_)
    cp = st([cr, qrr, phr, xr_, st([crp], 'rpge0d', '0 <_ %s' % cN), ph0, cq, phx], 'lemul12ad', '%s <_ %s' % (P_, U_))
    ur = st([qrr, xr_], 'remulcld', '%s e. RR' % U_)
    z50 = st([c7yr, w5r, c7y0, w50], 'mulge0d', '0 <_ %s' % Z5)
    uz = st([pr_, ur, z5r, z50, cp], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (P_, Z5, U_, Z5))
    TGT = split_imp(S_['gf2row'])[1].split(' <_ ', 1)[1]
    ue = st([qrr, kr, yr, w.inst('gf2alg')], 'syl3anc', '( %s x. %s ) = %s' % (U_, Z5, TGT))
    # chain
    e_sp = st([st([fm1], 'eqcomd', '%s = ( %s x. %s )' % (SP, P_, STK)), st([st([fm2], 'eqcomd', '%s = %s' % (STK, Z1_))], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (P_, STK, P_, Z1_))],
              'eqtrd', '%s = ( %s x. %s )' % (SP, P_, Z1_))
    sar = st([sf, mkr], 'fsumrecl', '%s e. RR' % SA)
    pz1 = st([pr_, z1r], 'remulcld', '( %s x. %s ) e. RR' % (P_, Z1_)); pz5 = st([pr_, z5r], 'remulcld', '( %s x. %s ) e. RR' % (P_, Z5))
    uz5 = st([ur, z5r], 'remulcld', '( %s x. %s ) e. RR' % (U_, Z5))
    c1 = st([sa, e_sp], 'breqtrd', '%s <_ ( %s x. %s )' % (SA, P_, Z1_))
    c2 = st([sar, pz1, pz5, c1, pz], 'letrd', '%s <_ ( %s x. %s )' % (SA, P_, Z5))
    c3 = st([sar, pz5, uz5, c2, uz], 'letrd', '%s <_ ( %s x. %s )' % (SA, U_, Z5))
    fin = st([c3, ue], 'breqtrd', '%s <_ %s' % (SA, TGT))
    # the frozen antecedent: rename the bound variables
    def cbv(P, x, y):
        idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, y, x, y))
        sb, _ = w.wcongr(P(x), {x: y}, '%s = %s' % (x, y), {x: idx})
        return sb
    e1 = w.s([cbv(P1, 'k', 'i')], 'cbvralvw', '( A. k e. S %s <-> A. i e. S %s )' % (P1('k'), P1('i')))
    e2 = w.s([cbv(P2, 'k', 'i')], 'cbvralvw', '( A. k e. S %s <-> A. i e. S %s )' % (P2('k'), P2('i')))
    e3a = w.s([cbv(lambda m: P3('k', m), 'm', 'u')], 'cbvralvw', '( A. m e. NN %s <-> A. u e. NN %s )' % (P3('k', 'm'), P3('k', 'u')))
    rq = w.s([cbv(lambda k: BIN(k, 'u'), 'k', 'y')], 'cbvrabv', '{ k e. S | %s } = { y e. S | %s }' % (BIN('k', 'u'), BIN('y', 'u')))
    e3b = w.s([w.s([rq], 'fveq2i', '( # ` { k e. S | %s } ) = ( # ` { y e. S | %s } )' % (BIN('k', 'u'), BIN('y', 'u')))], 'breq1i', '( %s <-> %s )' % (P3('k', 'u'), P3('y', 'u')))
    e3c = w.s([e3b], 'ralbii', '( A. u e. NN %s <-> A. u e. NN %s )' % (P3('k', 'u'), P3('y', 'u')))
    e3 = w.s([e3a, e3c], 'bitri', '( A. m e. NN %s <-> A. u e. NN %s )' % (P3('k', 'm'), P3('y', 'u')))
    X1k = '( S e. Fin /\\ A. k e. S %s )' % P1('k')
    X2k = '( A. k e. S %s /\\ A. m e. NN %s )' % (P2('k'), P3('k', 'm'))
    b1 = w.s([e1], 'anbi2i', '( %s <-> %s )' % (X1k, X1))
    b2 = w.s([e2, e3], 'anbi12i', '( %s <-> %s )' % (X2k, X2))
    b3 = w.s([b1, b2, w.s([], 'biid', '( %s <-> %s )' % (QK, QK))], '3anbi123i', '( ( %s /\\ %s /\\ %s ) <-> ( %s /\\ %s /\\ %s ) )' % (X1k, X2k, QK, X1, X2, QK))
    b4 = w.s([b3], 'anbi2i', '( %s <-> %s )' % (A0, a))
    w.qed([b4, fin], 'sylbi', S_['gf2row'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
