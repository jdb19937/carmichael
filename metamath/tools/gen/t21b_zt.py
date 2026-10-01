"""Sortie T21b: t21zt (the zone assembly)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from t21b_tr import basics
from c8lib import lin8
import cl as _cl

L = LX


def gen_zt():
    w = W('t21zt', 'The full weighted zero sum at ` T = X ^ 3 ` : zones I-IV at ` 39 / 50 <_ sigma* <_ tau ` total at most ` 4 E Y / 27 ` (Lean ` theta_AP_T21 ` 2146-2165; ~ t21z1 , ~ t21z2 , ~ t21z3 , ~ t21z4 , ~ t21split ).')
    A0, concl = split_imp(SB['t21zt'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    c = basics(w, A0, u)
    b = c['b']
    nn, xr, xe, yr, nx, ny, yx = c['nn'], c['xr'], c['xe'], c['yr'], c['nx'], c['ny'], c['yx']
    er = u['E e. RR']; e0 = u['0 < E']
    G_, g1, C_, c1, c2 = u['G e. RR'], u['1 <_ G'], u['C e. RR'], u['1 <_ C'], u['C <_ 2']
    LFB = LFD_BODY('G', 'C'); LGB = LGD_BODY('H', 'P', 'B', 'K')
    lfb, lgb = u[LFB], u[LGB]
    H_, h1, P_, p0, p72, B_, b1, b54, kn = u['H e. RR'], u['1 <_ H'], u['P e. RR'], u['0 <_ P'], u['P <_ ( 7 / 2 )'], u['B e. RR'], u['1 <_ B'], u['B <_ ( 5 / 4 )'], u['K e. NN0']
    rp_, vp = u['R e. RR+'], u['V e. RR+']
    EXZ = '( exp ` ( -u %s x. R ) )' % F9200
    E28 = '( exp ` ( ; 2 8 x. R ) )'
    h3 = u['( %s x. ( G x. %s ) ) <_ E' % (N6912, EXZ)]
    h4 = u['( ; 2 7 x. ( G x. %s ) ) <_ ( E x. V )' % E28]
    T4 = '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( X ^c %s ) )' % (N4320, L, F7900)
    T5 = '( ( %s x. ( 5 ^ K ) ) x. H ) <_ ( E x. ( %s ^c %s ) )' % (N50112, L, F92)
    t4, t5, t6 = u[T4], u[T5], u['( ; 1 8 x. %s ) <_ %s' % (CSL, L)]
    t7, t8 = u['R <_ %s' % CSL], u['( ; 4 0 x. R ) <_ %s' % L]
    HE = HEMPTY('N', X3, TAU, 'V')
    he = u[HE]
    lr = b['lr']; lp = s([lr, lin.linarith(w, A0, [b['l1']], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    rr = s([rp_], 'rpred', 'R e. RR')
    # sigma*, tau
    kr = s([kn], 'nn0red', 'K e. RR')
    LL = '( log ` %s )' % L
    llr = s([lp], 'relogcld', '%s e. RR' % LL)
    ll0 = s([lr, b['l1']], 'logge0d', '0 <_ %s' % LL)
    K2 = '( K + 2 )'
    k2r = s([kr, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % K2)
    k20 = lin.linarith(w, A0, [s([kn], 'nn0ge0d', '0 <_ K')], '0 <_ %s' % K2, leaves={'K': kr})
    csr = s([s([num.real(w, '; 5 0')], 'a1i', '; 5 0 e. RR'), s([k2r, llr], 'remulcld', '( %s x. %s ) e. RR' % (K2, LL))], 'remulcld', '%s e. RR' % CSL)
    cs0 = s([s([num.real(w, '; 5 0')], 'a1i', '; 5 0 e. RR'), s([k2r, llr], 'remulcld', '( %s x. %s ) e. RR' % (K2, LL)), s([num.ge0_nat(w, 50)], 'a1i', '0 <_ ; 5 0'), s([k2r, llr, k20, ll0], 'mulge0d', '0 <_ ( %s x. %s )' % (K2, LL))], 'mulge0d', '0 <_ %s' % CSL)
    Q = '( %s / %s )' % (CSL, L)
    qr = s([csr, lp], 'rerpdivcld', '%s e. RR' % Q)
    q0 = s([csr, lp, cs0], 'divge0d', '0 <_ %s' % Q)
    cs18 = lin8(w, A0, [t6], '%s <_ ( %s x. ( 1 / ; 1 8 ) )' % (CSL, L), {CSL: csr, L: lr})
    q18 = s([cs18, s([csr, s([num.real(w, '( 1 / ; 1 8 )')], 'a1i', '( 1 / ; 1 8 ) e. RR'), lp], 'ledivmuld', '( %s <_ ( 1 / ; 1 8 ) <-> %s <_ ( %s x. ( 1 / ; 1 8 ) ) )' % (Q, CSL, L))], 'mpbird', '%s <_ ( 1 / ; 1 8 )' % Q)
    RL = '( R / %s )' % L
    rlr = s([rr, lp], 'rerpdivcld', '%s e. RR' % RL)
    rl0 = s([rr, lp, s([rp_], 'rpge0d', '0 <_ R')], 'divge0d', '0 <_ %s' % RL)
    rlq = s([rr, csr, lp, t7], 'lediv1dd', '%s <_ %s' % (RL, Q))
    SS_ = SSTAR
    assert SS_ == '( 1 - %s )' % Q, SS_
    lv = {Q: qr, RL: rlr}
    cl = _cl.Closure(w, A0, {})
    for k_, st_ in lv.items():
        cl.leaf(k_, 'RR', st_); cl.atom(k_)
    s39 = lin.linarith(w, A0, [q18], '%s <_ %s' % (F3950, SS_), closure=cl)
    s910 = lin.linarith(w, A0, [q18], '%s <_ %s' % (F910, SS_), closure=cl)
    sst = lin.linarith(w, A0, [rlq], '%s <_ %s' % (SS_, TAU), closure=cl)
    t1_ = lin.linarith(w, A0, [rl0], '%s <_ 1' % TAU, closure=cl)
    ssr = s([s([], '1red', '1 e. RR'), qr], 'resubcld', '%s e. RR' % SS_)
    taur = s([s([], '1red', '1 e. RR'), rlr], 'resubcld', '%s e. RR' % TAU)
    clf = _cl.Closure(w, A0, {})
    for k_, st_ in (('C', C_), (Q, qr)):
        clf.leaf(k_, 'RR', st_); clf.atom(k_)
    fold = lin.nlinarith(w, A0, [c2, q18, q0, c1], '( C x. ( %s x. ( 1 - %s ) ) ) <_ %s' % (F92, SS_, HALF), closure=clf)
    r10 = lin8(w, A0, [t8, s([rp_], 'rpge0d', '0 <_ R')], '( ; 1 0 x. R ) <_ %s' % L, {'R': rr, L: lr})
    # zones
    ZS1 = ZS(X3, 'Y', HALF, F3950); ZS2 = ZS(X3, 'Y', F3950, SS_); ZS3 = ZS(X3, 'Y', SS_, TAU); ZT4 = ZT(X3, 'Y', TAU)
    EY27 = '( ( E x. Y ) / ; 2 7 )'
    z1 = ap(w, A0, [nn, xr, xe, yr, er, nx, ny, t4], 't21z1', '%s <_ %s' % (ZS1, EY27))
    z2 = ap(w, A0, [nn, xr, xe, yr, er, nx, ny, yx, H_, h1, P_, p0, p72, B_, b1, b54, kn, lgb, s39, t5], 't21z2', '%s <_ %s' % (ZS2, EY27))
    Z3R = '( ( ( ; ; 2 5 6 x. G ) x. Y ) x. %s )' % EXZ
    z3 = ap(w, A0, [nn, xr, xe, yr, nx, ny, yx, G_, g1, C_, c1, lfb, rp_, ssr, s910, sst, fold], 't21z3', '%s <_ %s' % (ZS3, Z3R))
    Z4R = '( ( ( G x. %s ) x. Y ) / V )' % E28
    z4 = ap(w, A0, [nn, xr, xe, nx, yr, c['y1'], G_, g1, C_, c2, lfb, rp_, vp, r10, he], 't21z4', '%s <_ %s' % (ZT4, Z4R))
    # zone III, IV into E Y / 27
    exr = s([s([s([num.real(w, F9200)], 'a1i', '%s e. RR' % F9200) and s([s([num.real(w, F9200)], 'a1i', '%s e. RR' % F9200)], 'renegcld', '-u %s e. RR' % F9200), rr], 'remulcld', '( -u %s x. R ) e. RR' % F9200)], 'reefcld', '%s e. RR' % EXZ)
    y0 = lin.linarith(w, A0, [c['y1']], '0 <_ Y', leaves={'Y': yr})
    GX = '( G x. %s )' % EXZ
    gxr = s([G_, exr], 'remulcld', '%s e. RR' % GX)
    m3 = s([s([s([num.real(w, N6912)], 'a1i', '%s e. RR' % N6912), gxr], 'remulcld', '( %s x. %s ) e. RR' % (N6912, GX)), er, yr, y0, h3], 'lemul1ad', '( ( %s x. %s ) x. Y ) <_ ( E x. Y )' % (N6912, GX))
    cl3 = _cl.Closure(w, A0, {})
    for k_, st_ in (('G', G_), (EXZ, exr), ('Y', yr)):
        cl3.leaf(k_, 'RR', st_); cl3.atom(k_)
    from mvlib import ringeq as ringeq_d
    r3 = ringeq_d(w, A0, '( ( %s x. %s ) x. Y )' % (N6912, GX), '( ; 2 7 x. %s )' % Z3R, cl3)
    z3r = s([s([s([s([num.real(w, '; ; 2 5 6')], 'a1i', '; ; 2 5 6 e. RR'), G_], 'remulcld', '( ; ; 2 5 6 x. G ) e. RR'), yr], 'remulcld', '( ( ; ; 2 5 6 x. G ) x. Y ) e. RR'), exr], 'remulcld', '%s e. RR' % Z3R)
    eyr = s([er, yr], 'remulcld', '( E x. Y ) e. RR')
    z3b = lin8(w, A0, [s([r3, m3], 'eqbrtrrd', '( ; 2 7 x. %s ) <_ ( E x. Y )' % Z3R)], '%s <_ %s' % (Z3R, EY27), {Z3R: z3r, '( E x. Y )': eyr})
    G28 = '( G x. %s )' % E28
    e28r = s([s([s([num.real(w, '; 2 8')], 'a1i', '; 2 8 e. RR'), rr], 'remulcld', '( ; 2 8 x. R ) e. RR')], 'reefcld', '%s e. RR' % E28)
    g28r = s([G_, e28r], 'remulcld', '%s e. RR' % G28)
    vr = s([vp], 'rpred', 'V e. RR')
    m4 = s([s([s([num.real(w, '; 2 7')], 'a1i', '; 2 7 e. RR'), g28r], 'remulcld', '( ; 2 7 x. %s ) e. RR' % G28), s([er, vr], 'remulcld', '( E x. V ) e. RR'), yr, y0, h4], 'lemul1ad',
           '( ( ; 2 7 x. %s ) x. Y ) <_ ( ( E x. V ) x. Y )' % G28)
    cl4 = _cl.Closure(w, A0, {})
    for k_, st_ in ((G28, g28r), ('Y', yr), ('E', er), ('V', vr)):
        cl4.leaf(k_, 'RR', st_); cl4.atom(k_)
    GY = '( %s x. Y )' % G28
    r4a = ringeq_d(w, A0, '( ( ; 2 7 x. %s ) x. Y )' % G28, '( ; 2 7 x. %s )' % GY, cl4)
    r4b = ringeq_d(w, A0, '( ( E x. V ) x. Y )' % (), '( V x. ( E x. Y ) )', cl4)
    m4b = s([s([s([r4a], 'eqcomd', '( ; 2 7 x. %s ) = ( ( ; 2 7 x. %s ) x. Y )' % (GY, G28)), m4], 'eqbrtrd', '( ; 2 7 x. %s ) <_ ( ( E x. V ) x. Y )' % GY), r4b], 'breqtrd', '( ; 2 7 x. %s ) <_ ( V x. ( E x. Y ) )' % GY)
    gyr = s([g28r, yr], 'remulcld', '%s e. RR' % GY)
    m4c = lin8(w, A0, [m4b], '%s <_ ( V x. %s )' % (GY, EY27), {GY: gyr, '( V x. ( E x. Y ) )': s([vr, eyr], 'remulcld', '( V x. ( E x. Y ) ) e. RR'), '( V x. %s )' % EY27: None}) if False else None
    ey27r = s([eyr, s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '%s e. RR' % EY27)
    cl5 = _cl.Closure(w, A0, {})
    for k_, st_ in (('V', vr), ('( E x. Y )', eyr)):
        cl5.leaf(k_, 'RR', st_); cl5.atom(k_)
    r5 = ringeq_d(w, A0, '( V x. ( E x. Y ) )', '( ; 2 7 x. ( V x. %s ) )' % EY27, cl5)
    vey = s([vr, ey27r], 'remulcld', '( V x. %s ) e. RR' % EY27)
    m4d = lin8(w, A0, [s([m4b, r5], 'breqtrd', '( ; 2 7 x. %s ) <_ ( ; 2 7 x. ( V x. %s ) )' % (GY, EY27))], '%s <_ ( V x. %s )' % (GY, EY27), {GY: gyr, '( V x. %s )' % EY27: vey})
    z4b = s([m4d, s([gyr, ey27r, vp], 'ledivmuld', '( ( %s / V ) <_ %s <-> %s <_ ( V x. %s ) )' % (GY, EY27, GY, EY27))], 'mpbird', '%s <_ %s' % (Z4R, EY27))
    # split
    x3r = b['x3r']
    ypp = s([yr, lin.linarith(w, A0, [c['y1']], '0 < Y', leaves={'Y': yr})], 'elrpd', 'Y e. RR+')
    f39 = s([num.real(w, F3950)], 'a1i', '%s e. RR' % F3950)
    h39 = s([num.le_lit(w, HALF, F3950)], 'a1i', '%s <_ %s' % (HALF, F3950))
    sp = ap(w, A0, [nn, x3r, ypp, f39, ssr, taur, h39, s39, sst, t1_], 't21split', '%s = ( ( ( %s + %s ) + %s ) + %s )' % (ZT(X3, 'Y', HALF), ZS1, ZS2, ZS3, ZT4))
    import t21alib as _ta
    zsr = lambda a_, b_: _ta.zs_real(w, A0, nn, s([num.real(w, a_)], 'a1i', '%s e. RR' % a_) if a_ in (HALF, F3950) else None, None, None, x3r, yr, y0, a_, b_, X3) if False else None
    lvf = {ZS1: None, ZS2: None, ZS3: None, ZT4: None, '( E x. Y )': eyr}
    # reals of the zone sums come from the bounds' left sides through the split equality: use letrd-free lin with closure facts
    z3f = s([z3, z3b], 'x', 'x') if False else None
    # zone sums are real: each <_ a real and >_ ... use the zs_real helper of T21a
    def zreal(a_, ar_, a0_, a1_, b_):
        return _ta.zs_real(w, A0, nn, ar_, a0_, a1_, x3r, yr, y0, a_, b_, X3)
    half_r = s([num.real(w, HALF)], 'a1i', '%s e. RR' % HALF)
    half0 = s([w.s([], 'halfgt0', '0 < %s' % HALF)], 'a1i', '0 < %s' % HALF)
    half1 = lin.linarith(w, A0, [s([w.s([], 'halflt1', '%s < 1' % HALF)], 'a1i', '%s < 1' % HALF)], '%s <_ 1' % HALF, leaves={HALF: half_r})
    f390 = s([num.le_lit(w, '0', F3950, strict=True)], 'a1i', '0 < %s' % F3950)
    f391 = s([num.le_lit(w, F3950, '1')], 'a1i', '%s <_ 1' % F3950)
    ss0 = lin.linarith(w, A0, [s39, f390], '0 < %s' % SS_, closure=cl) if False else lin.linarith(w, A0, [q18], '0 < %s' % SS_, closure=cl)
    ss1 = lin.linarith(w, A0, [q0], '%s <_ 1' % SS_, closure=cl)
    ta0 = lin.linarith(w, A0, [sst, q18], '0 < %s' % TAU, closure=cl)
    zr1 = zreal(HALF, half_r, half0, half1, F3950)
    zr2 = zreal(F3950, f39, f390, f391, SS_)
    zr3 = zreal(SS_, ssr, ss0, ss1, TAU)
    zr4 = s([zreal(TAU, taur, ta0, t1_, '1')], 'x', 'x') if False else None
    z4r = s([s([s([G_, e28r], 'remulcld', '%s e. RR' % G28), yr], 'remulcld', '( %s x. Y ) e. RR' % G28), vp], 'rerpdivcld', '%s e. RR' % Z4R)
    # ZT4 real: from t21split? use the bound ZT4 <_ Z4R and lower bound 0 <_ ZT4 is not needed: lin8 needs the atom real
    zt4r = s([s([s([sp, s([s([s([zr1, zr2], 'readdcld', '( %s + %s ) e. RR' % (ZS1, ZS2)), zr3], 'readdcld', '( ( %s + %s ) + %s ) e. RR' % (ZS1, ZS2, ZS3))], 'x', 'x')], 'x', 'x')], 'x', 'x')], 'x', 'x') if False else None
    ztr = ZTr = None
    # ZT4 real directly: finite double sum of reals (T21a's ws/zs pattern at a single abscissa)
    ZTR = _zt_real(w, A0, nn, taur, ta0, t1_, x3r, yr, y0)
    fin = lin8(w, A0, [sp, z1, z2, z3b, z4b, z3], '%s <_ ( ( 4 x. ( E x. Y ) ) / ; 2 7 )' % ZT(X3, 'Y', HALF),
               {ZT(X3, 'Y', HALF): None, ZS1: zr1, ZS2: zr2, ZS3: zr3, ZT4: ZTR, '( E x. Y )': eyr, Z3R: z3r}) if False else None
    fin = lin8(w, A0, [sp, z1, z2, s([z3, z3b], 'x', 'x') if False else s([zr3, z3r, ey27r, z3, z3b], 'letrd', '%s <_ %s' % (ZS3, EY27)), s([ZTR, z4r, ey27r, z4, z4b], 'letrd', '%s <_ %s' % (ZT4, EY27))],
               '%s <_ ( ( 4 x. ( E x. Y ) ) / ; 2 7 )' % ZT(X3, 'Y', HALF),
               {ZT(X3, 'Y', HALF): s([sp, s([s([s([zr1, zr2], 'readdcld', '( %s + %s ) e. RR' % (ZS1, ZS2)), zr3], 'readdcld', '( ( %s + %s ) + %s ) e. RR' % (ZS1, ZS2, ZS3)), ZTR], 'readdcld',
                                             '( ( ( %s + %s ) + %s ) + %s ) e. RR' % (ZS1, ZS2, ZS3, ZT4))], 'eqeltrd', '%s e. RR' % ZT(X3, 'Y', HALF)),
                ZS1: zr1, ZS2: zr2, ZS3: zr3, ZT4: ZTR, '( E x. Y )': eyr})
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21zt']))
    return go(w)


def _zt_real(w, A0, nn, ar, a0, a1, tr, yr, y0):
    """( A0 -> ZT(X3, Y, TAU) e. RR )"""
    import t21alib as _ta
    from cl import lift as lf
    tot, inf = _ta.nc_real(w, A0, nn, ar, a0, a1, tr, TAU, X3)
    C1, C2 = inf['C1'], inf['C2']
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, ZFX(TAU, X3)))
    qf = _ta.q_facts(w, C2, qin, lf(w, ar, C2), lf(w, tr, C2), TAU, X3)
    wr, w0, _ = _ta.wt_facts(w, C2, inf['orr'], inf['or0'], qf)
    yre = w.s([lf(w, yr, C2), lf(w, y0, C2), qf['re']], 'recxpcld', '( %s -> ( Y ^c ( Re ` q ) ) e. RR )' % C2)
    body = w.s([wr, yre], 'remulcld', '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) e. RR )' % (C2, WT()))
    inner = w.s([inf['zfin'], body], 'fsumrecl', '( %s -> sum_ q e. %s ( %s x. ( Y ^c ( Re ` q ) ) ) e. RR )' % (C1, ZFX(TAU, X3), WT()))
    return w.s([inf['dfin'], inner], 'fsumrecl', '( %s -> %s e. RR )' % (A0, ZT(X3, 'Y', TAU)))


if __name__ == '__main__':
    gen_zt()
