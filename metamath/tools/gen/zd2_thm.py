"""Sortie ZD2: Corollary 8.4 and Theorem M (Lean sum_good_le_density, sum_zeroCountBox_nonprincipal_le_of_thresholds,
sum_zeroCountBox_nonprincipal_le): zd2good, zd2mthr, zd2thm."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zd2_base import *
from zd2_gram import d_facts, ri_fin, G_
from zd2_cps import xbd_facts

CLOCR = CLOC
GAMKX = tsub(GAMK, {'K': CMX})


def cjk_facts(w, A, c, kr, k0, Kt='K'):
    """( A -> CLOC e. RR ), 0 <_ CLOC, CJK e. RR, 0 <_ CJK, GAMK e. RR, 0 <_ GAMK, at the Mertens constant text Kt
    (kr, k0 : Kt e. RR, 0 <_ Kt)"""
    C9K_, CJK_, GAMK_ = [tsub(x, {'K': Kt}) for x in (C9K, CJK, GAMK)]
    three = c([numst(w, A, '3', 'RR'), numst(w, A, KL, 'RR')], 'readdcld', '( 3 + %s ) e. RR' % KL)
    three0 = lin8(w, A, [], '0 <_ ( 3 + %s )' % KL, {})
    clr = c([numst(w, A, '5', 'RR'), three], 'remulcld', '%s e. RR' % CLOC)
    cl0 = c([numst(w, A, '5', 'RR'), three, numst(w, A, '5', 'ge0'), three0], 'mulge0d', '0 <_ %s' % CLOC)
    l400 = c([numst(w, A, '; ; 4 0 0', 'RR+')], 'relogcld', '( log ` ; ; 4 0 0 ) e. RR')
    l4000 = c([numst(w, A, '; ; 4 0 0', 'RR'), lin8(w, A, [], '1 <_ ; ; 4 0 0', {}), w.inst('logge0')], 'syl2anc', '0 <_ ( log ` ; ; 4 0 0 )')
    FAC = '( 5 + ( 2 x. ( log ` ; ; 4 0 0 ) ) )'
    facr = c([numst(w, A, '5', 'RR'), c([numst(w, A, '2', 'RR'), l400], 'remulcld', '( 2 x. ( log ` ; ; 4 0 0 ) ) e. RR')], 'readdcld', '%s e. RR' % FAC)
    fac0 = lin8(w, A, [l4000], '0 <_ %s' % FAC, {'( log ` ; ; 4 0 0 )': l400})
    kc7r = c([kr, numst(w, A, C7, 'RR')], 'remulcld', '( %s x. %s ) e. RR' % (Kt, C7))
    kc70 = c([kr, numst(w, A, C7, 'RR'), k0, numst(w, A, C7, 'ge0')], 'mulge0d', '0 <_ ( %s x. %s )' % (Kt, C7))
    c9r = c([kc7r, facr], 'remulcld', '%s e. RR' % C9K_); c90 = c([kc7r, facr, kc70, fac0], 'mulge0d', '0 <_ %s' % C9K_)
    p = c([numst(w, A, N3200, 'RR'), numst(w, A, C12, 'RR')], 'remulcld', '( %s x. %s ) e. RR' % (N3200, C12))
    p0 = c([numst(w, A, N3200, 'RR'), numst(w, A, C12, 'RR'), numst(w, A, N3200, 'ge0'), numst(w, A, C12, 'ge0')], 'mulge0d', '0 <_ ( %s x. %s )' % (N3200, C12))
    cjr = c([p, c9r], 'remulcld', '%s e. RR' % CJK_); cj0 = c([p, c9r, p0, c90], 'mulge0d', '0 <_ %s' % CJK_)
    cc = c([clr, cjr], 'remulcld', '( %s x. %s ) e. RR' % (CLOC, CJK_)); cc0 = c([clr, cjr, cl0, cj0], 'mulge0d', '0 <_ ( %s x. %s )' % (CLOC, CJK_))
    gr = c([numst(w, A, N20, 'RR'), cc], 'remulcld', '%s e. RR' % GAMK_); g0 = c([numst(w, A, N20, 'RR'), cc, numst(w, A, N20, 'ge0'), cc0], 'mulge0d', '0 <_ %s' % GAMK_)
    return dict(clr=clr, cl0=cl0, cjr=cjr, cj0=cj0, gr=gr, g0=g0)


def gen_good():
    w = W('zd2good', 'Corollary 8.4 (Lean ` sum_good_le_density ` ): under ` 200 <_ L ` , (T1), (T2), the ` chi_0 ` height clause and Mertens, the good zero mass over ` Y ` is at most ` gamma_m D ^ ( ( 5 / 2 ) ( 1 - S ) ) ` , ` gamma_m = 20 Cloc CJ ` ( ~ zrsg , ~ zd2cps at both parities, ~ zdgood ).')
    A0 = ante_of(S['zd2good'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0, l200, kr, k0 = [c.g(x) for x in ('N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '; ; 2 0 0 <_ %s' % LD, 'K e. RR', '0 <_ K')]
    f = d_facts(w, A0, c, nn_, tr, t0)
    _, yf = ri_fin(w, A0, c, nn_, ys)
    xp, xbp, xbr, xb0 = xbd_facts(w, A0, c, f, sr)
    kf = cjk_facts(w, A0, c, kr, k0)
    ss = c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS); tt = c([tr, t0], 'jca', TT)
    # the two parity counts
    def cps(p, pst):
        CP = tsub(S['zd2cps'], {'P': p})
        cpa, cpc = ante_of(CP)
        return c([c([c([], 'id', A0), pst], 'jca', cpa), w.inst('zd2cps')], 'syl', cpc)
    c0 = cps('0', numst(w, A0, '0', 'RR')); c1 = cps('1', numst(w, A0, '1', 'RR'))
    J0, J1 = '( # ` %s )' % RI('0'), '( # ` %s )' % RI('1')
    def hcnt(p, rif):
        h = c([rif, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RI(p))
        return c([h], 'nn0red', '( # ` %s ) e. RR' % RI(p)), c([h], 'nn0ge0d', '0 <_ ( # ` %s )' % RI(p))
    xpf = c([yf, c([], 'fzfid', '( 0 ... %s ) e. Fin' % QP), w.inst('xpfi')], 'syl2anc', '( Y X. ( 0 ... %s ) ) e. Fin' % QP)
    rif1 = c([xpf, w.inst('rabfi')], 'syl', '%s e. Fin' % RI('1'))
    rif0 = c([xpf, w.inst('rabfi')], 'syl', '%s e. Fin' % RI('0'))
    j0r, j00 = hcnt('0', rif0); j1r, j10 = hcnt('1', rif1)
    # zrsg
    SG = ante_of(stmt('zrsg'))
    l25 = lin8(w, A0, [l200], '; 2 5 <_ %s' % LD, {LD: f['lr']})
    sg = c([c([c([c([nn_, ys], 'jca', '( N e. NN /\\ Y C_ %s )' % DB_N), yf], 'jca', NY), c([ss, tt], 'jca', '( %s /\\ %s )' % (SS, TT)), l25], '3jca', SG[0]), w.inst('zrsg')], 'syl', SG[1])
    # zdgood
    GD = tsub(stmt('zdgood'), {'D': DSC, 'T': 'S', 'A': CLOC, 'B': CJK, 'J': J0, 'K': J1})
    gda, gdc = ante_of(GD)
    CXB = '( %s x. %s )' % (CJK, XBD)
    gd = c([c([c([c([c([f['dr'], f['d1']], 'jca', '( %s e. RR /\\ 1 < %s )' % (DSC, DSC)), c([sr, s1], 'jca', '( S e. RR /\\ S <_ 1 )')], 'jca', '( ( %s e. RR /\\ 1 < %s ) /\\ ( S e. RR /\\ S <_ 1 ) )' % (DSC, DSC)),
                   c([c([kf['clr'], kf['cl0']], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (CLOC, CLOC)), c([kf['cjr'], kf['cj0']], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (CJK, CJK))], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (CLOC, CLOC, CJK, CJK))], 'jca', top_and(gda)[0]),
                c([c([c([j0r, j00], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (J0, J0)), c0], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ %s <_ %s )' % (J0, J0, J0, CXB)),
                   c([c([j1r, j10], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (J1, J1)), c1], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ %s <_ %s )' % (J1, J1, J1, CXB))], 'jca', top_and(gda)[1])], 'jca', gda), w.inst('zdgood')], 'syl', gdc)
    assert gdc == '( ( %s x. ( 1 + %s ) ) x. ( %s + %s ) ) <_ ( %s x. %s )' % (CLOC, LAM, J0, J1, GAMK, DPOW), gdc
    gs = c([kf['clr'], c([c([], '1red', '1 e. RR'), c([c([c([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR'), f['lr']], 'remulcld', '%s e. RR' % LAM)], 'readdcld', '( 1 + %s ) e. RR' % LAM)], 'remulcld', '( %s x. ( 1 + %s ) ) e. RR' % (CLOC, LAM))
    mid = c([gs, c([j0r, j1r], 'readdcld', '( %s + %s ) e. RR' % (J0, J1))], 'remulcld', '( ( %s x. ( 1 + %s ) ) x. ( %s + %s ) ) e. RR' % (CLOC, LAM, J0, J1))
    dp = c([c([f['drp'], c([numst(w, A0, F52, 'RR'), c([c([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '( %s x. ( 1 - S ) ) e. RR' % F52)], 'rpcxpcld', '%s e. RR+' % DPOW)], 'rpred', '%s e. RR' % DPOW)
    rhs = c([kf['gr'], dp], 'remulcld', '( %s x. %s ) e. RR' % (GAMK, DPOW))
    # GOODS(Y) e. RR: from zrsg's typing? derive from the inequality's left side: use fsumrecl through ZR's facts is heavy; instead: the sum is real because it is bounded? no: use zrfib-free route: each inner sum is a finite sum of NN orders (ezf)
    # under NYS alone (HGOOD binds x): the outer sum is real
    cn = Ctx(w, NYS)
    nn2, ys2, sr2, s992, s12, tr2 = [cn.g(x) for x in ('N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR')]
    yf2 = ri_fin(w, NYS, cn, nn2, ys2)[1]
    Ax = '( %s /\\ x e. Y )' % NYS
    cx = Ctx(w, Ax)
    xb = cx([lift(w, ys2, Ax), cx([], 'simpr', 'x e. Y')], 'sseldd', 'x e. %s' % DB_N)
    EZ = tsub(stmt('ezf'), {'X': 'x', 'A': 'S'})
    eza, ezc = ante_of(EZ)
    ez = cx([cx([cx([lift(w, nn2, Ax), xb], 'jca', '( N e. NN /\\ x e. %s )' % DB_N), cx([cx([lift(w, sr2, Ax), lift(w, lin8(w, NYS, [s992], '0 < S', {'S': sr2}), Ax), lift(w, s12, Ax)], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), lift(w, tr2, Ax)], 'jca', '( ( S e. RR /\\ 0 < S /\\ S <_ 1 ) /\\ T e. RR )')], 'jca', eza), w.inst('ezf')], 'syl', ezc)
    GX = '{ v e. %s | v e. G }' % ZFX('x')
    zfin = cx([ez], 'simpld', '%s e. Fin' % ZFX('x'))
    gfin = cx([zfin, cx.a1(w.s([], 'ssrab2', '%s C_ %s' % (GX, ZFX('x'))), '%s C_ %s' % (GX, ZFX('x'))), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % GX)
    Aq = '( %s /\\ q e. %s )' % (Ax, GX)
    cq = Ctx(w, Aq)
    qz = cq([cq([], 'simpr', 'q e. %s' % GX), w.inst('elrabi')], 'syl', 'q e. %s' % ZFX('x'))
    ordn = cq([lift(w, cx([ez], 'simprd', 'A. q e. %s %s e. NN' % (ZFX('x'), ORDX('x', 'q'))), Aq), qz, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (ZFX('x'), ORDX('x', 'q'), ZFX('x'), ORDX('x', 'q')))], 'sylc', '%s e. NN' % ORDX('x', 'q'))
    inner = cx([gfin, cq([ordn], 'nnred', '%s e. RR' % ORDX('x', 'q'))], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (GX, ORDX('x', 'q')))
    goods = lift(w, cn([yf2, inner], 'fsumrecl', '%s e. RR' % GOODS('Y')), A0)
    w.qed([goods, mid, rhs, sg, gd], 'letrd', S['zd2good'])
    return go(w)


def gen_mthr():
    w = W('zd2mthr', 'Theorem M with explicit thresholds (Lean ` sum_zeroCountBox_nonprincipal_le_of_thresholds ` ): ` sum_{ chi =/= chi_0 } N ( S , T , chi ) <_ gamma_m ( N ( T + 2 ) ) ^ ( ( 5 / 2 ) ( 1 - S ) ) ` under ` 200 <_ L ` , (T1), (T2) and Mertens ( ~ zd2good with every zero good and ` Y ` the nonprincipal characters).')
    A0 = ante_of(S['zd2mthr'])[0]
    c = Ctx(w, A0)
    nn_, sr, s99, s1, tr, t0, l200, t1g, t2g, kr, k0, mer = [c.g(x) for x in ('N e. NN', 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '; ; 2 0 0 <_ %s' % LD, T1G, T2G, 'K e. RR', '0 <_ K', '%s <_ ( K x. ( log ` %s ) )' % (MERTD, RPD))]
    YD = '( %s \\ { %s } )' % (DB_N, X0)
    ys = c.a1(w.s([], 'difss', '%s C_ %s' % (YD, DB_N)), '%s C_ %s' % (YD, DB_N))
    ss = c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS); tt = c([tr, t0], 'jca', TT)
    # HGOOD at G := CC, Y := YD is vacuous
    HG = tsub(HGOOD, {'Y': YD, 'G': 'CC'})
    Ax = '( %s /\\ x e. %s )' % (A0, YD)
    cx = Ctx(w, Ax)
    ne = cx([cx([cx([], 'simpr', 'x e. %s' % YD), w.s([], 'eldifsn', '( x e. %s <-> ( x e. %s /\\ x =/= %s ) )' % (YD, DB_N, X0))], 'sylib', '( x e. %s /\\ x =/= %s )' % (DB_N, X0))], 'simprd', 'x =/= %s' % X0)
    nne = cx([ne], 'neneqd', '-. x = %s' % X0)
    BODYZ = 'A. z e. CC %s <_ ( abs ` ( Im ` z ) )' % LAMG
    imp = cx([nne], 'pm2.21d', '( x = %s -> %s )' % (X0, BODYZ))
    hg = c([imp], 'ralrimiva', HG)
    assert HG == 'A. x e. %s ( x = %s -> %s )' % (YD, X0, BODYZ), HG
    GD = tsub(S['zd2good'], {'Y': YD, 'G': 'CC'})
    gda, gdc = ante_of(GD)
    nys = c([c([nn_, ys], 'jca', '( N e. NN /\\ %s C_ %s )' % (YD, DB_N)), c([ss, tt], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', tsub(NYS, {'Y': YD}))
    thr = c([c([l200, t1g], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (LD, T1G)), c([t2g, hg], 'jca', '( %s /\\ %s )' % (T2G, HG))], 'jca', tsub(THR, {'Y': YD, 'G': 'CC'}))
    mk = c([c([kr, k0], 'jca', '( K e. RR /\\ 0 <_ K )'), mer], 'jca', MK)
    gd = c([c([nys, thr, mk], '3jca', gda), w.inst('zd2good')], 'syl', gdc)
    # { v e. ZFX(x) | v e. CC } = ZFX(x) under x e. YD
    ic = cx.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    CA, CB = '( S + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
    cac = cx([cx([lift(w, sr, Ax)], 'recnd', 'S e. CC'), cx([ic, cx([cx([lift(w, tr, Ax)], 'renegcld', '-u T e. RR')], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = cx([cx([], '1cnd', '1 e. CC'), cx([ic, cx([lift(w, tr, Ax)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CB)
    bss = cx([cac, cbc, w.inst('crectss')], 'syl2anc', '%s C_ CC' % BOXR)
    zss = cx([cx.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZFX('x'), BOXR)), '%s C_ %s' % (ZFX('x'), BOXR)), bss], 'sstrd', '%s C_ CC' % ZFX('x'))
    Av = '( %s /\\ v e. %s )' % (Ax, ZFX('x'))
    vc = w.s([lift(w, zss, Av), w.s([], 'simpr', '( %s -> v e. %s )' % (Av, ZFX('x')))], 'sseldd', '( %s -> v e. CC )' % Av)
    al = cx([vc], 'ralrimiva', 'A. v e. %s v e. CC' % ZFX('x'))
    GCC = '{ v e. %s | v e. CC }' % ZFX('x')
    ge = cx([al, w.s([], 'rabid2', '( %s = %s <-> A. v e. %s v e. CC )' % (ZFX('x'), GCC, ZFX('x')))], 'sylibr', '%s = %s' % (ZFX('x'), GCC))
    se = c([cx([ge], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (ZFX('x'), ORDX('x', 'q'), GCC, ORDX('x', 'q')))], 'sumeq2dv', '%s = %s' % (NCNP('N', 'S', 'T'), tsub(GOODS(YD), {'G': 'CC'})))
    assert gdc.startswith(tsub(GOODS(YD), {'G': 'CC'}) + ' <_ '), gdc[:300]
    w.qed([se, gd], 'eqbrtrd', S['zd2mthr'])
    return go(w)


def cmx_facts(w, A, c):
    """( A -> CMX e. RR ), ( A -> 0 <_ CMX )"""
    l4 = c([numst(w, A, '4', 'RR+')], 'relogcld', '( log ` 4 ) e. RR')
    l2p = c([numst(w, A, '2', 'RR'), lin8(w, A, [], '1 < 2', {})], 'rplogcld', '( log ` 2 ) e. RR+')
    l2 = c([l2p], 'rpred', '( log ` 2 ) e. RR'); l2n = c([l2p], 'rpne0d', '( log ` 2 ) =/= 0')
    ll2 = c([l2p], 'relogcld', '( log ` ( log ` 2 ) ) e. RR')
    num_ = c([numst(w, A, '2', 'RR'), c([l4, numst(w, A, '4', 'RR')], 'readdcld', '( ( log ` 4 ) + 4 ) e. RR')], 'remulcld', '( 2 x. ( ( log ` 4 ) + 4 ) ) e. RR')
    q = c([num_, l2, l2n], 'redivcld', '( ( 2 x. ( ( log ` 4 ) + 4 ) ) / ( log ` 2 ) ) e. RR')
    arg = c([c([numst(w, A, '3', 'RR'), q], 'readdcld', '( 3 + ( ( 2 x. ( ( log ` 4 ) + 4 ) ) / ( log ` 2 ) ) ) e. RR'), ll2], 'resubcld', '( ( 3 + ( ( 2 x. ( ( log ` 4 ) + 4 ) ) / ( log ` 2 ) ) ) - ( log ` ( log ` 2 ) ) ) e. RR')
    assert '( exp ` %s )' % strip_ante(formula_of(w, arg), A)[:-len(' e. RR')] == CMX
    er = c([arg], 'reefcld', '%s e. RR' % CMX)
    e0 = c([c([arg], 'rpefcld', '%s e. RR+' % CMX)], 'rpge0d', '0 <_ %s' % CMX)
    return er, e0


def gen_thm():
    w = W('zd2thm', 'Theorem M, the frozen unconditional form (Lean ` sum_zeroCountBox_nonprincipal_le ` ): there are ` gamma_m >_ 0 ` and ` D_0 >_ 1 ` with ` sum_{ chi =/= chi_0 } N ( s , t , chi ) <_ gamma_m ( n ( t + 2 ) ) ^ ( ( 5 / 2 ) ( 1 - s ) ) ` for every modulus ` n ` , ` t >_ 2 ` , ` 99 / 100 <_ s <_ 1 ` and ` n ( t + 2 ) >_ D_0 ` ( ~ zd2mthr at the thresholds ~ zd2thr and the Mertens constant of ~ zdmert ).')
    THRB = 'A. v e. RR ( u <_ v -> ( ; ; 2 0 0 <_ ( log ` v ) /\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 7 9 / ; ; ; 4 0 0 0 ) ) /\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 1 3 / ; ; 5 0 0 ) ) ) )' % (A1C, B2C)
    assert S['zd2thr'] == 'E. u e. RR ( 1 <_ u /\\ %s )' % THRB, S['zd2thr']
    AU = '( u e. RR /\\ ( 1 <_ u /\\ %s ) )' % THRB
    cu = Ctx(w, AU)
    ur, u1, thrb = cu.g('u e. RR'), cu.g('1 <_ u'), cu.g(THRB)
    # the point
    PTA = '( ( 2 <_ t /\\ ( %s <_ s /\\ s <_ 1 ) ) /\\ b <_ ( n x. ( t + 2 ) ) )' % F99
    PTAu = tsub(PTA, {'b': 'u'})
    A3 = '( ( ( ( %s /\\ n e. NN ) /\\ t e. RR ) /\\ s e. RR ) /\\ %s )' % (AU, PTAu)
    c3 = Ctx(w, A3)
    nn_, tr, sr = [c3.g(x) for x in ('n e. NN', 't e. RR', 's e. RR')]
    t2, s99, s1, ud = [c3.g(x) for x in ('2 <_ t', '%s <_ s' % F99, 's <_ 1', 'u <_ ( n x. ( t + 2 ) )')]
    DN = '( n x. ( t + 2 ) )'
    SUB = {'N': 'n', 'T': 't', 'S': 's'}
    LDn = tsub(LD, SUB)
    dn = c3([c3([nn_], 'nnred', 'n e. RR'), c3([tr, numst(w, A3, '2', 'RR')], 'readdcld', '( t + 2 ) e. RR')], 'remulcld', '%s e. RR' % DN)
    at, newt = ral_at(w, A3, lift(w, thrb, A3), 'v', DN, '( u <_ v -> ( ; ; 2 0 0 <_ ( log ` v ) /\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 7 9 / ; ; ; 4 0 0 0 ) ) /\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 1 3 / ; ; 5 0 0 ) ) ) )' % (A1C, B2C), dn)
    thr = c3([ud, at], 'mpd', '( ; ; 2 0 0 <_ %s /\\ %s /\\ %s )' % (LDn, tsub(T1G, SUB), tsub(T2G, SUB)))
    l200 = c3([thr], 'simp1d', '; ; 2 0 0 <_ %s' % LDn); t1 = c3([thr], 'simp2d', tsub(T1G, SUB)); t2g = c3([thr], 'simp3d', tsub(T2G, SUB))
    t0 = lin8(w, A3, [t2], '0 <_ t', {'t': tr})
    # Mertens at RPD(n,t) with the explicit constant
    RPn = tsub(RPD, SUB)
    d2 = lin8(w, A3, [c3([nn_], 'nnge1d', '1 <_ n'), c3([c3([nn_], 'nnred', 'n e. RR'), tr, lin8(w, A3, [c3([nn_], 'nnge1d', '1 <_ n')], '0 <_ n', {'n': c3([nn_], 'nnred', 'n e. RR')}), t0], 'mulge0d', '0 <_ ( n x. t )')], '2 <_ %s' % DN, {'n': c3([nn_], 'nnred', 'n e. RR'), 't': tr}, products=True)
    drp = c3([dn, lin8(w, A3, [d2], '0 < %s' % DN, {DN: dn})], 'elrpd', '%s e. RR+' % DN)
    rpr = c3([drp, numst(w, A3, '( 1 / ; ; 1 0 0 )', 'RR')], 'rpcxpcld', '%s e. RR+' % RPn)
    two = c3([c3([drp, l200], 'jca', '( %s e. RR+ /\\ ; ; 2 0 0 <_ %s )' % (DN, LDn)), w.inst('zd2rpar')], 'syl', '2 <_ %s' % RPn)
    MT = tsub(stmt('zdmert'), {'R': RPn})
    mta, mtc = ante_of(MT)
    mt = c3([c3([c3([rpr], 'rpred', '%s e. RR' % RPn), two], 'jca', mta), w.inst('zdmert')], 'syl', mtc)
    cmr, cm0 = cmx_facts(w, A3, c3)
    MH = tsub(S['zd2mthr'], dict(SUB, K=CMX))
    mha, mhc = ante_of(MH)
    Q = top_and(mha)
    mh = c3([c3([c3([nn_, c3([c3([sr, c3([s99, s1], 'jca', '( %s <_ s /\\ s <_ 1 )' % F99)], 'jca', tsub(SS, SUB)), c3([tr, t0], 'jca', tsub(TT, SUB))], 'jca', '( %s /\\ %s )' % (tsub(SS, SUB), tsub(TT, SUB)))], 'jca', Q[0]),
                 c3([c3([l200, t1], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (LDn, tsub(T1G, SUB))), t2g], 'jca', Q[1]), c3([c3([cmr, cm0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (CMX, CMX)), mt], 'jca', Q[2])], '3jca', mha), w.inst('zd2mthr')], 'syl', mhc)
    BODY = tsub(MBODY('n', 't', 's'), {'a': GAMKX, 'b': 'u'})
    assert BODY == '( %s -> %s )' % (PTAu, mhc), (BODY[:200], mhc[:200])
    A2 = '( ( ( %s /\\ n e. NN ) /\\ t e. RR ) /\\ s e. RR )' % AU
    st = w.s([mh], 'ex', '( %s -> %s )' % (A2, BODY))
    r1 = w.s([st], 'ralrimiva', '( ( ( %s /\\ n e. NN ) /\\ t e. RR ) -> A. s e. RR %s )' % (AU, BODY))
    r2 = w.s([r1], 'ralrimiva', '( ( %s /\\ n e. NN ) -> A. t e. RR A. s e. RR %s )' % (AU, BODY))
    r3 = w.s([r2], 'ralrimiva', '( %s -> A. n e. NN A. t e. RR A. s e. RR %s )' % (AU, BODY))
    cmr_u, cm0_u = cmx_facts(w, AU, cu)
    kf = cjk_facts(w, AU, cu, cmr_u, cm0_u, Kt=CMX)
    consts = cu([cu([kf['gr'], kf['g0']], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (GAMKX, GAMKX)), cu([ur, u1], 'jca', '( u e. RR /\\ 1 <_ u )')], 'jca',
                '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( u e. RR /\\ 1 <_ u ) )' % (GAMKX, GAMKX))
    MAT = S['zd2thm'][len('E. a E. b '):]
    MAT_g = tsub(MAT, {'a': GAMKX}); MAT_gu = tsub(MAT_g, {'b': 'u'})
    full = cu([consts, r3], 'jca', MAT_gu)
    st_b, chk = w.wcongr(MAT_g, {'b': 'u'}, 'b = u', {'b': w.s([], 'id', '( b = u -> b = u )')})
    assert chk == MAT_gu, chk[:200]
    exb = w.s([w.s([], 'vex', 'u e. _V'), st_b], 'spcev', '( %s -> E. b %s )' % (MAT_gu, MAT_g))
    st_a0, chk2 = w.wcongr(MAT, {'a': GAMKX}, 'a = %s' % GAMKX, {'a': w.s([], 'id', '( a = %s -> a = %s )' % (GAMKX, GAMKX))})
    assert chk2 == MAT_g, chk2[:200]
    st_a = w.s([st_a0], 'exbidv', '( a = %s -> ( E. b %s <-> E. b %s ) )' % (GAMKX, MAT, MAT_g))
    exa = w.s([w.s([], 'ovex', '%s e. _V' % GAMKX), st_a], 'spcev', '( E. b %s -> E. a E. b %s )' % (MAT_g, MAT))
    e1 = cu([full, cu.a1(exb, formula_of(w, exb))], 'mpd', 'E. b %s' % MAT_g)
    e2 = cu([e1, cu.a1(exa, formula_of(w, exa))], 'mpd', 'E. a E. b %s' % MAT)
    rl = w.s([e2], 'rexlimiva', '( %s -> E. a E. b %s )' % (S['zd2thr'], MAT))
    w.qed([w.s([], 'zd2thr', S['zd2thr']), rl], 'ax-mp', S['zd2thm'])
    return go(w)


GENS = {'zd2good': gen_good, 'zd2mthr': gen_mthr, 'zd2thm': gen_thm}

if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
