"""Sortie ZR: zrlan (Lean re_LSeries_vonMangoldt_le_sub_zeros / _le / _le_of_zero in one statement)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of
from zr_c import eta_nz
from zr_e import f2ne0


def sq_mem(w, A, tr, X, xr, Y, yr, hyps, lv):
    """( A -> ( X + ( _i x. Y ) ) e. SQ13(T) ) from lin hyps giving 3/8 <_ X <_ 29/8 and T - 13/8 <_ Y <_ T + 13/8"""
    c = Ctx(w, A)
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    cl = Closure(w, A, {'T': ('RR', tr), '_i': ('CC', ic)})
    cl.atom('T'); cl.atom('_i')
    SA = '( %s - ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('T')
    SB = '( %s + ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('T')
    FA, FB = '( ( 3 / 8 ) + ( _i x. ( T - ( ; 1 3 / 8 ) ) ) )', '( ( ; 2 9 / 8 ) + ( _i x. ( T + ( ; 1 3 / 8 ) ) ) )'
    ea = ringeq(w, A, SA, FA, cl); eb = ringeq(w, A, SB, FB, cl)
    c38, c298 = numst8(w, A, '( 3 / 8 )', 'RR'), numst8(w, A, '( ; 2 9 / 8 )', 'RR')
    tm = c([tr, numst8(w, A, '( ; 1 3 / 8 )', 'RR')], 'resubcld', '( T - ( ; 1 3 / 8 ) ) e. RR')
    tp = c([tr, numst8(w, A, '( ; 1 3 / 8 )', 'RR')], 'readdcld', '( T + ( ; 1 3 / 8 ) ) e. RR')
    ra = c([c([ea], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (SA, FA)), c([c38, tm, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 3 / 8 )' % FA)], 'eqtrd', '( Re ` %s ) = ( 3 / 8 )' % SA)
    rb = c([c([eb], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (SB, FB)), c([c298, tp, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( ; 2 9 / 8 )' % FB)], 'eqtrd', '( Re ` %s ) = ( ; 2 9 / 8 )' % SB)
    ia = c([c([ea], 'fveq2d', '( Im ` %s ) = ( Im ` %s )' % (SA, FA)), c([c38, tm, w.inst('crim')], 'syl2anc', '( Im ` %s ) = ( T - ( ; 1 3 / 8 ) )' % FA)], 'eqtrd', '( Im ` %s ) = ( T - ( ; 1 3 / 8 ) )' % SA)
    ib = c([c([eb], 'fveq2d', '( Im ` %s ) = ( Im ` %s )' % (SB, FB)), c([c298, tp, w.inst('crim')], 'syl2anc', '( Im ` %s ) = ( T + ( ; 1 3 / 8 ) )' % FB)], 'eqtrd', '( Im ` %s ) = ( T + ( ; 1 3 / 8 ) )' % SB)
    sac, sbc = cl.mem(SA, 'CC'), cl.mem(SB, 'CC')
    RA, RB, IA, IB = ['( %s ` %s )' % (f, x) for f, x in (('Re', SA), ('Re', SB), ('Im', SA), ('Im', SB))]
    rar, rbr = c([sac], 'recld', '%s e. RR' % RA), c([sbc], 'recld', '%s e. RR' % RB)
    iar, ibr = c([sac], 'imcld', '%s e. RR' % IA), c([sbc], 'imcld', '%s e. RR' % IB)
    lv2 = dict(lv); lv2.update({RA: rar, RB: rbr, IA: iar, IB: ibr, 'T': tr, X: xr, Y: yr})
    i1 = c([c([xr, lin8(w, A, [ra] + hyps, '%s <_ %s' % (RA, X), lv2), lin8(w, A, [rb] + hyps, '%s <_ %s' % (X, RB), lv2)], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (X, RA, X, X, RB)),
            c([rar, rbr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (X, RA, RB, X, RA, X, X, RB))], 'mpbird', '%s e. ( %s [,] %s )' % (X, RA, RB))
    i2 = c([c([yr, lin8(w, A, [ia] + hyps, '%s <_ %s' % (IA, Y), lv2), lin8(w, A, [ib] + hyps, '%s <_ %s' % (Y, IB), lv2)], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (Y, IA, Y, Y, IB)),
            c([iar, ibr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (Y, IA, IB, Y, IA, Y, Y, IB))], 'mpbird', '%s e. ( %s [,] %s )' % (Y, IA, IB))
    P = '( %s + ( _i x. %s ) )' % (X, Y)
    return c([c([c([sac, sbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), c([i1, i2], 'jca', '( %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) )' % (X, RA, RB, Y, IA, IB))], 'jca',
                 '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) ) )' % (SA, SB, X, RA, RB, Y, IA, IB)), w.inst('crectpt')], 'syl', '%s e. %s' % (P, SQ13('T')))


def ne0_by_re(w, A, zc, rez_ne0, Z):
    """( A -> Z =/= 0 ) from ( A -> ( Re ` Z ) =/= 0 )"""
    c = Ctx(w, A)
    RZ = '( Re ` %s )' % Z
    imp = c.a1(w.s([w.s([], 'fveq2', '( %s = 0 -> %s = ( Re ` 0 ) )' % (Z, RZ)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> %s = 0 )' % (Z, RZ)), '( %s = 0 -> %s = 0 )' % (Z, RZ))
    return c([rez_ne0, c([imp], 'necon3d', '( %s =/= 0 -> %s =/= 0 )' % (RZ, Z))], 'mpd', '%s =/= 0' % Z)


def e12(w, A):
    """( A -> ( E1 ` 2 ) =/= 0 ) (ectr at T = 0)"""
    c = Ctx(w, A)
    nx = nx1(w, A)
    b = c([c([nx, c([], '0red', '0 e. RR')], 'jca', '( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ 0 e. RR )' % U1), w.inst('ectr')], 'syl', '( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % E1)
    return f2ne0(w, A, E1, None, '( 1 / 2 )', bstep=b)


def gen_lan(label='zrlan'):
    from ef4_g import elrab_pack
    if label == 'zrlanx':
        w = W('zrlanx', 'The Landau input of ~ zrlan with the zeta-zero mass ` x ` of the square written out.')
    else:
      w = W('zrlan', 'Lean ` re_LSeries_vonMangoldt_le_sub_zeros ` , ` _le ` , ` _le_of_zero ` : ` Re ( - zeta \' / zeta ) ( S ) <_ K log ( abs T + 2 ) + 10 + W / ( W ^ 2 + T ^ 2 ) - x ` at ` S = ( 1 + W ) + i T ` , '
             'where ` x >_ 0 ` is the zeta-zero mass of the square and ` x >_ 1 / ( 1 + W - b ) ` for every zero ` b + i T ` , ` 3 / 8 <_ b <_ 1 ` ( ~ lndeta , ~ ef5lds , ~ ef5ez , ~ zrgq ).')
    A0 = ante_of(S[label])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); wp = c.g('W e. RR+'); w20 = c.g('W <_ ( 1 / ; 2 0 )')
    wr = c([wp], 'rpred', 'W e. RR'); wc = c([wr], 'recnd', 'W e. CC'); tc = c([tr], 'recnd', 'T e. CC')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    ow = c([c([], '1red', '1 e. RR'), wr], 'readdcld', '( 1 + W ) e. RR')
    swc = c([c([ow], 'recnd', '( 1 + W ) e. CC'), c([ic, tc], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SW)
    sre = c([ow, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + W )' % SW)
    RSW = '( Re ` %s )' % SW
    rswr = c([swc], 'recld', '%s e. RR' % RSW)
    s1 = lin8(w, A0, [sre, c([wp], 'rpgt0d', '0 < W')], '1 < %s' % RSW, {RSW: rswr, 'W': wr})
    en = eta_nz(w, A0, swc, s1, SW)
    cl = Closure(w, A0, {'W': ('CC', wc), 'T': ('CC', tc), '_i': ('CC', ic)})
    for a in ('W', 'T', '_i'):
        cl.atom(a)
    d0 = ringeq(w, A0, '( %s - %s )' % (SW, C2T('T')), '( W - 1 )', cl)
    wm = c([wr, c([], '1red', '1 e. RR')], 'resubcld', '( W - 1 ) e. RR')
    ab = c([c([lin8(w, A0, [w20, c([wp], 'rpgt0d', '0 < W')], '-u ( 3 / 2 ) <_ ( W - 1 )', {'W': wr}), lin8(w, A0, [w20], '( W - 1 ) <_ ( 3 / 2 )', {'W': wr})], 'jca',
              '( -u ( 3 / 2 ) <_ ( W - 1 ) /\\ ( W - 1 ) <_ ( 3 / 2 ) )'), c([wm, numst8(w, A0, '( 3 / 2 )', 'RR')], 'absled', '( ( abs ` ( W - 1 ) ) <_ ( 3 / 2 ) <-> ( -u ( 3 / 2 ) <_ ( W - 1 ) /\\ ( W - 1 ) <_ ( 3 / 2 ) ) )')],
           'mpbird', '( abs ` ( W - 1 ) ) <_ ( 3 / 2 )')
    ab2 = c([c([d0], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( W - 1 ) )' % (SW, C2T('T'))), ab], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( 3 / 2 )' % (SW, C2T('T')))
    LAN = ante_of(tsub(stmt('lndeta'), {'S': SW}))
    ln = c([c([tr, c([swc, ab2, en], '3jca', top_and(LAN[0])[1])], 'jca', LAN[0]), w.inst('lndeta')], 'syl', LAN[1])
    LE, LG = LDF(ETA, SW), LDF(GF, SW)
    ZS = ZSE('T')
    MQ, OG, OE, IFQ = '( %s holord q )' % ETA, '( %s holord q )' % GF, '( %s holord q )' % E1, 'if ( q = 1 , 1 , 0 )'
    Zq = '( %s - q )' % SW
    SE = 'sum_ q e. %s ( %s / %s )' % (ZS, MQ, Zq)
    fz = c([tr, w.inst('etazc')], 'syl', tsub(ante_of(stmt('etazc'))[1], {}))
    fin_ = c([fz], 'simp1d', '%s e. Fin' % ZS)
    alq = c([fz], 'simp2d', 'A. q e. %s %s e. NN' % (ZS, MQ))
    Aq = '( %s /\\ q e. %s )' % (A0, ZS)
    cq = Ctx(w, Aq)
    qz = cq([], 'simpr', 'q e. %s' % ZS)
    mqn = w.s([alq], 'r19.21bi', '( %s -> %s e. NN )' % (Aq, MQ))
    mqc = cq([mqn], 'nncnd', '%s e. CC' % MQ)
    zs = cq([cq([lift(w, tr, Aq), qz], 'jca', '( T e. RR /\\ q e. %s )' % ZS), w.inst('zrzs')], 'syl', tsub(ante_of(S['zrzs'])[1], {'Q': 'q'}))
    qh = cq([cq([zs], 'simp1d', '( q e. %s /\\ ( %s ` q ) = 0 )' % (HP0, ETA))], 'simpld', 'q e. %s' % HP0)
    gn = cq([cq([cq([lift(w, tr, Aq), lift(w, wp, Aq)], 'jca', '( T e. RR /\\ W e. RR+ )'), qz], 'jca', '( ( T e. RR /\\ W e. RR+ ) /\\ q e. %s )' % ZS), w.inst('zrgnn')], 'syl',
            tsub(ante_of(S['zrgnn'])[1], {'Q': 'q'}))
    rzq = cq([gn], 'simp2d', '0 < ( Re ` %s )' % Zq)
    qc = cq([cq([qh, cq([cq([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbid', '( q e. CC /\\ 0 < ( Re ` q ) )')], 'simpld', 'q e. CC')
    zqc = cq([lift(w, swc, Aq), qc], 'subcld', '%s e. CC' % Zq)
    zqn = ne0_by_re(w, Aq, zqc, cq([rzq], 'gt0ne0d', '( Re ` %s ) =/= 0' % Zq), Zq)
    def ordst(F, f2):
        hq = cq([cq([cq([lift(w, hol_gf(w, A0) if F == GF else hol_e1(w, A0), Aq), lift(w, f2, Aq)], 'jca', '( %s /\\ ( %s ` 2 ) =/= 0 )' % (HOLF(F, HP0), F)), qh], 'jca',
                    '( ( %s /\\ ( %s ` 2 ) =/= 0 ) /\\ q e. %s )' % (HOLF(F, HP0), F, HP0)), w.inst('zrord')], 'syl', tsub(ante_of(S['zrord'])[1], {'F': F, 'P': 'q'}))
        return hq
    g2 = f2ne0(w, A0, GF, 'gfctr', '( 1 / 2 )')
    e2 = e12(w, A0)
    ogc = cq([cq([ordst(GF, g2)], 'simpld', '%s e. NN0' % OG)], 'nn0cnd', '%s e. CC' % OG)
    oer = cq([ordst(E1, e2)], 'simpld', '%s e. NN0' % OE)
    oec = cq([oer], 'nn0cnd', '%s e. CC' % OE)
    ifc = cq([cq([], '1cnd', '1 e. CC'), cq([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFQ)
    ez = cq([qh, w.inst('ef5ez')], 'syl', '( %s + %s ) = ( %s + %s )' % (MQ, IFQ, OG, OE))
    m1 = cq([cq([mqc, ifc], 'pncand', '( ( %s + %s ) - %s ) = %s' % (MQ, IFQ, IFQ, MQ))], 'eqcomd', '%s = ( ( %s + %s ) - %s )' % (MQ, MQ, IFQ, IFQ))
    m2 = cq([m1, cq([ez], 'oveq1d', '( ( %s + %s ) - %s ) = ( ( %s + %s ) - %s )' % (MQ, IFQ, IFQ, OG, OE, IFQ))], 'eqtrd', '%s = ( ( %s + %s ) - %s )' % (MQ, OG, OE, IFQ))
    GO = GORD('q')
    m3 = cq([m2, cq([ogc, oec, ifc], 'addsubd', '( ( %s + %s ) - %s ) = ( %s + %s )' % (OG, OE, IFQ, GO, OE))], 'eqtrd', '%s = ( %s + %s )' % (MQ, GO, OE))
    goc = cq([ogc, ifc], 'subcld', '%s e. CC' % GO)
    t1 = cq([cq([m3], 'oveq1d', '( %s / %s ) = ( ( %s + %s ) / %s )' % (MQ, Zq, GO, OE, Zq)), cq([goc, oec, zqc, zqn], 'divdird', '( ( %s + %s ) / %s ) = ( ( %s / %s ) + ( %s / %s ) )' % (GO, OE, Zq, GO, Zq, OE, Zq))],
            'eqtrd', '( %s / %s ) = ( ( %s / %s ) + ( %s / %s ) )' % (MQ, Zq, GO, Zq, OE, Zq))
    q1c = cq([goc, zqc, zqn], 'divcld', '( %s / %s ) e. CC' % (GO, Zq)); q2c = cq([oec, zqc, zqn], 'divcld', '( %s / %s ) e. CC' % (OE, Zq))
    RG, RE_ = '( Re ` ( %s / %s ) )' % (GO, Zq), '( Re ` ( %s / %s ) )' % (OE, Zq)
    t2 = cq([cq([t1], 'fveq2d', '( Re ` ( %s / %s ) ) = ( Re ` ( ( %s / %s ) + ( %s / %s ) ) )' % (MQ, Zq, GO, Zq, OE, Zq)), cq([q1c, q2c], 'readdd', '( Re ` ( ( %s / %s ) + ( %s / %s ) ) ) = ( %s + %s )' % (GO, Zq, OE, Zq, RG, RE_))],
            'eqtrd', '( Re ` ( %s / %s ) ) = ( %s + %s )' % (MQ, Zq, RG, RE_))
    rgr = cq([q1c], 'recld', '%s e. RR' % RG); rer = cq([q2c], 'recld', '%s e. RR' % RE_)
    GT = GTERM(SW)
    XS = 'sum_ q e. %s %s' % (ZS, RE_)
    sp = c([c([t2], 'sumeq2dv', 'sum_ q e. %s ( Re ` ( %s / %s ) ) = sum_ q e. %s ( %s + %s )' % (ZS, MQ, Zq, ZS, RG, RE_)),
            c([fin_, cq([rgr], 'recnd', '%s e. CC' % RG), cq([rer], 'recnd', '%s e. CC' % RE_)], 'fsumadd', 'sum_ q e. %s ( %s + %s ) = ( %s + %s )' % (ZS, RG, RE_, GT, XS))],
           'eqtrd', 'sum_ q e. %s ( Re ` ( %s / %s ) ) = ( %s + %s )' % (ZS, MQ, Zq, GT, XS))
    mzc = cq([mqc, zqc, zqn], 'divcld', '( %s / %s ) e. CC' % (MQ, Zq))
    sre_ = c([fin_, mzc], 'fsumre', '( Re ` %s ) = sum_ q e. %s ( Re ` ( %s / %s ) )' % (SE, ZS, MQ, Zq))
    rse = c([sre_, sp], 'eqtrd', '( Re ` %s ) = ( %s + %s )' % (SE, GT, XS))
    sec = c([fin_, mzc], 'fsumcl', '%s e. CC' % SE)
    from zr_b import mv, VMF
    Ak = '( %s /\\ k e. NN )' % A0
    ck = Ctx(w, Ak)
    kn = ck([], 'simpr', 'k e. NN')
    TKK = '( ( Lam ` k ) x. ( k ^c -u %s ) )' % SW
    tkc = ck([ck([ck([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC'), ck([ck([kn], 'nncnd', 'k e. CC'), ck([lift(w, swc, Ak)], 'negcld', '-u %s e. CC' % SW)], 'cxpcld', '( k ^c -u %s ) e. CC' % SW)],
              'mulcld', '%s e. CC' % TKK)
    fk = mv(w, Ak, 'n', 'NN', '( ( Lam ` n ) x. ( n ^c -u %s ) )' % SW, 'k', kn, tkc)
    cv = c([c([swc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SW, SW)), w.inst('zrvmc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % VMF(SW))
    DS = DL(SW)
    dsc = c([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), c([], '1zzd', '1 e. ZZ'), fk, tkc, cv], 'isumcl', '%s e. CC' % DS)
    gv = c([c([swc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SW, SW)), w.inst('zrgv')], 'syl', tsub(ante_of(S['zrgv'])[1], {'S': SW}))
    EXM = '( ( exp ` ( ( %s - 1 ) x. ( log ` 2 ) ) ) - 1 )' % SW
    lgq = c([gv], 'simprd', '%s = ( ( log ` 2 ) / %s )' % (LG, EXM))
    two = numst8(w, A0, '2', 'RR+')
    lgc = c([lgq, c([c([c([two], 'relogcld', '( log ` 2 ) e. RR')], 'recnd', '( log ` 2 ) e. CC'),
                    c([c([c([c([swc, c([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % SW), c([c([two], 'relogcld', '( log ` 2 ) e. RR')], 'recnd', '( log ` 2 ) e. CC')], 'mulcld',
                             '( ( %s - 1 ) x. ( log ` 2 ) ) e. CC' % SW)], 'efcld', '( exp ` ( ( %s - 1 ) x. ( log ` 2 ) ) ) e. CC' % SW), c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % EXM),
                    c([gv], 'simpld', '%s =/= 0' % EXM)], 'divcld', '( ( log ` 2 ) / %s ) e. CC' % EXM)], 'eqeltrd', '%s e. CC' % LG)
    ld = c([c([swc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SW, SW)), w.inst('ef5lds')], 'syl', '%s = ( %s - %s )' % (LE, LG, DS))
    lec = c([ld, c([lgc, dsc], 'subcld', '( %s - %s ) e. CC' % (LG, DS))], 'eqeltrd', '%s e. CC' % LE)
    RLE, RLG, RDS, RSE = ['( Re ` %s )' % x for x in (LE, LG, DS, SE)]
    rle = c([c([ld], 'fveq2d', '%s = ( Re ` ( %s - %s ) )' % (RLE, LG, DS)), c([lgc, dsc], 'resubd', '( Re ` ( %s - %s ) ) = ( %s - %s )' % (LG, DS, RLG, RDS))], 'eqtrd', '%s = ( %s - %s )' % (RLE, RLG, RDS))
    D1 = '( %s - %s )' % (SE, LE)
    d1c = c([sec, lec], 'subcld', '%s e. CC' % D1)
    ra = c([d1c], 'releabsd', '( Re ` %s ) <_ ( abs ` %s )' % (D1, D1))
    rs = c([sec, lec], 'resubd', '( Re ` %s ) = ( %s - %s )' % (D1, RSE, RLE))
    asb = c([sec, lec], 'abssubd', '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (D1, LE, SE))
    zq = c([c([tr, c([wp, w20], 'jca', W20)], 'jca', '( T e. RR /\\ %s )' % W20), w.inst('zrgq')], 'syl', ante_of(S['zrgq'])[1])
    DEN = '( ( W ^ 2 ) + ( T ^ 2 ) )'
    denr = c([c([wr], 'resqcld', '( W ^ 2 ) e. RR'), c([tr], 'resqcld', '( T ^ 2 ) e. RR')], 'readdcld', '%s e. RR' % DEN)
    denp = lin8(w, A0, [c([wr, c([wp], 'rpne0d', 'W =/= 0')], 'sqgt0d', '0 < ( W ^ 2 )'), c([tr], 'sqge0d', '0 <_ ( T ^ 2 )')], '0 < %s' % DEN,
                {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( T ^ 2 )': c([tr], 'resqcld', '( T ^ 2 ) e. RR')})
    wtr = c([wr, denr, c([denp], 'gt0ne0d', '%s =/= 0' % DEN)], 'redivcld', '%s e. RR' % WTT)
    gtr = c([fin_, rgr], 'fsumrecl', '%s e. RR' % GT)
    xsr = c([fin_, rer], 'fsumrecl', '%s e. RR' % XS)
    LT = LT2('T')
    ltr = c([c([c([c([tc], 'abscld', '( abs ` T ) e. RR'), numst8(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` T ) + 2 ) e. RR'),
               lin8(w, A0, [c([tc], 'absge0d', '0 <_ ( abs ` T )')], '0 < ( ( abs ` T ) + 2 )', {'( abs ` T )': c([tc], 'abscld', '( abs ` T ) e. RR')})], 'elrpd', '( ( abs ` T ) + 2 ) e. RR+')],
            'relogcld', '%s e. RR' % LT)
    lvF = {RLE: c([lec], 'recld', '%s e. RR' % RLE), RLG: c([lgc], 'recld', '%s e. RR' % RLG), RDS: c([dsc], 'recld', '%s e. RR' % RDS), RSE: c([sec], 'recld', '%s e. RR' % RSE),
           GT: gtr, XS: xsr, WTT: wtr, LT: ltr, '( Re ` %s )' % D1: c([d1c], 'recld', '( Re ` %s ) e. RR' % D1), '( abs ` %s )' % D1: c([d1c], 'abscld', '( abs ` %s ) e. RR' % D1),
           '( abs ` ( %s - %s ) )' % (LE, SE): c([c([lec, sec], 'subcld', '( %s - %s ) e. CC' % (LE, SE))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (LE, SE))}
    GOAL1 = '%s <_ ( ( ( %s x. %s ) + ( ; 1 0 + %s ) ) - %s )' % (RDS, KL, LT, WTT, XS)
    RDSW = '( Re ` %s )' % DL(SW)
    main = lin8(w, A0, [rle, ra, rs, asb, ln, rse, zq], GOAL1, lvF)
    x0 = c([fin_, rer, cq([cq([cq([cq([oer], 'nn0red', '%s e. RR' % OE), cq([oer], 'nn0ge0d', '0 <_ %s' % OE)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (OE, OE)), cq([zqc, rzq], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (Zq, Zq))],
                               'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (OE, OE, Zq, Zq)), w.inst('redivnn')], 'syl', '0 <_ %s' % RE_)], 'fsumge0', '0 <_ %s' % XS)
    if label == 'zrlanx':
        assert XS == XSE, (XS, XSE)
        w.qed([c([main, x0], 'jca', ante_of(S['zrlanx'])[1])], 'idi', S['zrlanx'])
        return run8(w)
    re0 = cq([cq([cq([cq([oer], 'nn0red', '%s e. RR' % OE), cq([oer], 'nn0ge0d', '0 <_ %s' % OE)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (OE, OE)), cq([zqc, rzq], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (Zq, Zq))],
                  'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (OE, OE, Zq, Zq)), w.inst('redivnn')], 'syl', '0 <_ %s' % RE_)
    # every zero b + i T gives 1 / ( 1 + W - b ) <_ XS
    HB = '( ( ( 3 / 8 ) <_ b /\\ b <_ 1 ) /\\ ( %s ` ( b + ( _i x. T ) ) ) = 0 )' % E1
    Ab = '( %s /\\ b e. RR )' % A0
    Abh = '( %s /\\ %s )' % (Ab, HB)
    ch = Ctx(w, Abh)
    br = ch.g('b e. RR'); b38 = ch.g('( 3 / 8 ) <_ b'); b1 = ch.g('b <_ 1'); ez_ = ch.g('( %s ` ( b + ( _i x. T ) ) ) = 0' % E1)
    L_ = lambda st: lift(w, st, Abh)
    RHO = '( b + ( _i x. T ) )'
    insq = sq_mem(w, Abh, L_(tr), 'b', br, 'T', L_(tr), [b38, b1], {})
    rhc = ch([ch([br], 'recnd', 'b e. CC'), ch([L_(ic), L_(tc)], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % RHO)
    rre = ch([br, L_(tr), w.inst('crre')], 'syl2anc', '( Re ` %s ) = b' % RHO)
    rhh = ch([ch([rhc, ch([lin8(w, Abh, [b38], '0 < b', {'b': br}), ch([rre], 'eqcomd', 'b = ( Re ` %s )' % RHO)], 'breqtrd', '0 < ( Re ` %s )' % RHO)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (RHO, RHO)),
              ch([ch([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (RHO, HP0, RHO, RHO))], 'mpbird', '%s e. %s' % (RHO, HP0))
    e1n = ch([ez_, ch.a1(w.s([], '0ne1', '0 =/= 1'), '0 =/= 1')], 'eqnetrd', '( %s ` %s ) =/= 1' % (E1, RHO))
    imp = ch.a1(w.s([w.s([], 'fveq2', '( %s = 1 -> ( %s ` %s ) = ( %s ` 1 ) )' % (RHO, E1, RHO, E1)), w.s([], 'ef5e11', '( %s ` 1 ) = 1' % E1)], 'eqtrdi', '( %s = 1 -> ( %s ` %s ) = 1 )' % (RHO, E1, RHO)),
                '( %s = 1 -> ( %s ` %s ) = 1 )' % (RHO, E1, RHO))
    rn1 = ch([e1n, ch([imp], 'necon3d', '( ( %s ` %s ) =/= 1 -> %s =/= 1 )' % (E1, RHO, RHO))], 'mpd', '%s =/= 1' % RHO)
    zt = ch([ch([rhh, rn1], 'jca', '( %s e. %s /\\ %s =/= 1 )' % (RHO, HP0, RHO)), w.inst('zc1ezt')], 'syl', tsub(ante_of(stmt('zc1ezt'))[1], {'P': RHO}))
    etz = ch([ez_, ch([zt], 'simprd', '( ( %s ` %s ) = 0 -> ( %s ` %s ) = 0 )' % (E1, RHO, ETA, RHO))], 'mpd', '( %s ` %s ) = 0' % (ETA, RHO))
    from ef4_g import elrab_pack
    rin = elrab_pack(w, Abh, 'r', SQ13('T'), '( %s ` r ) = 0' % ETA, RHO, insq, etz)
    od = ch([ch([ch([L_(hol_e1(w, A0)), L_(e2)], 'jca', '( %s /\\ ( %s ` 2 ) =/= 0 )' % (HOLF(E1, HP0), E1)), rhh], 'jca', '( ( %s /\\ ( %s ` 2 ) =/= 0 ) /\\ %s e. %s )' % (HOLF(E1, HP0), E1, RHO, HP0)),
             w.inst('zrord')], 'syl', tsub(ante_of(S['zrord'])[1], {'F': E1, 'P': RHO}))
    OER = '( %s holord %s )' % (E1, RHO)
    onn = ch([ez_, ch([od], 'simprd', '( ( %s ` %s ) = 0 -> %s e. NN )' % (E1, RHO, OER))], 'mpd', '%s e. NN' % OER)
    R = '( ( 1 + W ) - b )'
    clb = Closure(w, Abh, {'W': ('CC', L_(wc)), 'T': ('CC', L_(tc)), '_i': ('CC', L_(ic)), 'b': ('CC', ch([br], 'recnd', 'b e. CC'))})
    for a_ in ('W', 'T', '_i', 'b'):
        clb.atom(a_)
    zr = ringeq(w, Abh, '( %s - %s )' % (SW, RHO), R, clb)
    rr = ch([ch([ch([], '1red', '1 e. RR'), L_(wr)], 'readdcld', '( 1 + W ) e. RR'), br], 'resubcld', '%s e. RR' % R)
    rp = ch([rr, lin8(w, Abh, [b1, L_(c([wp], 'rpgt0d', '0 < W'))], '0 < %s' % R, {'b': br, 'W': L_(wr)})], 'elrpd', '%s e. RR+' % R)
    oerr = ch([onn], 'nnred', '%s e. RR' % OER)
    TR = '( Re ` ( %s / ( %s - %s ) ) )' % (OER, SW, RHO)
    tv = ch([ch([ch([zr], 'oveq2d', '( %s / ( %s - %s ) ) = ( %s / %s )' % (OER, SW, RHO, OER, R))], 'fveq2d', '%s = ( Re ` ( %s / %s ) )' % (TR, OER, R)),
             ch([ch([oerr, rr, ch([rp], 'rpne0d', '%s =/= 0' % R)], 'redivcld', '( %s / %s ) e. RR' % (OER, R))], 'rered', '( Re ` ( %s / %s ) ) = ( %s / %s )' % (OER, R, OER, R))],
            'eqtrd', '%s = ( %s / %s )' % (TR, OER, R))
    ld1 = ch([ch([onn], 'nnge1d', '1 <_ %s' % OER), ch([ch([], '1red', '1 e. RR'), oerr, rp], 'lediv1d', '( 1 <_ %s <-> ( 1 / %s ) <_ ( %s / %s ) )' % (OER, R, OER, R))], 'mpbid', '( 1 / %s ) <_ ( %s / %s )' % (R, OER, R))
    Abq = '( %s /\\ q e. %s )' % (Abh, ZS)
    cbq = Ctx(w, Abq)
    bridge = cbq([cbq.g(A0), cbq.g('q e. %s' % ZS)], 'jca', Aq)
    rl = lambda st: w.s([bridge, st], 'syl', '( %s -> %s )' % (Abq, strip_ante(formula_of(w, st), Aq)))
    eqq, newq = w.congr(RE_, {'q': RHO}, 'q = %s' % RHO, {'q': w.s([], 'id', '( q = %s -> q = %s )' % (RHO, RHO))})
    assert newq == TR, (newq, TR)
    ge1 = ch([L_(fin_), rl(rer), rl(re0), eqq, rin], 'fsumge1', '%s <_ %s' % (TR, XS))
    trr = ch([tv, ch([oerr, rr, ch([rp], 'rpne0d', '%s =/= 0' % R)], 'redivcld', '( %s / %s ) e. RR' % (OER, R))], 'eqeltrd', '%s e. RR' % TR)
    IR = '( 1 / %s )' % R
    bb = lin8(w, Abh, [tv, ld1, ge1], '%s <_ %s' % (IR, XS), {TR: trr, XS: L_(xsr), IR: ch([ch([], '1red', '1 e. RR'), rr, ch([rp], 'rpne0d', '%s =/= 0' % R)], 'redivcld', '%s e. RR' % IR),
                                                                '( %s / %s )' % (OER, R): ch([oerr, rr, ch([rp], 'rpne0d', '%s =/= 0' % R)], 'redivcld', '( %s / %s ) e. RR' % (OER, R))})
    exb = w.s([bb], 'ex', '( %s -> ( %s -> %s <_ %s ) )' % (Ab, HB, IR, XS))
    alb = c([exb], 'ralrimiva', 'A. b e. RR ( %s -> %s <_ %s )' % (HB, IR, XS))
    BODY = ante_of(S['zrlan'])[1]
    body = BODY[len('E. x e. RR '):]
    eqx, newx = w.wcongr(body, {'x': XS}, 'x = %s' % XS, {'x': w.s([], 'id', '( x = %s -> x = %s )' % (XS, XS))})
    Ax = '( %s /\\ x = %s )' % (A0, XS)
    at = c([c([x0, main], 'jca', top_and(newx)[0]), alb], 'jca', newx)
    fin = c([xsr, w.s([eqx], 'adantl', '( %s -> ( %s <-> %s ) )' % (Ax, body, newx)), at], 'rspcedvd', BODY)
    w.qed([fin], 'idi', S['zrlan'])
    return run8(w)


GENS = {'zrlan': gen_lan, 'zrlanx': lambda: gen_lan('zrlanx')}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
