"""Sortie ZR: zrgb, zrga (the two cases of the g'/g bound), zrgnn, zrgk, zrgq (Lean re_gFun_logDeriv_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of

SKK = SK('K')
V_ = '( ( %s - %s ) x. %s )' % (SW, SKK, L2)
E_ = EXL('( %s - 1 )' % SW)
EM = '( %s - 1 )' % E_


class Setup:
    """common facts under A0 containing T e. RR, W e. RR+, W <_ 1/20 (and K e. ZZ when k=True)"""
    def __init__(self, w, A0, k=True):
        self.w, self.A0 = w, A0
        c = self.c = Ctx(w, A0)
        self.tr = c.g('T e. RR'); self.wp = c.g('W e. RR+'); self.w20 = c.g('W <_ ( 1 / ; 2 0 )')
        self.wr = c([self.wp], 'rpred', 'W e. RR')
        self.tc = c([self.tr], 'recnd', 'T e. CC'); self.wc = c([self.wr], 'recnd', 'W e. CC')
        self.ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
        ow = c([c([], '1red', '1 e. RR'), self.wr], 'readdcld', '( 1 + W ) e. RR')
        self.ow = ow
        self.sc = c([c([ow], 'recnd', '( 1 + W ) e. CC'), c([self.ic, self.tc], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SW)
        self.sre = c([ow, self.tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + W )' % SW)
        rsr = c([self.sc], 'recld', '( Re ` %s ) e. RR' % SW)
        self.s1 = lin8(w, A0, [self.sre, c([self.wp], 'rpgt0d', '0 < W')], '1 < ( Re ` %s )' % SW, {'( Re ` %s )' % SW: rsr, 'W': self.wr})
        gv = c([c([self.sc, self.s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SW, SW)), w.inst('zrgv')], 'syl', tsub(ante_of(S['zrgv'])[1], {'S': SW}))
        self.emn = c([gv], 'simpld', '%s =/= 0' % EM)
        self.ldf = c([gv], 'simprd', '%s = ( %s / %s )' % (LDF(GF, SW), L2, EM))
        l2 = c.a1(w.s([], 'zrl2', S['zrl2']), S['zrl2'])
        self.llo = c([l2], 'simpld', '( 1 / 3 ) < %s' % L2); self.lhi = c([l2], 'simprd', '%s < 1' % L2)
        two = numst8(w, A0, '2', 'RR+')
        self.lr = c([two], 'relogcld', '%s e. RR' % L2); self.lc = c([self.lr], 'recnd', '%s e. CC' % L2)
        self.ec = c([c([c([self.sc, c([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % SW), self.lc], 'mulcld', '( ( %s - 1 ) x. %s ) e. CC' % (SW, L2))], 'efcld', '%s e. CC' % E_)
        self.emc = c([self.ec, c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % EM)
        if k:
            self.kz = c.g('K e. ZZ')
            gk = c([c([c([self.tr, self.wr], 'jca', '( T e. RR /\\ W e. RR )'), self.kz], 'jca', '( ( T e. RR /\\ W e. RR ) /\\ K e. ZZ )'), w.inst('zrgvk')], 'syl',
                   tsub(ante_of(S['zrgvk'])[1], {}))
            self.vv = c([gk], 'simpld', '%s = ( ( W x. %s ) + ( _i x. %s ) )' % (V_, L2, PHI('K')))
            self.ev = c([gk], 'simprd', '%s = ( exp ` %s )' % (E_, V_))
            kc = c([self.kz], 'zcnd', 'K e. CC')
            pir = c.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
            self.phr = c([c([self.tr, self.lr], 'remulcld', '( T x. %s ) e. RR' % L2),
                          c([numst8(w, A0, '2', 'RR'), c([pir, c([self.kz], 'zred', 'K e. RR')], 'remulcld', '( _pi x. K ) e. RR')], 'remulcld', '( 2 x. ( _pi x. K ) ) e. RR')],
                         'resubcld', '%s e. RR' % PHI('K'))
            self.wl = c([self.wr, self.lr], 'remulcld', '( W x. %s ) e. RR' % L2)
            self.vre = c([c([self.vv], 'fveq2d', '( Re ` %s ) = ( Re ` ( ( W x. %s ) + ( _i x. %s ) ) )' % (V_, L2, PHI('K'))), c([self.wl, self.phr, w.inst('crre')], 'syl2anc', '( Re ` ( ( W x. %s ) + ( _i x. %s ) ) ) = ( W x. %s )' % (L2, PHI('K'), L2))],
                         'eqtrd', '( Re ` %s ) = ( W x. %s )' % (V_, L2))
            self.vim = c([c([self.vv], 'fveq2d', '( Im ` %s ) = ( Im ` ( ( W x. %s ) + ( _i x. %s ) ) )' % (V_, L2, PHI('K'))), c([self.wl, self.phr, w.inst('crim')], 'syl2anc', '( Im ` ( ( W x. %s ) + ( _i x. %s ) ) ) = %s' % (L2, PHI('K'), PHI('K')))],
                         'eqtrd', '( Im ` %s ) = %s' % (V_, PHI('K')))
            self.vc = c([self.vv, c([c([self.wl], 'recnd', '( W x. %s ) e. CC' % L2), c([self.ic, c([self.phr], 'recnd', '%s e. CC' % PHI('K'))], 'mulcld', '( _i x. %s ) e. CC' % PHI('K'))], 'addcld', '( ( W x. %s ) + ( _i x. %s ) ) e. CC' % (L2, PHI('K')))], 'eqeltrd', '%s e. CC' % V_)


def gen_gB():
    w = W('zrgb', 'Lean ` re_gFun_logDeriv_le ` , case B: when the nearest pole ` s_K ` of ` g \' / g ` is at distance ` >_ 1 / ( 2 log 2 ) ` , ` Re g \' / g ( ( 1 + W ) + i T ) <_ 0 ` ( ~ zrcos , ~ eflegeo , ~ zrrec ).')
    A0 = ante_of(S['zrgb'])[0]
    U = Setup(w, A0)
    c = U.c
    h1 = c.g('( 1 / 2 ) <_ ( abs ` %s )' % PHI('K')); h2 = c.g('( abs ` %s ) <_ _pi' % PHI('K'))
    cs = c([c([U.phr, c([h1, h2], 'jca', '( ( 1 / 2 ) <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ _pi )' % (PHI('K'), PHI('K')))], 'jca',
              '( %s e. RR /\\ ( ( 1 / 2 ) <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ _pi ) )' % (PHI('K'), PHI('K'), PHI('K'))), w.inst('zrcos')], 'syl', '( cos ` %s ) < ( ; 1 1 / ; 1 2 )' % PHI('K'))
    # Re E = exp ( W L ) cos phi
    RV, IV = '( Re ` %s )' % V_, '( Im ` %s )' % V_
    eu = c([U.vc, w.inst('efeul')], 'syl', '( exp ` %s ) = ( ( exp ` %s ) x. ( ( cos ` %s ) + ( _i x. ( sin ` %s ) ) ) )' % (V_, RV, IV, IV))
    rvr = c([U.vc], 'recld', '%s e. RR' % RV); ivr = c([U.vc], 'imcld', '%s e. RR' % IV)
    exr = c([rvr], 'reefcld', '( exp ` %s ) e. RR' % RV)
    CS = '( ( cos ` %s ) + ( _i x. ( sin ` %s ) ) )' % (IV, IV)
    csc = c([c([c([ivr], 'recoscld', '( cos ` %s ) e. RR' % IV)], 'recnd', '( cos ` %s ) e. CC' % IV), c([U.ic, c([c([ivr], 'resincld', '( sin ` %s ) e. RR' % IV)], 'recnd', '( sin ` %s ) e. CC' % IV)], 'mulcld', '( _i x. ( sin ` %s ) ) e. CC' % IV)],
            'addcld', '%s e. CC' % CS)
    r1 = c([exr, csc], 'remul2d', '( Re ` ( ( exp ` %s ) x. %s ) ) = ( ( exp ` %s ) x. ( Re ` %s ) )' % (RV, CS, RV, CS))
    r2 = c([c([ivr], 'recoscld', '( cos ` %s ) e. RR' % IV), c([ivr], 'resincld', '( sin ` %s ) e. RR' % IV), w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( cos ` %s )' % (CS, IV))
    RE = '( Re ` %s )' % E_
    ex2 = c([c([U.ev], 'fveq2d', '%s = ( Re ` ( exp ` %s ) )' % (RE, V_)), c([eu], 'fveq2d', '( Re ` ( exp ` %s ) ) = ( Re ` ( ( exp ` %s ) x. %s ) )' % (V_, RV, CS))], 'eqtrd', '%s = ( Re ` ( ( exp ` %s ) x. %s ) )' % (RE, RV, CS))
    ex3 = c([ex2, c([r1, c([r2], 'oveq2d', '( ( exp ` %s ) x. ( Re ` %s ) ) = ( ( exp ` %s ) x. ( cos ` %s ) )' % (RV, CS, RV, IV))], 'eqtrd',
                    '( Re ` ( ( exp ` %s ) x. %s ) ) = ( ( exp ` %s ) x. ( cos ` %s ) )' % (RV, CS, RV, IV))], 'eqtrd', '%s = ( ( exp ` %s ) x. ( cos ` %s ) )' % (RE, RV, IV))
    WL = '( W x. %s )' % L2
    ex4 = c([ex3, c([c([U.vre], 'fveq2d', '( exp ` %s ) = ( exp ` %s )' % (RV, WL)), c([U.vim], 'fveq2d', '( cos ` %s ) = ( cos ` %s )' % (IV, PHI('K')))], 'oveq12d',
                    '( ( exp ` %s ) x. ( cos ` %s ) ) = ( ( exp ` %s ) x. ( cos ` %s ) )' % (RV, IV, WL, PHI('K')))], 'eqtrd', '%s = ( ( exp ` %s ) x. ( cos ` %s ) )' % (RE, WL, PHI('K')))
    # exp ( W L ) <_ 20 / 19
    EX = '( exp ` %s )' % WL
    lv0 = {'W': U.wr, L2: U.lr}
    wl0 = c([U.wr, U.lr, c([U.wp], 'rpge0d', '0 <_ W'), lin8(w, A0, [U.llo], '0 <_ %s' % L2, lv0)], 'mulge0d', '0 <_ %s' % WL)
    hint1 = c([U.wr, c([c([], '1red', '1 e. RR'), U.lr], 'resubcld', '( 1 - %s ) e. RR' % L2), c([U.wp], 'rpge0d', '0 <_ W'), lin8(w, A0, [U.lhi], '0 <_ ( 1 - %s )' % L2, lv0)],
              'mulge0d', '0 <_ ( W x. ( 1 - %s ) )' % L2)
    wl1 = lin8(w, A0, [hint1, U.w20], '%s <_ ( 1 / ; 2 0 )' % WL, lv0, products=True)
    lvw = {WL: U.wl}
    eg = c([U.wl, wl0, lin8(w, A0, [wl1], '%s < 1' % WL, lvw)], 'eflegeo', '%s <_ ( 1 / ( 1 - %s ) )' % (EX, WL))
    Y = '( 1 / ( 1 - %s ) )' % WL
    om = c([c([], '1red', '1 e. RR'), U.wl], 'resubcld', '( 1 - %s ) e. RR' % WL)
    omp = lin8(w, A0, [wl1], '0 < ( 1 - %s )' % WL, lvw)
    yr = c([c([], '1red', '1 e. RR'), om, c([omp], 'gt0ne0d', '( 1 - %s ) =/= 0' % WL)], 'redivcld', '%s e. RR' % Y)
    yv = c([c([], '1cnd', '1 e. CC'), c([om], 'recnd', '( 1 - %s ) e. CC' % WL), c([omp], 'gt0ne0d', '( 1 - %s ) =/= 0' % WL)], 'divcan1d', '( %s x. ( 1 - %s ) ) = 1' % (Y, WL))
    y0 = c([c([], '1red', '1 e. RR'), c([om, omp], 'elrpd', '( 1 - %s ) e. RR+' % WL), lin8(w, A0, [], '0 <_ 1', {})], 'divge0d', '0 <_ %s' % Y)
    hy = c([yr, c([numst8(w, A0, '( 1 / ; 2 0 )', 'RR'), U.wl], 'resubcld', '( ( 1 / ; 2 0 ) - %s ) e. RR' % WL), y0, lin8(w, A0, [wl1], '0 <_ ( ( 1 / ; 2 0 ) - %s )' % WL, lvw)],
           'mulge0d', '0 <_ ( %s x. ( ( 1 / ; 2 0 ) - %s ) )' % (Y, WL))
    yle = lin8(w, A0, [yv, hy], '%s <_ ( ; 2 0 / ; 1 9 )' % Y, {Y: yr, WL: U.wl}, products=True)
    exr2 = c([U.wl], 'reefcld', '%s e. RR' % EX)
    ex0 = c([c([U.wl, w.inst('efgt0')], 'syl', '0 < %s' % EX)], 'ltled', '0 <_ %s' % EX)
    COS = '( cos ` %s )' % PHI('K')
    cr = c([U.phr], 'recoscld', '%s e. RR' % COS)
    hc = c([exr2, c([numst8(w, A0, '( ; 1 1 / ; 1 2 )', 'RR'), cr], 'resubcld', '( ( ; 1 1 / ; 1 2 ) - %s ) e. RR' % COS), ex0, lin8(w, A0, [cs], '0 <_ ( ( ; 1 1 / ; 1 2 ) - %s )' % COS, {COS: cr})],
           'mulge0d', '0 <_ ( %s x. ( ( ; 1 1 / ; 1 2 ) - %s ) )' % (EX, COS))
    rer = c([U.ec], 'recld', '%s e. RR' % RE)
    re1 = lin8(w, A0, [ex4, hc, eg, yle], '%s <_ 1' % RE, {RE: rer, EX: exr2, COS: cr, Y: yr}, products=True)
    # Re ( 1 / ( E - 1 ) ) <_ 0
    rq = c([c([U.emc, U.emn], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (EM, EM)), w.inst('zrrec')], 'syl', '( Re ` ( 1 / %s ) ) = ( ( Re ` %s ) / ( ( abs ` %s ) ^ 2 ) )' % (EM, EM, EM))
    rem = c([U.ec, c([], '1cnd', '1 e. CC')], 'resubd', '( Re ` %s ) = ( %s - ( Re ` 1 ) )' % (EM, RE))
    rmr = c([U.emc], 'recld', '( Re ` %s ) e. RR' % EM)
    rm0 = lin8(w, A0, [rem, c.a1(w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1'), re1], '( Re ` %s ) <_ 0' % EM, {'( Re ` %s )' % EM: rmr, RE: rer, '( Re ` 1 )': c([c([], '1cnd', '1 e. CC')], 'recld', '( Re ` 1 ) e. RR')})
    AB = '( ( abs ` %s ) ^ 2 )' % EM
    ar = c([U.emc], 'abscld', '( abs ` %s ) e. RR' % EM)
    ap = c([U.emn, c([U.emc, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (EM, EM))], 'mpbid', '0 < ( abs ` %s )' % EM)
    abrp = c([c([ar, ap], 'elrpd', '( abs ` %s ) e. RR+' % EM), c.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '%s e. RR+' % AB)
    qle = c([c([rm0, c([c([abrp], 'rpcnd', '%s e. CC' % AB)], 'mul02d', '( 0 x. %s ) = 0' % AB)], 'breqtrrd', '( Re ` %s ) <_ ( 0 x. %s )' % (EM, AB)),
             c([rmr, c([], '0red', '0 e. RR'), abrp], 'ledivmul2d', '( ( ( Re ` %s ) / %s ) <_ 0 <-> ( Re ` %s ) <_ ( 0 x. %s ) )' % (EM, AB, EM, AB))], 'mpbird', '( ( Re ` %s ) / %s ) <_ 0' % (EM, AB))
    rq0 = c([rq, qle], 'eqbrtrd', '( Re ` ( 1 / %s ) ) <_ 0' % EM)
    # Re g'/g = L Re ( 1 / ( E - 1 ) )
    RQ = '( Re ` ( 1 / %s ) )' % EM
    iq = c([c([], '1cnd', '1 e. CC'), U.emc, U.emn], 'divcld', '( 1 / %s ) e. CC' % EM)
    g1 = c([c([U.ldf], 'fveq2d', '( Re ` %s ) = ( Re ` ( %s / %s ) )' % (LDF(GF, SW), L2, EM)),
            c([c([c([U.lc, U.emc, U.emn], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (L2, EM, L2, EM))], 'fveq2d', '( Re ` ( %s / %s ) ) = ( Re ` ( %s x. ( 1 / %s ) ) )' % (L2, EM, L2, EM)),
               c([U.lr, iq], 'remul2d', '( Re ` ( %s x. ( 1 / %s ) ) ) = ( %s x. %s )' % (L2, EM, L2, RQ))], 'eqtrd', '( Re ` ( %s / %s ) ) = ( %s x. %s )' % (L2, EM, L2, RQ))],
           'eqtrd', '( Re ` %s ) = ( %s x. %s )' % (LDF(GF, SW), L2, RQ))
    rqr = c([iq], 'recld', '%s e. RR' % RQ)
    hq = c([U.lr, c([rqr], 'renegcld', '-u %s e. RR' % RQ), lin8(w, A0, [U.llo], '0 <_ %s' % L2, {L2: U.lr}), lin8(w, A0, [rq0], '0 <_ -u %s' % RQ, {RQ: rqr})], 'mulge0d', '0 <_ ( %s x. -u %s )' % (L2, RQ))
    RL = '( Re ` %s )' % LDF(GF, SW)
    fin = lin8(w, A0, [g1, hq], '%s <_ 0' % RL, {RL: c([c([U.ldf, c([U.lc, U.emc, U.emn], 'divcld', '( %s / %s ) e. CC' % (L2, EM))], 'eqeltrd', '%s e. CC' % LDF(GF, SW))], 'recld', '%s e. RR' % RL),
                                                 L2: U.lr, RQ: rqr}, products=True)
    w.qed([fin], 'idi', S['zrgb'])
    return run8(w)


def gen_gA():
    w = W('zrga', 'Lean ` re_gFun_logDeriv_le ` , case A: near the pole ` s_K ` , ` Re g \' / g ( S ) <_ 10 + Re 1 / ( S - s_K ) ` for ` S = ( 1 + W ) + i T ` ( ~ zrexp , ~ zrgvk ).')
    A0 = ante_of(S['zrga'])[0]
    U = Setup(w, A0)
    c = U.c
    h = c.g('( abs ` %s ) < ( 1 / 2 )' % PHI('K'))
    WL = '( W x. %s )' % L2
    lv0 = {'W': U.wr, L2: U.lr}
    wlp = c([U.wr, U.lr, c([U.wp], 'rpgt0d', '0 < W'), lin8(w, A0, [U.llo], '0 < %s' % L2, lv0)], 'mulgt0d', '0 < %s' % WL)
    hint1 = c([U.wr, c([c([], '1red', '1 e. RR'), U.lr], 'resubcld', '( 1 - %s ) e. RR' % L2), c([U.wp], 'rpge0d', '0 <_ W'), lin8(w, A0, [U.lhi], '0 <_ ( 1 - %s )' % L2, lv0)],
              'mulge0d', '0 <_ ( W x. ( 1 - %s ) )' % L2)
    wl1 = lin8(w, A0, [hint1, U.w20], '%s <_ ( 1 / ; 2 0 )' % WL, lv0, products=True)
    # V =/= 0
    RV = '( Re ` %s )' % V_
    rvp = c([wlp, c([U.vre], 'eqcomd', '%s = %s' % (WL, RV))], 'breqtrd', '0 < %s' % RV)
    A1 = '( %s /\\ %s = 0 )' % (A0, V_)
    z1 = w.s([w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (A1, V_))], 'fveq2d', '( %s -> %s = ( Re ` 0 ) )' % (A1, RV)), w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % A1)],
             'eqtrd', '( %s -> %s = 0 )' % (A1, RV))
    rvr = c([U.vc], 'recld', '%s e. RR' % RV)
    nz = c([c([rvp], 'gt0ne0d', '%s =/= 0' % RV), c([w.s([z1], 'ex', '( %s -> ( %s = 0 -> %s = 0 ) )' % (A0, V_, RV))], 'necon3d', '( %s =/= 0 -> %s =/= 0 )' % (RV, V_))], 'mpd', '%s =/= 0' % V_)
    # abs V <_ 9 / 10
    PH = PHI('K')
    IP = '( _i x. %s )' % PH
    wlc = c([U.wl], 'recnd', '%s e. CC' % WL); ipc = c([U.ic, c([U.phr], 'recnd', '%s e. CC' % PH)], 'mulcld', '%s e. CC' % IP)
    at = c([wlc, ipc], 'abstrid', '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (WL, IP, WL, IP))
    a1 = c([U.wl, c([wlp], 'ltled', '0 <_ %s' % WL)], 'absidd', '( abs ` %s ) = %s' % (WL, WL))
    am = c([U.ic, c([U.phr], 'recnd', '%s e. CC' % PH)], 'absmuld', '( abs ` %s ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (IP, PH))
    apr = c([c([U.phr], 'recnd', '%s e. CC' % PH)], 'abscld', '( abs ` %s ) e. RR' % PH)
    ai = c.a1(w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1')
    AV = '( abs ` %s )' % V_
    avr = c([U.vc], 'abscld', '%s e. RR' % AV)
    av = c([c([U.vv], 'fveq2d', '%s = ( abs ` ( %s + %s ) )' % (AV, WL, IP)), at], 'eqbrtrd', '%s <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (AV, WL, IP))
    lvA = {AV: avr, '( abs ` %s )' % WL: c([wlc], 'abscld', '( abs ` %s ) e. RR' % WL), '( abs ` %s )' % IP: c([ipc], 'abscld', '( abs ` %s ) e. RR' % IP),
           '( abs ` _i )': c([U.ic], 'abscld', '( abs ` _i ) e. RR'), '( abs ` %s )' % PH: apr, WL: U.wl}
    avb = lin8(w, A0, [av, a1, am, ai, h, wl1], '%s <_ ( 9 / ; 1 0 )' % AV, lvA, products=True)
    zx = c([c([c([U.vc, nz], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (V_, V_)), avb], 'jca', ante_of(tsub(S['zrexp'], {'V': V_}))[0]), w.inst('zrexp')], 'syl', ante_of(tsub(S['zrexp'], {'V': V_}))[1])
    EV = '( exp ` %s )' % V_
    Q1, Q2 = '( 1 / ( %s - 1 ) )' % EV, '( 1 / %s )' % V_
    ec = c([U.vc], 'efcld', '%s e. CC' % EV)
    evm = c([U.ev], 'oveq1d', '%s = ( %s - 1 )' % (EM, EV))
    evn = c([c([evm], 'eqcomd', '( %s - 1 ) = %s' % (EV, EM)), U.emn], 'eqnetrd', '( %s - 1 ) =/= 0' % EV)
    evc = c([ec, c([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % EV)
    q1c = c([c([], '1cnd', '1 e. CC'), evc, evn], 'divcld', '%s e. CC' % Q1)
    q2c = c([c([], '1cnd', '1 e. CC'), U.vc, nz], 'divcld', '%s e. CC' % Q2)
    dfc = c([q1c, q2c], 'subcld', '( %s - %s ) e. CC' % (Q1, Q2))
    rd = c([q1c, q2c], 'resubd', '( Re ` ( %s - %s ) ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (Q1, Q2, Q1, Q2))
    ra = c([dfc], 'releabsd', '( Re ` ( %s - %s ) ) <_ ( abs ` ( %s - %s ) )' % (Q1, Q2, Q1, Q2))
    R1, R2 = '( Re ` %s )' % Q1, '( Re ` %s )' % Q2
    r1r = c([q1c], 'recld', '%s e. RR' % R1); r2r = c([q2c], 'recld', '%s e. RR' % R2)
    RD, AD = '( Re ` ( %s - %s ) )' % (Q1, Q2), '( abs ` ( %s - %s ) )' % (Q1, Q2)
    lvB = {R1: r1r, R2: r2r, RD: c([dfc], 'recld', '%s e. RR' % RD), AD: c([dfc], 'abscld', '%s e. RR' % AD)}
    rb = lin8(w, A0, [rd, ra, zx], '%s <_ ( %s + ; 1 0 )' % (R1, R2), lvB)
    # Re LDF = L Re Q1
    ld2 = c([U.ldf, c([evm], 'oveq2d', '( %s / %s ) = ( %s / ( %s - 1 ) )' % (L2, EM, L2, EV))], 'eqtrd', '%s = ( %s / ( %s - 1 ) )' % (LDF(GF, SW), L2, EV))
    g1 = c([c([ld2], 'fveq2d', '( Re ` %s ) = ( Re ` ( %s / ( %s - 1 ) ) )' % (LDF(GF, SW), L2, EV)),
            c([c([c([U.lc, evc, evn], 'divrecd', '( %s / ( %s - 1 ) ) = ( %s x. %s )' % (L2, EV, L2, Q1))], 'fveq2d', '( Re ` ( %s / ( %s - 1 ) ) ) = ( Re ` ( %s x. %s ) )' % (L2, EV, L2, Q1)),
               c([U.lr, q1c], 'remul2d', '( Re ` ( %s x. %s ) ) = ( %s x. %s )' % (L2, Q1, L2, R1))], 'eqtrd', '( Re ` ( %s / ( %s - 1 ) ) ) = ( %s x. %s )' % (L2, EV, L2, R1))],
           'eqtrd', '( Re ` %s ) = ( %s x. %s )' % (LDF(GF, SW), L2, R1))
    # L Re Q2 = Re ( 1 / ( SW - SK ) )
    D_ = '( %s - %s )' % (SW, SKK)
    skc = c([c([], '1cnd', '1 e. CC'), c([U.ic, c([c([c([], '2cnd', '2 e. CC'), c([c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC'), c([U.kz], 'zcnd', 'K e. CC')], 'mulcld', '( _pi x. K ) e. CC')],
                                                  'mulcld', '( 2 x. ( _pi x. K ) ) e. CC'), U.lc, c([lin8(w, A0, [U.llo], '0 < %s' % L2, lv0)], 'gt0ne0d', '%s =/= 0' % L2)], 'divcld',
                                                '( ( 2 x. ( _pi x. K ) ) / %s ) e. CC' % L2)], 'mulcld', '( _i x. ( ( 2 x. ( _pi x. K ) ) / %s ) ) e. CC' % L2)], 'addcld', '%s e. CC' % SKK)
    dc = c([U.sc, skc], 'subcld', '%s e. CC' % D_)
    l0 = c([lin8(w, A0, [U.llo], '0 < %s' % L2, lv0)], 'gt0ne0d', '%s =/= 0' % L2)
    dn = c([dc, U.lc, nz], 'mulne0bad', '%s =/= 0' % D_)
    q3 = c([c([], '1cnd', '1 e. CC'), dc, U.lc, dn, l0], 'divcan5rd', '( ( 1 x. %s ) / ( %s x. %s ) ) = ( 1 / %s )' % (L2, D_, L2, D_))
    q4 = c([c([c([U.lc], 'mullidd', '( 1 x. %s ) = %s' % (L2, L2))], 'oveq1d', '( ( 1 x. %s ) / %s ) = ( %s / %s )' % (L2, V_, L2, V_)), q3], 'eqtr3d', '( %s / %s ) = ( 1 / %s )' % (L2, V_, D_))
    q5 = c([c([c([U.lc, U.vc, nz], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (L2, V_, L2, Q2)), q4], 'eqtr3d', '( %s x. %s ) = ( 1 / %s )' % (L2, Q2, D_))], 'fveq2d',
           '( Re ` ( %s x. %s ) ) = ( Re ` ( 1 / %s ) )' % (L2, Q2, D_))
    q6 = c([c([U.lr, q2c], 'remul2d', '( Re ` ( %s x. %s ) ) = ( %s x. %s )' % (L2, Q2, L2, R2)), q5], 'eqtr3d', '( %s x. %s ) = ( Re ` ( 1 / %s ) )' % (L2, R2, D_))
    RS = '( Re ` ( 1 / %s ) )' % D_
    rsr = c([c([c([], '1cnd', '1 e. CC'), dc, dn], 'divcld', '( 1 / %s ) e. CC' % D_)], 'recld', '%s e. RR' % RS)
    RL = '( Re ` %s )' % LDF(GF, SW)
    rlr = c([c([U.ldf, c([U.lc, U.emc, U.emn], 'divcld', '( %s / %s ) e. CC' % (L2, EM))], 'eqeltrd', '%s e. CC' % LDF(GF, SW))], 'recld', '%s e. RR' % RL)
    hm = c([U.lr, c([c([r2r, numst8(w, A0, '; 1 0', 'RR')], 'readdcld', '( %s + ; 1 0 ) e. RR' % R2), r1r], 'resubcld', '( ( %s + ; 1 0 ) - %s ) e. RR' % (R2, R1)),
            lin8(w, A0, [U.llo], '0 <_ %s' % L2, lv0), lin8(w, A0, [rb], '0 <_ ( ( %s + ; 1 0 ) - %s )' % (R2, R1), lvB)], 'mulge0d', '0 <_ ( %s x. ( ( %s + ; 1 0 ) - %s ) )' % (L2, R2, R1))
    fin = lin8(w, A0, [g1, q6, hm, U.lhi], ante_of(S['zrga'])[1], {RL: rlr, L2: U.lr, R1: r1r, R2: r2r, RS: rsr}, products=True)
    w.qed([fin], 'idi', S['zrga'])
    return run8(w)


def f2ne0(w, A, F, ctr, lo, bstep=None):
    """( A -> ( F ` 2 ) =/= 0 ) from a centre bound ctr : ( t e. RR -> lo <_ abs ( F ` ( 2 + ( _i x. t ) ) ) ), lo > 0;
    or from bstep : ( A -> lo <_ abs ( F ` ( 2 + ( _i x. 0 ) ) ) )"""
    c = Ctx(w, A)
    if bstep is None:
        BD = '%s <_ ( abs ` ( %s ` ( 2 + ( _i x. t ) ) ) )' % (lo, F)
        rg = c.a1(w.s([w.s([], ctr, '( t e. RR -> %s )' % BD)], 'rgen', 'A. t e. RR %s' % BD), 'A. t e. RR %s' % BD)
        b, _ = ral_at(w, A, rg, 't', '0', BD, c([], '0red', '0 e. RR'))
    else:
        b = bstep
    i0 = w.s([w.s([], 'ax-icn', '_i e. CC')], 'mul01i', '( _i x. 0 ) = 0')
    t0 = w.s([i0], 'oveq2i', '( 2 + ( _i x. 0 ) ) = ( 2 + 0 )')
    t1 = w.s([t0, w.s([w.s([], '2cn', '2 e. CC')], 'addridi', '( 2 + 0 ) = 2')], 'eqtri', '( 2 + ( _i x. 0 ) ) = 2')
    fe = c.a1(w.s([w.s([t1], 'fveq2i', '( %s ` ( 2 + ( _i x. 0 ) ) ) = ( %s ` 2 )' % (F, F))], 'fveq2i', '( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) ) = ( abs ` ( %s ` 2 ) )' % (F, F)),
              '( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) ) = ( abs ` ( %s ` 2 ) )' % (F, F))
    b2 = c([b, fe], 'breqtrd', '%s <_ ( abs ` ( %s ` 2 ) )' % (lo, F))
    AF = '( abs ` ( %s ` 2 ) )' % F
    # F ` 2 = 0 -> abs = 0
    A1 = '( %s /\\ ( %s ` 2 ) = 0 )' % (A, F)
    z = w.s([w.s([w.s([], 'simpr', '( %s -> ( %s ` 2 ) = 0 )' % (A1, F))], 'fveq2d', '( %s -> %s = ( abs ` 0 ) )' % (A1, AF)), w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % A1)],
             'eqtrd', '( %s -> %s = 0 )' % (A1, AF))
    b3 = w.s([lift(w, b2, A1), z], 'breqtrd', '( %s -> %s <_ 0 )' % (A1, lo))
    lt = lin8(w, A1, [], '0 < %s' % lo, {})
    nb = w.s([b3, w.s([lift(w, numst8(w, A, lo, 'RR'), A1), w.s([], '0red', '( %s -> 0 e. RR )' % A1)], 'lenltd', '( %s -> ( %s <_ 0 <-> -. 0 < %s ) )' % (A1, lo, lo))], 'mpbid', '( %s -> -. 0 < %s )' % (A1, lo))
    # pm2.65da: ( A /\ F2 = 0 ) -> 0 < lo and -. 0 < lo, so -. F2 = 0
    nn = c([lt, nb], 'pm2.65da', '-. ( %s ` 2 ) = 0' % F)
    return c([nn], 'neqned', '( %s ` 2 ) =/= 0' % F)


def gen_gnn():
    w = W('zrgnn', 'The weight ` ord_g ( q ) - [ q = 1 ] ` of an eta zero ` q ` in the square is in ` NN0 ` , and its term in the pole sum has nonnegative real part ( ~ zrzs , ~ hp0ordf , ~ hp0ordnn ).')
    A0 = ante_of(S['zrgnn'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); wp = c.g('W e. RR+'); qin = c.g('Q e. %s' % ZSE('T'))
    zs = c([c([tr, qin], 'jca', '( T e. RR /\\ Q e. %s )' % ZSE('T')), w.inst('zrzs')], 'syl', tsub(ante_of(S['zrzs'])[1], {}))
    qh = c([c([zs], 'simp1d', '( Q e. %s /\\ ( %s ` Q ) = 0 )' % (HP0, ETA))], 'simpld', 'Q e. %s' % HP0)
    rq1 = c([c([zs], 'simp2d', '( ( 3 / 8 ) <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 )')], 'simprd', '( Re ` Q ) <_ 1')
    g2 = f2ne0(w, A0, GF, 'gfctr', '( 1 / 2 )')
    hol = hol_gf(w, A0)
    HQ = '( ( %s /\\ ( %s ` 2 ) =/= 0 ) /\\ Q e. %s )' % (HOLF(GF, HP0), GF, HP0)
    hq = c([c([hol, g2], 'jca', '( %s /\\ ( %s ` 2 ) =/= 0 )' % (HOLF(GF, HP0), GF)), qh], 'jca', HQ)
    of = c([hq, w.inst('zrord')], 'syl', tsub(ante_of(S['zrord'])[1], {'F': GF, 'P': 'Q'}))
    o0 = c([of], 'simpld', '( %s holord Q ) e. NN0' % GF)
    OG = '( %s holord Q )' % GF
    # case Q = 1
    A1 = '( %s /\\ Q = 1 )' % A0
    c1 = Ctx(w, A1)
    q1 = c1([], 'simpr', 'Q = 1')
    from zc1_f import gval
    gv_, VAL = gval(w, A1, lift(w, qh, A1), 'Q')
    sub0 = c1([c1([c1([q1], 'oveq2d', '( 1 - Q ) = ( 1 - 1 )'), c1([c1([], '1cnd', '1 e. CC')], 'subidd', '( 1 - 1 ) = 0')], 'eqtrd', '( 1 - Q ) = 0')], 'oveq2d', '( 2 ^c ( 1 - Q ) ) = ( 2 ^c 0 )')
    p1 = c1([sub0, c1([c1([], '2cnd', '2 e. CC')], 'cxp0d', '( 2 ^c 0 ) = 1')], 'eqtrd', '( 2 ^c ( 1 - Q ) ) = 1')
    gz = c1([gv_, c1([c1([p1], 'oveq2d', '( 1 - ( 2 ^c ( 1 - Q ) ) ) = ( 1 - 1 )'), c1([c1([], '1cnd', '1 e. CC')], 'subidd', '( 1 - 1 ) = 0')], 'eqtrd', '( 1 - ( 2 ^c ( 1 - Q ) ) ) = 0')],
            'eqtrd', '( %s ` Q ) = 0' % GF)
    onn = c1([gz, c1([lift(w, of, A1)], 'simprd', '( ( %s ` Q ) = 0 -> %s e. NN )' % (GF, OG))], 'mpd', '%s e. NN' % OG)
    it = c1([q1], 'iftrued', 'if ( Q = 1 , 1 , 0 ) = 1')
    e1 = c1([c1([it], 'oveq2d', '%s = ( %s - 1 )' % (GORD('Q'), OG)), c1([onn, w.inst('nnm1nn0')], 'syl', '( %s - 1 ) e. NN0' % OG)], 'eqeltrd', '%s e. NN0' % GORD('Q'))
    A2 = '( %s /\\ Q =/= 1 )' % A0
    c2 = Ctx(w, A2)
    iff = c2([c2([c2([], 'simpr', 'Q =/= 1')], 'neneqd', '-. Q = 1')], 'iffalsed', 'if ( Q = 1 , 1 , 0 ) = 0')
    oc = c2([c2([lift(w, o0, A2)], 'nn0cnd', '%s e. CC' % OG)], 'subid1d', '( %s - 0 ) = %s' % (OG, OG))
    e2 = c2([c2([c2([iff], 'oveq2d', '%s = ( %s - 0 )' % (GORD('Q'), OG)), oc], 'eqtrd', '%s = %s' % (GORD('Q'), OG)), lift(w, o0, A2)], 'eqeltrd', '%s e. NN0' % GORD('Q'))
    gn = c([e1, e2], 'pm2.61dane', '%s e. NN0' % GORD('Q'))
    # Re ( SW - Q ) > 0
    U_wr = c([wp], 'rpred', 'W e. RR')
    ow = c([c([], '1red', '1 e. RR'), U_wr], 'readdcld', '( 1 + W ) e. RR')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    sc = c([c([ow], 'recnd', '( 1 + W ) e. CC'), c([ic, c([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SW)
    sre = c([ow, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + W )' % SW)
    qc = c([qh, c([c([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( Q e. %s <-> ( Q e. CC /\\ 0 < ( Re ` Q ) ) )' % HP0)], 'mpbid', '( Q e. CC /\\ 0 < ( Re ` Q ) )')
    qcc = c([qc], 'simpld', 'Q e. CC')
    rd = c([sc, qcc], 'resubd', '( Re ` ( %s - Q ) ) = ( ( Re ` %s ) - ( Re ` Q ) )' % (SW, SW))
    DQ = '( Re ` ( %s - Q ) )' % SW
    lv = {DQ: c([c([sc, qcc], 'subcld', '( %s - Q ) e. CC' % SW)], 'recld', '%s e. RR' % DQ), '( Re ` %s )' % SW: c([sc], 'recld', '( Re ` %s ) e. RR' % SW),
          '( Re ` Q )': c([qcc], 'recld', '( Re ` Q ) e. RR'), 'W': U_wr}
    dp = lin8(w, A0, [rd, sre, rq1, c([wp], 'rpgt0d', '0 < W')], '0 < %s' % DQ, lv)
    gr = c([gn], 'nn0red', '%s e. RR' % GORD('Q')); g0 = c([gn], 'nn0ge0d', '0 <_ %s' % GORD('Q'))
    rn = c([c([c([gr, g0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (GORD('Q'), GORD('Q'))), c([c([sc, qcc], 'subcld', '( %s - Q ) e. CC' % SW), dp], 'jca', '( ( %s - Q ) e. CC /\\ 0 < %s )' % (SW, DQ))],
               'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( ( %s - Q ) e. CC /\\ 0 < %s ) )' % (GORD('Q'), GORD('Q'), SW, DQ)), w.inst('redivnn')], 'syl', '0 <_ ( Re ` ( %s / ( %s - Q ) ) )' % (GORD('Q'), SW))
    fin = c([gn, dp, rn], '3jca', ante_of(S['zrgnn'])[1])
    w.qed([fin], 'idi', S['zrgnn'])
    return run8(w)


def gen_ord():
    w = W('zrord', 'Orders of a function holomorphic on the half-plane with ` F ( 2 ) =/= 0 ` : in ` NN0 ` , and in ` NN ` at a zero ( ~ hp0ordf , ~ hp0ordnn ; a wrapper free of their ` $d F z ` ).')
    A0 = ante_of(S['zrord'])[0]
    c = Ctx(w, A0)
    o = c([c([], 'id', A0), w.inst('hp0ordf')], 'syl', ante_of(stmt('hp0ordf'))[1])
    o0 = c([o], 'simpld', '( F holord P ) e. NN0')
    A1 = '( %s /\\ ( F ` P ) = 0 )' % A0
    nn = w.s([w.s([], 'id', '( %s -> %s )' % (A1, A1)), w.inst('hp0ordnn')], 'syl', '( %s -> ( F holord P ) e. NN )' % A1)
    fin = c([o0, w.s([nn], 'ex', '( %s -> ( ( F ` P ) = 0 -> ( F holord P ) e. NN ) )' % A0)], 'jca', ante_of(S['zrord'])[1])
    w.qed([fin], 'idi', S['zrord'])
    return run8(w)


def gen_gk():
    from ef4_g import elrab_pack
    w = W('zrgk', 'A pole ` s_K ` , ` K =/= 0 ` , of ` g \' / g ` near height ` T ` is an eta zero in the square ` SQ ( 2 + i T , 13 / 8 ) ` and its term dominates ` Re 1 / ( S - s_K ) ` ( ~ ef5g0 , ~ ef5em , ~ zrord ).')
    A0 = ante_of(S['zrgk'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); wp = c.g('W e. RR+'); kz = c.g('K e. ZZ'); k0 = c.g('K =/= 0'); h = c.g('( abs ` %s ) < ( 1 / 2 )' % PHI('K'))
    wr = c([wp], 'rpred', 'W e. RR')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    pir = c.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR'); pic = c([pir], 'recnd', '_pi e. CC')
    two = numst8(w, A0, '2', 'RR+')
    lr = c([two], 'relogcld', '%s e. RR' % L2); lc = c([lr], 'recnd', '%s e. CC' % L2)
    l2 = c.a1(w.s([], 'zrl2', S['zrl2']), S['zrl2'])
    llo = c([l2], 'simpld', '( 1 / 3 ) < %s' % L2)
    lp = lin8(w, A0, [llo], '0 < %s' % L2, {L2: lr})
    l0 = c([lp], 'gt0ne0d', '%s =/= 0' % L2)
    kr = c([kz], 'zred', 'K e. RR'); kc = c([kr], 'recnd', 'K e. CC')
    N2 = '( 2 x. ( _pi x. K ) )'
    n2r = c([numst8(w, A0, '2', 'RR'), c([pir, kr], 'remulcld', '( _pi x. K ) e. RR')], 'remulcld', '%s e. RR' % N2)
    D = '( %s / %s )' % (N2, L2)
    dr = c([n2r, lr, l0], 'redivcld', '%s e. RR' % D)
    dl = c([c([n2r], 'recnd', '%s e. CC' % N2), lc, l0], 'divcan1d', '( %s x. %s ) = %s' % (D, L2, N2))
    pk = PHI('K')
    phr = c([c([tr, lr], 'remulcld', '( T x. %s ) e. RR' % L2), n2r], 'resubcld', '%s e. RR' % pk)
    ab = c([h, c([phr, numst8(w, A0, '( 1 / 2 )', 'RR'), w.inst('abslt')], 'syl2anc', '( ( abs ` %s ) < ( 1 / 2 ) <-> ( -u ( 1 / 2 ) < %s /\\ %s < ( 1 / 2 ) ) )' % (pk, pk, pk))], 'mpbid',
           '( -u ( 1 / 2 ) < %s /\\ %s < ( 1 / 2 ) )' % (pk, pk))
    ab1 = c([ab], 'simpld', '-u ( 1 / 2 ) < %s' % pk); ab2 = c([ab], 'simprd', '%s < ( 1 / 2 )' % pk)
    lvx = {'T': tr, D: dr, L2: lr, '_pi': pir, 'K': kr}
    lrp = c([lr, lp], 'elrpd', '%s e. RR+' % L2)
    X1, X2 = '( ( T - %s ) + ( 3 / 2 ) )' % D, '( ( %s - T ) + ( 3 / 2 ) )' % D
    out = []
    for X, hh in ((X1, ab1), (X2, ab2)):
        xr = Closure(w, A0, {'T': ('RR', tr), D: ('RR', dr)})
        xr.atom('T'); xr.atom(D)
        xrr = xr.mem(X, 'RR')
        m = lin8(w, A0, [dl, hh, llo], '( 0 x. %s ) < ( %s x. %s )' % (L2, X, L2), lvx, products=True)
        out.append(c([m, c([c([], '0red', '0 e. RR'), xrr, lrp], 'ltmul1d', '( 0 < %s <-> ( 0 x. %s ) < ( %s x. %s ) )' % (X, L2, X, L2))], 'mpbird', '0 < %s' % X))
    # the square
    cl = Closure(w, A0, {'T': ('RR', tr), '_i': ('CC', ic)})
    cl.atom('T'); cl.atom('_i')
    SA = '( %s - ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('T')
    SB = '( %s + ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('T')
    FA, FB = '( ( 3 / 8 ) + ( _i x. ( T - ( ; 1 3 / 8 ) ) ) )', '( ( ; 2 9 / 8 ) + ( _i x. ( T + ( ; 1 3 / 8 ) ) ) )'
    ea = ringeq(w, A0, SA, FA, cl); eb = ringeq(w, A0, SB, FB, cl)
    c38, c298 = numst8(w, A0, '( 3 / 8 )', 'RR'), numst8(w, A0, '( ; 2 9 / 8 )', 'RR')
    tm = c([tr, numst8(w, A0, '( ; 1 3 / 8 )', 'RR')], 'resubcld', '( T - ( ; 1 3 / 8 ) ) e. RR')
    tp = c([tr, numst8(w, A0, '( ; 1 3 / 8 )', 'RR')], 'readdcld', '( T + ( ; 1 3 / 8 ) ) e. RR')
    ra = c([c([ea], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (SA, FA)), c([c38, tm, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 3 / 8 )' % FA)], 'eqtrd', '( Re ` %s ) = ( 3 / 8 )' % SA)
    rb = c([c([eb], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (SB, FB)), c([c298, tp, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( ; 2 9 / 8 )' % FB)], 'eqtrd', '( Re ` %s ) = ( ; 2 9 / 8 )' % SB)
    ia = c([c([ea], 'fveq2d', '( Im ` %s ) = ( Im ` %s )' % (SA, FA)), c([c38, tm, w.inst('crim')], 'syl2anc', '( Im ` %s ) = ( T - ( ; 1 3 / 8 ) )' % FA)], 'eqtrd', '( Im ` %s ) = ( T - ( ; 1 3 / 8 ) )' % SA)
    ib = c([c([eb], 'fveq2d', '( Im ` %s ) = ( Im ` %s )' % (SB, FB)), c([c298, tp, w.inst('crim')], 'syl2anc', '( Im ` %s ) = ( T + ( ; 1 3 / 8 ) )' % FB)], 'eqtrd', '( Im ` %s ) = ( T + ( ; 1 3 / 8 ) )' % SB)
    sac, sbc = cl.mem(SA, 'CC'), cl.mem(SB, 'CC')
    RA, RB, IA, IB = ['( %s ` %s )' % (f, x) for f, x in (('Re', SA), ('Re', SB), ('Im', SA), ('Im', SB))]
    rar, rbr = c([sac], 'recld', '%s e. RR' % RA), c([sbc], 'recld', '%s e. RR' % RB)
    iar, ibr = c([sac], 'imcld', '%s e. RR' % IA), c([sbc], 'imcld', '%s e. RR' % IB)
    lv2 = {RA: rar, RB: rbr, IA: iar, IB: ibr, 'T': tr, D: dr}
    i1 = c([c([c([], '1red', '1 e. RR'), lin8(w, A0, [ra], '%s <_ 1' % RA, lv2), lin8(w, A0, [rb], '1 <_ %s' % RB, lv2)], '3jca', '( 1 e. RR /\\ %s <_ 1 /\\ 1 <_ %s )' % (RA, RB)),
            c([rar, rbr, w.inst('elicc2')], 'syl2anc', '( 1 e. ( %s [,] %s ) <-> ( 1 e. RR /\\ %s <_ 1 /\\ 1 <_ %s ) )' % (RA, RB, RA, RB))], 'mpbird', '1 e. ( %s [,] %s )' % (RA, RB))
    i2 = c([c([dr, lin8(w, A0, [ia, out[1]], '%s <_ %s' % (IA, D), lv2), lin8(w, A0, [ib, out[0]], '%s <_ %s' % (D, IB), lv2)], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (D, IA, D, D, IB)),
            c([iar, ibr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (D, IA, IB, D, IA, D, D, IB))], 'mpbird', '%s e. ( %s [,] %s )' % (D, IA, IB))
    SKK_ = SK('K')
    insq = c([c([c([sac, sbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), c([i1, i2], 'jca', '( 1 e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) )' % (RA, RB, D, IA, IB))], 'jca',
               '( ( %s e. CC /\\ %s e. CC ) /\\ ( 1 e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) ) )' % (SA, SB, RA, RB, D, IA, IB)), w.inst('crectpt')], 'syl', '%s e. %s' % (SKK_, SQ13('T')))
    # SK in HP0, SK =/= 1
    skc = c([c([], '1cnd', '1 e. CC'), c([ic, c([dr], 'recnd', '%s e. CC' % D)], 'mulcld', '( _i x. %s ) e. CC' % D)], 'addcld', '%s e. CC' % SKK_)
    rsk = c([c([], '1red', '1 e. RR'), dr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % SKK_)
    isk = c([c([], '1red', '1 e. RR'), dr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (SKK_, D))
    skh = c([c([skc, c([c.a1(w.s([], '0lt1', '0 < 1'), '0 < 1'), c([rsk], 'eqcomd', '1 = ( Re ` %s )' % SKK_)], 'breqtrd', '0 < ( Re ` %s )' % SKK_)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (SKK_, SKK_)),
             c([c([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (SKK_, HP0, SKK_, SKK_))], 'mpbird', '%s e. %s' % (SKK_, HP0))
    n2n = c([c([], '2cnd', '2 e. CC'), c([pic, kc], 'mulcld', '( _pi x. K ) e. CC'), c.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0'),
             c([pic, kc, c.a1(w.s([], 'pine0', '_pi =/= 0'), '_pi =/= 0'), k0], 'mulne0d', '( _pi x. K ) =/= 0')], 'mulne0d', '%s =/= 0' % N2)
    dn = c([c([n2r], 'recnd', '%s e. CC' % N2), lc, n2n, l0], 'divne0d', '%s =/= 0' % D)
    A1 = '( %s /\\ %s = 1 )' % (A0, SKK_)
    i1_ = w.s([w.s([w.s([], 'simpr', '( %s -> %s = 1 )' % (A1, SKK_))], 'fveq2d', '( %s -> ( Im ` %s ) = ( Im ` 1 ) )' % (A1, SKK_)), w.s([w.s([], 'im1', '( Im ` 1 ) = 0')], 'a1i', '( %s -> ( Im ` 1 ) = 0 )' % A1)],
              'eqtrd', '( %s -> ( Im ` %s ) = 0 )' % (A1, SKK_))
    i2_ = w.s([lift(w, isk, A1), i1_], 'eqtr3d', '( %s -> %s = 0 )' % (A1, D))
    sk1 = c([dn, c([w.s([i2_], 'ex', '( %s -> ( %s = 1 -> %s = 0 ) )' % (A0, SKK_, D))], 'necon3d', '( %s =/= 0 -> %s =/= 1 )' % (D, SKK_))], 'mpd', '%s =/= 1' % SKK_)
    # GF ( SK ) = 0
    g0b = c([skh, w.inst('ef5g0')], 'syl', '( ( %s ` %s ) = 0 <-> E. n e. ZZ %s = %s )' % (GF, SKK_, SKK_, SK('n')))
    eqn, newb = w.wcongr('%s = %s' % (SKK_, SK('n')), {'n': 'K'}, 'n = K', {'n': w.s([], 'id', '( n = K -> n = K )')})
    An = '( %s /\\ n = K )' % A0
    ex = c([kz, w.s([eqn], 'adantl', '( %s -> ( %s = %s <-> %s ) )' % (An, SKK_, SK('n'), newb)), c([], 'eqidd', '%s = %s' % (SKK_, SKK_))], 'rspcedvd', 'E. n e. ZZ %s = %s' % (SKK_, SK('n')))
    gz = c([ex, g0b], 'mpbird', '( %s ` %s ) = 0' % (GF, SKK_))
    em = c([c([skh, sk1], 'jca', '( %s e. %s /\\ %s =/= 1 )' % (SKK_, HP0, SKK_)), w.inst('ef5em')], 'syl', tsub(ante_of(stmt('ef5em'))[1], {'S': SKK_}))
    E1S = '( ( %s ` %s ) / ( %s - 1 ) )' % (E1, SKK_, SKK_)
    import zc1lib as _zc
    e1v = _zc.fcc(w, A0, hol_e1(w, A0), E1, HP0, SKK_, skh)
    e1d = c([e1v, c([skc, c([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % SKK_), c([skc, c([], '1cnd', '1 e. CC'), sk1], 'subne0d', '( %s - 1 ) =/= 0' % SKK_)], 'divcld', '%s e. CC' % E1S)
    ez = c([em, c([c([gz], 'oveq1d', '( ( %s ` %s ) x. %s ) = ( 0 x. %s )' % (GF, SKK_, E1S, E1S)), c([e1d], 'mul02d', '( 0 x. %s ) = 0' % E1S)], 'eqtrd', '( ( %s ` %s ) x. %s ) = 0' % (GF, SKK_, E1S))],
           'eqtrd', '( %s ` %s ) = 0' % (ETA, SKK_))
    inz = elrab_pack(w, A0, 'r', SQ13('T'), '( %s ` r ) = 0' % ETA, SKK_, insq, ez)
    # the order and the term
    g2 = f2ne0(w, A0, GF, 'gfctr', '( 1 / 2 )')
    od = c([c([c([hol_gf(w, A0), g2], 'jca', '( %s /\\ ( %s ` 2 ) =/= 0 )' % (HOLF(GF, HP0), GF)), skh], 'jca', '( ( %s /\\ ( %s ` 2 ) =/= 0 ) /\\ %s e. %s )' % (HOLF(GF, HP0), GF, SKK_, HP0)), w.inst('zrord')],
           'syl', tsub(ante_of(S['zrord'])[1], {'F': GF, 'P': SKK_}))
    OG = '( %s holord %s )' % (GF, SKK_)
    onn = c([gz, c([od], 'simprd', '( ( %s ` %s ) = 0 -> %s e. NN )' % (GF, SKK_, OG))], 'mpd', '%s e. NN' % OG)
    iff = c([c([sk1], 'neneqd', '-. %s = 1' % SKK_)], 'iffalsed', 'if ( %s = 1 , 1 , 0 ) = 0' % SKK_)
    GO = GORD(SKK_)
    geq = c([c([iff], 'oveq2d', '%s = ( %s - 0 )' % (GO, OG)), c([c([onn], 'nncnd', '%s e. CC' % OG)], 'subid1d', '( %s - 0 ) = %s' % (OG, OG))], 'eqtrd', '%s = %s' % (GO, OG))
    gm = c([onn, w.inst('nnm1nn0')], 'syl', '( %s - 1 ) e. NN0' % OG)
    # Re ( 1 / Z ) <_ Re ( GO / Z ), Z = SW - SK
    Z = '( %s - %s )' % (SW, SKK_)
    ow = c([c([], '1red', '1 e. RR'), wr], 'readdcld', '( 1 + W ) e. RR')
    swc = c([c([ow], 'recnd', '( 1 + W ) e. CC'), c([ic, c([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SW)
    zc = c([swc, skc], 'subcld', '%s e. CC' % Z)
    rz = c([swc, skc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (Z, SW, SKK_))
    sre = c([ow, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + W )' % SW)
    RZ = '( Re ` %s )' % Z
    rzp = lin8(w, A0, [rz, sre, rsk, c([wp], 'rpgt0d', '0 < W')], '0 < %s' % RZ, {RZ: c([zc], 'recld', '%s e. RR' % RZ), '( Re ` %s )' % SW: c([swc], 'recld', '( Re ` %s ) e. RR' % SW),
                                                                                   '( Re ` %s )' % SKK_: c([skc], 'recld', '( Re ` %s ) e. RR' % SKK_), 'W': wr})
    zn = c([c([rzp], 'gt0ne0d', '%s =/= 0' % RZ), c([w.s([w.s([w.s([], 'fveq2', '( %s = 0 -> %s = ( Re ` 0 ) )' % (Z, RZ)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> %s = 0 )' % (Z, RZ))], 'a1i',
                                                                                    '( %s -> ( %s = 0 -> %s = 0 ) )' % (A0, Z, RZ))], 'necon3d', '( %s =/= 0 -> %s =/= 0 )' % (RZ, Z))], 'mpd', '%s =/= 0' % Z)
    ogc = c([onn], 'nncnd', '%s e. CC' % OG)
    sp = c([c([], '1cnd', '1 e. CC'), ogc], 'pncan3d', '( 1 + ( %s - 1 ) ) = %s' % (OG, OG))
    om1 = '( %s - 1 )' % OG
    dd = c([c([], '1cnd', '1 e. CC'), c([ogc, c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % om1), zc, zn], 'divdird', '( ( 1 + %s ) / %s ) = ( ( 1 / %s ) + ( %s / %s ) )' % (om1, Z, Z, om1, Z))
    q1 = c([c([c([sp, geq], 'eqtr4d', '( 1 + %s ) = %s' % (om1, GO))], 'oveq1d', '( ( 1 + %s ) / %s ) = ( %s / %s )' % (om1, Z, GO, Z)), dd], 'eqtr3d', '( %s / %s ) = ( ( 1 / %s ) + ( %s / %s ) )' % (GO, Z, Z, om1, Z))
    iz = c([c([], '1cnd', '1 e. CC'), zc, zn], 'divcld', '( 1 / %s ) e. CC' % Z)
    oz = c([c([ogc, c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % om1), zc, zn], 'divcld', '( %s / %s ) e. CC' % (om1, Z))
    r1 = c([c([q1], 'fveq2d', '( Re ` ( %s / %s ) ) = ( Re ` ( ( 1 / %s ) + ( %s / %s ) ) )' % (GO, Z, Z, om1, Z)), c([iz, oz], 'readdd', '( Re ` ( ( 1 / %s ) + ( %s / %s ) ) ) = ( ( Re ` ( 1 / %s ) ) + ( Re ` ( %s / %s ) ) )' % (Z, om1, Z, Z, om1, Z))],
           'eqtrd', '( Re ` ( %s / %s ) ) = ( ( Re ` ( 1 / %s ) ) + ( Re ` ( %s / %s ) ) )' % (GO, Z, Z, om1, Z))
    rn = c([c([c([c([gm], 'nn0red', '%s e. RR' % om1), c([gm], 'nn0ge0d', '0 <_ %s' % om1)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (om1, om1)), c([zc, rzp], 'jca', '( %s e. CC /\\ 0 < %s )' % (Z, RZ))], 'jca',
               '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. CC /\\ 0 < %s ) )' % (om1, om1, Z, RZ)), w.inst('redivnn')], 'syl', '0 <_ ( Re ` ( %s / %s ) )' % (om1, Z))
    R1_, R2_, R3_ = '( Re ` ( %s / %s ) )' % (GO, Z), '( Re ` ( 1 / %s ) )' % Z, '( Re ` ( %s / %s ) )' % (om1, Z)
    goc = c([c([c([geq, ogc], 'eqeltrd', '%s e. CC' % GO), zc, zn], 'divcld', '( %s / %s ) e. CC' % (GO, Z))], 'recld', '%s e. RR' % R1_)
    le = lin8(w, A0, [r1, rn], '%s <_ %s' % (R2_, R1_), {R1_: goc, R2_: c([iz], 'recld', '%s e. RR' % R2_), R3_: c([oz], 'recld', '%s e. RR' % R3_)})
    fin = c([inz, le], 'jca', ante_of(S['zrgk'])[1])
    w.qed([fin], 'idi', S['zrgk'])
    return run8(w)


def gen_gq():
    w = W('zrgq', 'Lean ` re_gFun_logDeriv_le ` : ` Re g \' / g ( S ) <_ 10 + W / ( W ^ 2 + T ^ 2 ) + sum_ q Re ( ( ord_g ( q ) - [ q = 1 ] ) / ( S - q ) ) ` over the eta zeros ` q ` of the square, ` S = ( 1 + W ) + i T ` ; the pole ` s_0 = 1 ` gives the middle term ( ~ zrga , ~ zrgb , ~ zrgk , ~ rddif ).')
    A0 = ante_of(S['zrgq'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); wp = c.g('W e. RR+'); w20 = c.g('W <_ ( 1 / ; 2 0 )')
    wr = c([wp], 'rpred', 'W e. RR')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    pir = c.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
    ppos = c.a1(w.s([], 'pipos', '0 < _pi'), '0 < _pi')
    two = numst8(w, A0, '2', 'RR+')
    lr = c([two], 'relogcld', '%s e. RR' % L2)
    TP = '( 2 x. _pi )'
    tpr = c([numst8(w, A0, '2', 'RR'), pir], 'remulcld', '%s e. RR' % TP)
    tpp = c([numst8(w, A0, '2', 'RR'), pir, lin8(w, A0, [], '0 < 2', {}), ppos], 'mulgt0d', '0 < %s' % TP)
    tp0 = c([tpp], 'gt0ne0d', '%s =/= 0' % TP)
    TL = '( T x. %s )' % L2
    tlr = c([tr, lr], 'remulcld', '%s e. RR' % TL)
    X = '( %s / %s )' % (TL, TP)
    xr = c([tlr, tpr, tp0], 'redivcld', '%s e. RR' % X)
    KF = '( |_ ` ( %s + ( 1 / 2 ) ) )' % X
    kz = c([c([xr, numst8(w, A0, '( 1 / 2 )', 'RR')], 'readdcld', '( %s + ( 1 / 2 ) ) e. RR' % X)], 'flcld', '%s e. ZZ' % KF)
    kr = c([kz], 'zred', '%s e. RR' % KF)
    rd = c([xr, w.inst('rddif')], 'syl', '( abs ` ( %s - %s ) ) <_ ( 1 / 2 )' % (KF, X))
    KX = '( %s - %s )' % (KF, X)
    kxr = c([kr, xr], 'resubcld', '%s e. RR' % KX)
    rd2 = c([rd, c([kxr, numst8(w, A0, '( 1 / 2 )', 'RR')], 'absled', '( ( abs ` %s ) <_ ( 1 / 2 ) <-> ( -u ( 1 / 2 ) <_ %s /\\ %s <_ ( 1 / 2 ) ) )' % (KX, KX, KX))], 'mpbid',
            '( -u ( 1 / 2 ) <_ %s /\\ %s <_ ( 1 / 2 ) )' % (KX, KX))
    xm = c([c([tlr], 'recnd', '%s e. CC' % TL), c([tpr], 'recnd', '%s e. CC' % TP), tp0], 'divcan1d', '( %s x. %s ) = %s' % (X, TP, TL))
    P = PHI(KF)
    phr = c([tlr, c([numst8(w, A0, '2', 'RR'), c([pir, kr], 'remulcld', '( _pi x. %s ) e. RR' % KF)], 'remulcld', '( 2 x. ( _pi x. %s ) ) e. RR' % KF)], 'resubcld', '%s e. RR' % P)
    h1 = c([pir, c([numst8(w, A0, '( 1 / 2 )', 'RR'), kxr], 'resubcld', '( ( 1 / 2 ) - %s ) e. RR' % KX), c([ppos], 'ltled', '0 <_ _pi'), lin8(w, A0, [c([rd2], 'simprd', '%s <_ ( 1 / 2 )' % KX)], '0 <_ ( ( 1 / 2 ) - %s )' % KX, {KX: kxr})],
           'mulge0d', '0 <_ ( _pi x. ( ( 1 / 2 ) - %s ) )' % KX)
    h2 = c([pir, c([numst8(w, A0, '( 1 / 2 )', 'RR'), kxr], 'readdcld', '( ( 1 / 2 ) + %s ) e. RR' % KX), c([ppos], 'ltled', '0 <_ _pi'), lin8(w, A0, [c([rd2], 'simpld', '-u ( 1 / 2 ) <_ %s' % KX)], '0 <_ ( ( 1 / 2 ) + %s )' % KX, {KX: kxr})],
           'mulge0d', '0 <_ ( _pi x. ( ( 1 / 2 ) + %s ) )' % KX)
    lvp = {KF: kr, X: xr, '_pi': pir, 'T': tr, L2: lr}
    pa = lin8(w, A0, [xm, h1], '-u _pi <_ %s' % P, lvp, products=True)
    pb = lin8(w, A0, [xm, h2], '%s <_ _pi' % P, lvp, products=True)
    pab = c([c([pa, pb], 'jca', '( -u _pi <_ %s /\\ %s <_ _pi )' % (P, P)), c([phr, pir], 'absled', '( ( abs ` %s ) <_ _pi <-> ( -u _pi <_ %s /\\ %s <_ _pi ) )' % (P, P, P))], 'mpbird', '( abs ` %s ) <_ _pi' % P)
    # the sum and W / ( W^2 + T^2 ) are nonnegative
    fz = c([tr, w.inst('etazc')], 'syl', tsub(ante_of(stmt('etazc'))[1], {}))
    fin_ = c([fz], 'simp1d', '%s e. Fin' % ZSE('T'))
    Aq = '( %s /\\ q e. %s )' % (A0, ZSE('T'))
    cq = Ctx(w, Aq)
    gn = cq([cq([cq([lift(w, tr, Aq), lift(w, wp, Aq)], 'jca', '( T e. RR /\\ W e. RR+ )'), cq([], 'simpr', 'q e. %s' % ZSE('T'))], 'jca', '( ( T e. RR /\\ W e. RR+ ) /\\ q e. %s )' % ZSE('T')),
             w.inst('zrgnn')], 'syl', tsub(ante_of(S['zrgnn'])[1], {'Q': 'q'}))
    TQ = '( Re ` ( %s / ( %s - q ) ) )' % (GORD('q'), SW)
    tq0 = cq([gn], 'simp3d', '0 <_ %s' % TQ)
    swc = c([c([c([c([], '1red', '1 e. RR'), wr], 'readdcld', '( 1 + W ) e. RR')], 'recnd', '( 1 + W ) e. CC'), c([ic, c([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SW)
    rq = cq([gn], 'simp2d', '0 < ( Re ` ( %s - q ) )' % SW)
    zsq = cq([cq([lift(w, tr, Aq), cq([], 'simpr', 'q e. %s' % ZSE('T'))], 'jca', '( T e. RR /\\ q e. %s )' % ZSE('T')), w.inst('zrzs')], 'syl', tsub(ante_of(S['zrzs'])[1], {'Q': 'q'}))
    qh = cq([cq([zsq], 'simp1d', '( q e. %s /\\ ( %s ` q ) = 0 )' % (HP0, ETA))], 'simpld', 'q e. %s' % HP0)
    qc = cq([cq([qh, cq([cq([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbid', '( q e. CC /\\ 0 < ( Re ` q ) )')], 'simpld', 'q e. CC')
    zq = cq([lift(w, swc, Aq), qc], 'subcld', '( %s - q ) e. CC' % SW)
    zqn = cq([cq([rq], 'gt0ne0d', '( Re ` ( %s - q ) ) =/= 0' % SW), cq([w.s([w.s([w.s([], 'fveq2', '( ( %s - q ) = 0 -> ( Re ` ( %s - q ) ) = ( Re ` 0 ) )' % (SW, SW)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi',
                                                                              '( ( %s - q ) = 0 -> ( Re ` ( %s - q ) ) = 0 )' % (SW, SW))], 'a1i', '( %s -> ( ( %s - q ) = 0 -> ( Re ` ( %s - q ) ) = 0 ) )' % (Aq, SW, SW))],
                                                             'necon3d', '( ( Re ` ( %s - q ) ) =/= 0 -> ( %s - q ) =/= 0 )' % (SW, SW))], 'mpd', '( %s - q ) =/= 0' % SW)
    tqr = cq([cq([cq([cq([gn], 'simp1d', '%s e. NN0' % GORD('q'))], 'nn0cnd', '%s e. CC' % GORD('q')), zq, zqn], 'divcld', '( %s / ( %s - q ) ) e. CC' % (GORD('q'), SW))], 'recld', '%s e. RR' % TQ)
    GT = GTERM(SW)
    gt0 = c([fin_, tqr, tq0], 'fsumge0', '0 <_ %s' % GT)
    gtr = c([fin_, tqr], 'fsumrecl', '%s e. RR' % GT)
    DEN = '( ( W ^ 2 ) + ( T ^ 2 ) )'
    denr = c([c([wr], 'resqcld', '( W ^ 2 ) e. RR'), c([tr], 'resqcld', '( T ^ 2 ) e. RR')], 'readdcld', '%s e. RR' % DEN)
    denp = lin8(w, A0, [c([wr, c([wp], 'rpne0d', 'W =/= 0')], 'sqgt0d', '0 < ( W ^ 2 )'), c([tr], 'sqge0d', '0 <_ ( T ^ 2 )')],
                '0 < %s' % DEN, {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( T ^ 2 )': c([tr], 'resqcld', '( T ^ 2 ) e. RR')})
    wtr = c([wr, denr, c([denp], 'gt0ne0d', '%s =/= 0' % DEN)], 'redivcld', '%s e. RR' % WTT)
    wt0 = c([wr, c([denr, denp], 'elrpd', '%s e. RR+' % DEN), c([wp], 'rpge0d', '0 <_ W')], 'divge0d', '0 <_ %s' % WTT)
    RL = '( Re ` %s )' % LDF(GF, SW)
    GOAL = ante_of(S['zrgq'])[1]
    # case B
    Ab = '( %s /\\ -. ( abs ` %s ) < ( 1 / 2 ) )' % (A0, P)
    cb = Ctx(w, Ab)
    hb = cb([cb([], 'simpr', '-. ( abs ` %s ) < ( 1 / 2 )' % P), cb([lift(w, c([c([phr], 'recnd', '%s e. CC' % P)], 'abscld', '( abs ` %s ) e. RR' % P), Ab), lift(w, numst8(w, A0, '( 1 / 2 )', 'RR'), Ab)], 'lenltd',
                                                                           '( ( 1 / 2 ) <_ ( abs ` %s ) <-> -. ( abs ` %s ) < ( 1 / 2 ) )' % (P, P))], 'mpbird', '( 1 / 2 ) <_ ( abs ` %s )' % P)
    AB_ = '( ( T e. RR /\\ %s ) /\\ ( %s e. ZZ /\\ ( ( 1 / 2 ) <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ _pi ) ) )' % (W20, KF, P, P)
    gb = cb([cb([lift(w, c([tr, c([wp, w20], 'jca', W20)], 'jca', '( T e. RR /\\ %s )' % W20), Ab), cb([lift(w, kz, Ab), cb([hb, lift(w, pab, Ab)], 'jca', '( ( 1 / 2 ) <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ _pi )' % (P, P))], 'jca',
                                                                                                                '( %s e. ZZ /\\ ( ( 1 / 2 ) <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ _pi ) )' % (KF, P, P))], 'jca', AB_), w.inst('zrgb')], 'syl', '%s <_ 0' % RL)
    # case A
    Aa = '( %s /\\ ( abs ` %s ) < ( 1 / 2 ) )' % (A0, P)
    ca = Ctx(w, Aa)
    AA_ = '( ( T e. RR /\\ %s ) /\\ ( %s e. ZZ /\\ ( abs ` %s ) < ( 1 / 2 ) ) )' % (W20, KF, P)
    tw = c([tr, c([wp, w20], 'jca', W20)], 'jca', '( T e. RR /\\ %s )' % W20)
    ga = ca([ca([lift(w, tw, Aa), ca([lift(w, kz, Aa), ca([], 'simpr', '( abs ` %s ) < ( 1 / 2 )' % P)], 'jca', '( %s e. ZZ /\\ ( abs ` %s ) < ( 1 / 2 ) )' % (KF, P))], 'jca', AA_),
             w.inst('zrga')], 'syl', '%s <_ ( ; 1 0 + ( Re ` ( 1 / ( %s - %s ) ) ) )' % (RL, SW, SK(KF)))
    RS = '( Re ` ( 1 / ( %s - %s ) ) )' % (SW, SK(KF))
    lc = c([lr], 'recnd', '%s e. CC' % L2)
    l0 = c([lin8(w, A0, [c([c.a1(w.s([], 'zrl2', S['zrl2']), S['zrl2'])], 'simpld', '( 1 / 3 ) < %s' % L2)], '0 < %s' % L2, {L2: lr})], 'gt0ne0d', '%s =/= 0' % L2)
    kc = c([kr], 'recnd', '%s e. CC' % KF)
    skc = c([c([], '1cnd', '1 e. CC'), c([ic, c([c([c([], '2cnd', '2 e. CC'), c([c([pir], 'recnd', '_pi e. CC'), kc], 'mulcld', '( _pi x. %s ) e. CC' % KF)], 'mulcld', '( 2 x. ( _pi x. %s ) ) e. CC' % KF), lc, l0], 'divcld',
                                                  '( ( 2 x. ( _pi x. %s ) ) / %s ) e. CC' % (KF, L2))], 'mulcld', '( _i x. ( ( 2 x. ( _pi x. %s ) ) / %s ) ) e. CC' % (KF, L2))], 'addcld', '%s e. CC' % SK(KF))
    # subcase K = 0
    A1 = '( %s /\\ %s = 0 )' % (Aa, KF)
    c1 = Ctx(w, A1)
    k0 = c1([], 'simpr', '%s = 0' % KF)
    e1 = c1([c1([k0], 'oveq2d', '( _pi x. %s ) = ( _pi x. 0 )' % KF), c1([c1.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mul01d', '( _pi x. 0 ) = 0')], 'eqtrd', '( _pi x. %s ) = 0' % KF)
    e2 = c1([c1([e1], 'oveq2d', '( 2 x. ( _pi x. %s ) ) = ( 2 x. 0 )' % KF), c1([c1([], '2cnd', '2 e. CC')], 'mul01d', '( 2 x. 0 ) = 0')], 'eqtrd', '( 2 x. ( _pi x. %s ) ) = 0' % KF)
    e3 = c1([c1([e2], 'oveq1d', '( ( 2 x. ( _pi x. %s ) ) / %s ) = ( 0 / %s )' % (KF, L2, L2)), c1([lift(w, lc, A1), lift(w, l0, A1)], 'div0d', '( 0 / %s ) = 0' % L2)], 'eqtrd', '( ( 2 x. ( _pi x. %s ) ) / %s ) = 0' % (KF, L2))
    e4 = c1([c1([e3], 'oveq2d', '( _i x. ( ( 2 x. ( _pi x. %s ) ) / %s ) ) = ( _i x. 0 )' % (KF, L2)), c1([lift(w, ic, A1)], 'mul01d', '( _i x. 0 ) = 0')], 'eqtrd', '( _i x. ( ( 2 x. ( _pi x. %s ) ) / %s ) ) = 0' % (KF, L2))
    e5 = c1([c1([e4], 'oveq2d', '%s = ( 1 + 0 )' % SK(KF)), c1([c1([], '1cnd', '1 e. CC')], 'addridd', '( 1 + 0 ) = 1')], 'eqtrd', '%s = 1' % SK(KF))
    cl = Closure(w, A1, {'W': ('CC', lift(w, c([wr], 'recnd', 'W e. CC'), A1)), 'T': ('CC', lift(w, c([tr], 'recnd', 'T e. CC'), A1)), '_i': ('CC', lift(w, ic, A1))})
    for a_ in ('W', 'T', '_i'):
        cl.atom(a_)
    WT = '( W + ( _i x. T ) )'
    e6 = c1([c1([e5], 'oveq2d', '( %s - %s ) = ( %s - 1 )' % (SW, SK(KF), SW)), ringeq(w, A1, '( %s - 1 )' % SW, WT, cl)], 'eqtrd', '( %s - %s ) = %s' % (SW, SK(KF), WT))
    wtc = cl.mem(WT, 'CC')
    rwt = c1([lift(w, wr, A1), lift(w, tr, A1), w.inst('crre')], 'syl2anc', '( Re ` %s ) = W' % WT)
    wtn = c1([c1([rwt, lift(w, c([wp], 'rpne0d', 'W =/= 0'), A1)], 'eqnetrd', '( Re ` %s ) =/= 0' % WT),
              c1([w.s([w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (WT, WT)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> ( Re ` %s ) = 0 )' % (WT, WT))], 'a1i',
                        '( %s -> ( %s = 0 -> ( Re ` %s ) = 0 ) )' % (A1, WT, WT))], 'necon3d', '( ( Re ` %s ) =/= 0 -> %s =/= 0 )' % (WT, WT))], 'mpd', '%s =/= 0' % WT)
    zr_ = c1([c1([wtc, wtn], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (WT, WT)), w.inst('zrrec')], 'syl', '( Re ` ( 1 / %s ) ) = ( ( Re ` %s ) / ( ( abs ` %s ) ^ 2 ) )' % (WT, WT, WT))
    aq = c1([lift(w, wr, A1), lift(w, tr, A1), w.inst('absreimsq')], 'syl2anc', '( ( abs ` %s ) ^ 2 ) = %s' % (WT, DEN))
    v1 = c1([zr_, c1([rwt, aq], 'oveq12d', '( ( Re ` %s ) / ( ( abs ` %s ) ^ 2 ) ) = %s' % (WT, WT, WTT))], 'eqtrd', '( Re ` ( 1 / %s ) ) = %s' % (WT, WTT))
    v2 = c1([c1([c1([e6], 'oveq2d', '( 1 / ( %s - %s ) ) = ( 1 / %s )' % (SW, SK(KF), WT))], 'fveq2d', '%s = ( Re ` ( 1 / %s ) )' % (RS, WT)), v1], 'eqtrd', '%s = %s' % (RS, WTT))
    s0 = c1([lift(w, ga, A1), c1([v2], 'oveq2d', '( ; 1 0 + %s ) = ( ; 1 0 + %s )' % (RS, WTT))], 'breqtrd', '%s <_ ( ; 1 0 + %s )' % (RL, WTT))
    lvA = {WTT: lift(w, wtr, A1), GT: lift(w, gtr, A1)}
    sre = c([c([c([], '1red', '1 e. RR'), wr], 'readdcld', '( 1 + W ) e. RR'), tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + W )' % SW)
    s1 = lin8(w, A0, [sre, c([wp], 'rpgt0d', '0 < W')], '1 < ( Re ` %s )' % SW, {'( Re ` %s )' % SW: c([swc], 'recld', '( Re ` %s ) e. RR' % SW), 'W': wr})
    gv = c([c([swc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SW, SW)), w.inst('zrgv')], 'syl', tsub(ante_of(S['zrgv'])[1], {'S': SW}))
    smc_ = c([swc, c([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % SW)
    ecc_ = c([c([smc_, lc], 'mulcld', '( ( %s - 1 ) x. %s ) e. CC' % (SW, L2))], 'efcld', '%s e. CC' % E_)
    emc_ = c([ecc_, c([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % EM)
    qc_ = c([lc, emc_, c([gv], 'simpld', '%s =/= 0' % EM)], 'divcld', '( %s / %s ) e. CC' % (L2, EM))
    ldc = c([c([gv], 'simprd', '%s = ( %s / %s )' % (LDF(GF, SW), L2, EM)), qc_], 'eqeltrd', '%s e. CC' % LDF(GF, SW))
    rlr = c([ldc], 'recld', '%s e. RR' % RL)
    lvA[RL] = lift(w, rlr, A1)
    f1 = lin8(w, A1, [s0, lift(w, gt0, A1)], GOAL, lvA)
    # subcase K =/= 0
    A2 = '( %s /\\ %s =/= 0 )' % (Aa, KF)
    c2 = Ctx(w, A2)
    AK = '( ( T e. RR /\\ %s ) /\\ ( ( %s e. ZZ /\\ %s =/= 0 ) /\\ ( abs ` %s ) < ( 1 / 2 ) ) )' % (W20, KF, KF, P)
    gk = c2([c2([lift(w, tw, A2), c2([c2([lift(w, kz, A2), c2([], 'simpr', '%s =/= 0' % KF)], 'jca', '( %s e. ZZ /\\ %s =/= 0 )' % (KF, KF)), c2([c2([], 'simpl', Aa), w.inst('simpr')], 'syl', '( abs ` %s ) < ( 1 / 2 )' % P)],
                                    'jca', '( ( %s e. ZZ /\\ %s =/= 0 ) /\\ ( abs ` %s ) < ( 1 / 2 ) )' % (KF, KF, P))], 'jca', AK), w.inst('zrgk')], 'syl', tsub(ante_of(S['zrgk'])[1], {'K': KF}))
    SKF = SK(KF)
    skin = c2([gk], 'simpld', '%s e. %s' % (SKF, ZSE('T')))
    TK = '( Re ` ( %s / ( %s - %s ) ) )' % (GORD(SKF), SW, SKF)
    tle = c2([gk], 'simprd', '%s <_ %s' % (RS, TK))
    eqq, newq = w.congr(TQ, {'q': SKF}, 'q = %s' % SKF, {'q': w.s([], 'id', '( q = %s -> q = %s )' % (SKF, SKF))})
    assert newq == TK, (newq, TK)
    A2q = '( %s /\\ q e. %s )' % (A2, ZSE('T'))
    c2q = Ctx(w, A2q)
    bridge = c2q([c2q.g(A0), c2q.g('q e. %s' % ZSE('T'))], 'jca', Aq)
    rl = lambda st: w.s([bridge, st], 'syl', '( %s -> %s )' % (A2q, strip_ante(formula_of(w, st), Aq)))
    ge1 = c2([lift(w, fin_, A2), rl(tqr), rl(tq0), eqq, skin], 'fsumge1', '%s <_ %s' % (TK, GT))
    Z2 = '( %s - %s )' % (SW, SKF)
    z2c = c2([lift(w, swc, A2), lift(w, skc, A2)], 'subcld', '%s e. CC' % Z2)
    rz2 = c2([lift(w, swc, A2), lift(w, skc, A2)], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (Z2, SW, SKF))
    D2_ = '( ( 2 x. ( _pi x. %s ) ) / %s )' % (KF, L2)
    d2r = c2([c2([lift(w, numst8(w, A0, '2', 'RR'), A2), c2([lift(w, pir, A2), lift(w, kr, A2)], 'remulcld', '( _pi x. %s ) e. RR' % KF)], 'remulcld', '( 2 x. ( _pi x. %s ) ) e. RR' % KF), lift(w, lr, A2), lift(w, l0, A2)],
              'redivcld', '%s e. RR' % D2_)
    rsk = c2([c2([], '1red', '1 e. RR'), d2r, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % SKF)
    RZ2 = '( Re ` %s )' % Z2
    rz2p = lin8(w, A2, [rz2, lift(w, sre, A2), rsk, lift(w, c([wp], 'rpgt0d', '0 < W'), A2)], '0 < %s' % RZ2,
                {RZ2: c2([z2c], 'recld', '%s e. RR' % RZ2), '( Re ` %s )' % SW: lift(w, c([swc], 'recld', '( Re ` %s ) e. RR' % SW), A2), '( Re ` %s )' % SKF: c2([lift(w, skc, A2)], 'recld', '( Re ` %s ) e. RR' % SKF), 'W': lift(w, wr, A2)})
    z2n = c2([c2([rz2p], 'gt0ne0d', '%s =/= 0' % RZ2),
              c2([w.s([w.s([w.s([], 'fveq2', '( %s = 0 -> %s = ( Re ` 0 ) )' % (Z2, RZ2)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> %s = 0 )' % (Z2, RZ2))], 'a1i',
                        '( %s -> ( %s = 0 -> %s = 0 ) )' % (A2, Z2, RZ2))], 'necon3d', '( %s =/= 0 -> %s =/= 0 )' % (RZ2, Z2))], 'mpd', '%s =/= 0' % Z2)
    rs2 = c2([c2([c2([], '1cnd', '1 e. CC'), z2c, z2n], 'divcld', '( 1 / %s ) e. CC' % Z2)], 'recld', '%s e. RR' % RS)
    gn2 = c2([c2([c2([lift(w, tr, A2), lift(w, wp, A2)], 'jca', '( T e. RR /\\ W e. RR+ )'), skin], 'jca', '( ( T e. RR /\\ W e. RR+ ) /\\ %s e. %s )' % (SKF, ZSE('T'))), w.inst('zrgnn')], 'syl',
              tsub(ante_of(S['zrgnn'])[1], {'Q': SKF}))
    tkr = c2([c2([c2([c2([gn2], 'simp1d', '%s e. NN0' % GORD(SKF))], 'nn0cnd', '%s e. CC' % GORD(SKF)), z2c, z2n], 'divcld', '( %s / %s ) e. CC' % (GORD(SKF), Z2))], 'recld', '%s e. RR' % TK)
    lvB = {WTT: lift(w, wtr, A2), GT: lift(w, gtr, A2), RL: lift(w, rlr, A2), RS: rs2, TK: tkr}
    f2 = lin8(w, A2, [lift(w, ga, A2), tle, ge1, lift(w, wt0, A2)], GOAL, lvB)
    b_fin = lin8(w, Ab, [gb, lift(w, gt0, Ab), lift(w, wt0, Ab)], GOAL, {RL: lift(w, rlr, Ab), WTT: lift(w, wtr, Ab), GT: lift(w, gtr, Ab)})
    fa = ca([f1, f2], 'pm2.61dane', GOAL)
    fin = c([fa, b_fin], 'pm2.61dan', GOAL)
    w.qed([fin], 'idi', S['zrgq'])
    return run8(w)


GENS = {'zrgb': gen_gB, 'zrga': gen_gA, 'zrgnn': gen_gnn, 'zrord': gen_ord, 'zrgk': gen_gk, 'zrgq': gen_gq}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
