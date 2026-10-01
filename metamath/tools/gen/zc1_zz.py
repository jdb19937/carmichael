"""Sortie ZC1: the small-disk zero count (sdzc, Lean sum_ord_smallDisk_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import cl as _cl
from c8_o import numst
from c10_f import crfacts
import c9_h
patch(c9_h)
from c9_h import lf_hol
import zc1_d, zc1_y, zc1_z
import lin
lin.FASTPATH = True

KK = '; ; ; ; ; ; ; 7 0 0 0 0 0 0 0'
KN = '; ; ; ; ; ; ; 1 7 5 0 0 0 0 0'
ZL = ZS(LFN, 'T')
PT = '( 1 + ( _i x. T ) )'
SDF = '{ p e. %s | ( abs ` ( p - %s ) ) <_ W }' % (ZL, PT)
S['sdzc'] = ('( ( %s /\\ ( T e. RR /\\ ( W e. RR+ /\\ W <_ ( 1 / ; 2 0 ) ) ) ) -> sum_ q e. %s ( %s holord q ) <_ ( 6 + ( ( %s x. W ) x. ( log ` %s ) ) ) )') % (CHI, SDF, LFN, KK, XT)
S0 = '( ( 1 + W ) + ( _i x. T ) )'
DSX = lambda z: 'sum_ k e. NN ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u %s ) )' % z


def clo_atoms(w, A0, lv):
    c = _cl.Closure(w, A0, lv)
    for k_ in lv:
        c.atom(k_)
    return c


def gen_sdzc():
    w = W('sdzc', 'Small-disk zero count (Lean ` sum_ord_smallDisk_le ` , ` 5 + 2400000 w log ` there): the zeros of ` L ( s , chi ) ` within ` w ` of ` 1 + i T ` , ` 0 < w <_ 1 / 20 ` , have mass at most ` 6 + 70000000 w log ( N ( abs T + 2 ) ) ` : the Landau expansion ( ~ lndlchrk ) at ` s0 = ( 1 + w ) + i T ` , where every term has nonnegative real part ( ~ redivnn ) and the disc terms at least ` m / ( 4 w ) ` ( ~ redivge ), against ` abs L \' / L ( s0 ) <_ ( 5 / 4 ) / w + 5 ` ( ~ lchrldre ).')
    A0 = ante_of(S['sdzc'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); tr = s([], 'simprl', 'T e. RR'); ww = s([], 'simprr', '( W e. RR+ /\\ W <_ ( 1 / ; 2 0 ) )')
    wp = s([ww, w.inst('simpl')], 'syl', 'W e. RR+'); w20 = s([ww, w.inst('simpr')], 'syl', 'W <_ ( 1 / ; 2 0 )')
    wr = s([wp], 'rpred', 'W e. RR'); wc = s([wp], 'rpcnd', 'W e. CC')
    nx = s([chi, w.inst('simpl')], 'syl', NX)
    hol = lf_hol(w, A0, chi)
    lvw = {'W': wr}
    w1 = lin8(w, A0, [w20], 'W <_ 1', lvw)
    # s0
    ow = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), wr], 'readdcld', '( 1 + W ) e. RR')
    s0c, rs0, is0 = crfacts(w, A0, '( 1 + W )', 'T', ow, tr)
    import c9_h as C9
    c0, re0, im0 = C9.c0_facts(w, A0, tr)
    d0 = s([s([ow], 'recnd', '( 1 + W ) e. CC'), s([], '2cnd', '2 e. CC'), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
           'pnpcan2d', '( %s - %s ) = ( ( 1 + W ) - 2 )' % (S0, C0))
    dr = s([ow, numst(w, A0, '2', 'RR')], 'resubcld', '( ( 1 + W ) - 2 ) e. RR')
    an = s([dr, lin8(w, A0, [w1], '( ( 1 + W ) - 2 ) <_ 0', lvw)], 'absnidd', '( abs ` ( ( 1 + W ) - 2 ) ) = -u ( ( 1 + W ) - 2 )')
    a32 = s([s([s([d0], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( ( 1 + W ) - 2 ) )' % (S0, C0)), an], 'eqtrd', '( abs ` ( %s - %s ) ) = -u ( ( 1 + W ) - 2 )' % (S0, C0)),
             lin8(w, A0, [s([wp], 'rpgt0d', '0 < W')], '-u ( ( 1 + W ) - 2 ) <_ ( 3 / 2 )', lvw)], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( 3 / 2 )' % (S0, C0))
    rsr = s([s0c], 'recld', '( Re ` %s ) e. RR' % S0)
    s01 = lin8(w, A0, [rs0, s([wp], 'rpgt0d', '0 < W')], '1 < ( Re ` %s )' % S0, {'W': wr, '( Re ` %s )' % S0: rsr})
    s0h = s([s([s0c, lin8(w, A0, [s01], '0 < ( Re ` %s )' % S0, {'( Re ` %s )' % S0: rsr})], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (S0, S0)),
             s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (S0, HP0, S0, S0))], 'mpbird', '%s e. %s' % (S0, HP0))
    def lval(ante, x, xh, xc, x1):
        sa = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        v, _ = _cg.mptval(w, ante, 's', HP0, LSs('s'), x, xh, exs=sa([w.s([], 'sumex', '%s e. _V' % LSs(x))], 'a1i', '%s e. _V' % LSs(x)), gen=w.g)
        ag = sa([sa([lift(w, chi, ante), sa([xc, x1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (x, x))], 'jca', '( %s /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (CHI, x, x)), w.inst('lchragr')],
                'syl', '%s = %s' % (LSs(x), DSX(x)))
        ne = sa([sa([lift(w, nx, ante), sa([xc, x1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (x, x))], 'jca', '( %s /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (NX, x, x)), w.inst('lchrne0')],
                'syl', '%s =/= 0' % DSX(x))
        return sa([sa([v, ag], 'eqtrd', '( %s ` %s ) = %s' % (LFN, x, DSX(x))), ne], 'eqnetrd', '( %s ` %s ) =/= 0' % (LFN, x))
    ls0 = lval(A0, S0, s0h, s0c, s01)
    LK = tsub(stmt('lndlchrk'), {'S': S0})
    lka, lkc = ante_of(LK)
    lk = s([s([s([chi, tr], 'jca', top_and(lka)[0]), s([s0c, a32, ls0], '3jca', top_and(lka)[1])], 'jca', lka), w.inst('lndlchrk')], 'syl', lkc)
    LD = tsub(S['lchrldre'], {'S': S0, 'U': 'W'})
    lda, ldc = ante_of(LD)
    ld = s([s([chi, s([s([wp, w1], 'jca', '( W e. RR+ /\\ W <_ 1 )'), s([s0c, rs0], 'jca', '( %s e. CC /\\ ( Re ` %s ) = ( 1 + W ) )' % (S0, S0))], 'jca', top_and(lda)[1])], 'jca', lda), w.inst('lchrldre')],
           'syl', ldc)
    QT = '( ( ( CC _D %s ) ` %s ) / ( %s ` %s ) )' % (LFN, S0, LFN, S0)
    TERM = lambda q: '( ( %s holord %s ) / ( %s - %s ) )' % (LFN, q, S0, q)
    SUM = 'sum_ q e. %s %s' % (ZL, TERM('q'))
    # zeros: finite, orders, Re q <_ 1
    LZ = tsub(S['lchrzc8'], {})
    lz = s([s([chi, tr], 'jca', ante_of(LZ)[0]), w.inst('lchrzc8')], 'syl', ante_of(LZ)[1])
    zlf = s([lz, w.inst('simp1')], 'syl', '%s e. Fin' % ZL); zln = s([lz, w.inst('simp2')], 'syl', 'A. q e. %s ( %s holord q ) e. NN' % (ZL, LFN))
    Aq = '( %s /\\ q e. %s )' % (A0, ZL)
    sq = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    Lq = lambda st: lift(w, st, Aq)
    SQ13 = SQ(C0, R138)
    elq = w.s([w.s([w.s([], 'fveq2', '( r = q -> ( %s ` r ) = ( %s ` q ) )' % (LFN, LFN))], 'eqeq1d', '( r = q -> ( ( %s ` r ) = 0 <-> ( %s ` q ) = 0 ) )' % (LFN, LFN))],
              'elrab', '( q e. %s <-> ( q e. %s /\\ ( %s ` q ) = 0 ) )' % (ZL, SQ13, LFN))
    qq = sq([sq([], 'simpr', 'q e. %s' % ZL), elq], 'sylib', '( q e. %s /\\ ( %s ` q ) = 0 )' % (SQ13, LFN))
    qs = sq([qq, w.inst('simpl')], 'syl', 'q e. %s' % SQ13); q0 = sq([qq, w.inst('simpr')], 'syl', '( %s ` q ) = 0' % LFN)
    import c8_n
    r138 = numst(w, Aq, R138, 'RR')
    qc = sq([sq([s([], 'x', 'x') if False else Lq(c0), r138], 'x', 'x') if False else None], 'x', 'x') if False else None
    sss = sq([sq([sq([Lq(c0), r138], 'jca', '( %s e. CC /\\ %s e. RR )' % (C0, R138)), sq([lin8(w, Aq, [], '%s < 2' % R138, {}), Lq(re0)], 'breqtrrd', '%s < ( Re ` %s )' % (R138, C0))], 'jca',
                  '( ( %s e. CC /\\ %s e. RR ) /\\ %s < ( Re ` %s ) )' % (C0, R138, R138, C0)), w.inst('sqhp0')], 'syl', '%s C_ %s' % (SQ13, HP0))
    qh = sq([sss, qs], 'sseldd', 'q e. %s' % HP0)
    qcc = sq([sq([qh, sq([sq([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbid', '( q e. CC /\\ 0 < ( Re ` q ) )'),
              w.inst('simpl')], 'syl', 'q e. CC')
    rqr = sq([qcc], 'recld', '( Re ` q ) e. RR')
    Aq1 = '( %s /\\ 1 < ( Re ` q ) )' % Aq
    lq1 = lval(Aq1, 'q', lift(w, qh, Aq1), lift(w, qcc, Aq1), w.s([], 'simpr', '( %s -> 1 < ( Re ` q ) )' % Aq1))
    nre = w.s([lift(w, q0, Aq1), lq1], 'x', 'x') if False else w.s([w.s([lift(w, q0, Aq1), lq1], 'x', 'x') if False else None], 'x', 'x') if False else None
    contr = w.s([lq1, w.s([lift(w, q0, Aq1)], 'x', 'x') if False else lift(w, q0, Aq1)], 'x', 'x') if False else None
    nq = w.s([w.s([lift(w, q0, Aq1)], 'x', 'x') if False else lift(w, q0, Aq1), w.s([lq1], 'neneqd', '( %s -> -. ( %s ` q ) = 0 )' % (Aq1, LFN))], 'pm2.65da', '( %s -> -. 1 < ( Re ` q ) )' % Aq)
    rq1 = sq([nq, sq([rqr, sq([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'lenltd', '( ( Re ` q ) <_ 1 <-> -. 1 < ( Re ` q ) )')], 'mpbird', '( Re ` q ) <_ 1')
    DQ = '( %s - q )' % S0
    dqc = sq([Lq(s0c), qcc], 'subcld', '%s e. CC' % DQ)
    rdq = sq([Lq(s0c), qcc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` q ) )' % (DQ, S0))
    lvq = {'W': Lq(wr), '( Re ` q )': rqr, '( Re ` %s )' % S0: Lq(rsr), '( Re ` %s )' % DQ: sq([dqc], 'recld', '( Re ` %s ) e. RR' % DQ)}
    rdw = lin8(w, Aq, [rdq, Lq(rs0), rq1], 'W <_ ( Re ` %s )' % DQ, lvq)
    rd0 = lin8(w, Aq, [rdw, Lq(s([wp], 'rpgt0d', '0 < W'))], '0 < ( Re ` %s )' % DQ, lvq)
    OQ = '( %s holord q )' % LFN
    oqn = w.s([zln], 'r19.21bi', '( %s -> %s e. NN )' % (Aq, OQ))
    oqr = sq([oqn], 'nnred', '%s e. RR' % OQ); oq0 = sq([sq([oqn], 'nnnn0d', '%s e. NN0' % OQ)], 'nn0ge0d', '0 <_ %s' % OQ)
    RN = tsub(S['redivnn'], {'M': OQ, 'Z': DQ})
    tnn = sq([sq([sq([oqr, oq0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (OQ, OQ)), sq([dqc, rd0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (DQ, DQ))], 'jca', ante_of(RN)[0]), w.inst('redivnn')], 'syl', ante_of(RN)[1])
    dqne = sq([dqc, sq([dqc, rd0], 'x', 'x') if False else None], 'x', 'x') if False else None
    # dq =/= 0 from 0 < Re dq
    Adz = '( %s /\\ %s = 0 )' % (Aq, DQ)
    cz = w.s([lift(w, rd0, Adz), w.s([w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (Adz, DQ))], 'fveq2d', '( %s -> ( Re ` %s ) = ( Re ` 0 ) )' % (Adz, DQ)), w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % Adz)],
                                                   'eqtrd', '( %s -> ( Re ` %s ) = 0 )' % (Adz, DQ))], 'breqtrd', '( %s -> 0 < 0 )' % Adz)
    dqn = sq([w.s([cz, w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Adz)], 'ltnrd', '( %s -> -. 0 < 0 )' % Adz)], 'pm2.65da', '( %s -> -. %s = 0 )' % (Aq, DQ))], 'neqned', '%s =/= 0' % DQ)
    tc = sq([sq([oqr], 'recnd', '%s e. CC' % OQ), dqc, dqn], 'divcld', '%s e. CC' % TERM('q'))
    trr = sq([tc], 'recld', '( Re ` %s ) e. RR' % TERM('q'))
    sumc = s([zlf, tc], 'fsumcl', '%s e. CC' % SUM)
    fre = s([zlf, tc], 'fsumre', '( Re ` %s ) = sum_ q e. %s ( Re ` %s )' % (SUM, ZL, TERM('q')))
    # the disc part
    Ap = '( %s /\\ q e. %s )' % (A0, SDF)
    sp = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ap, f))
    elp = w.s([w.s([w.s([w.s([], 'oveq1', '( p = q -> ( p - %s ) = ( q - %s ) )' % (PT, PT))], 'fveq2d', '( p = q -> ( abs ` ( p - %s ) ) = ( abs ` ( q - %s ) ) )' % (PT, PT))], 'breq1d',
                    '( p = q -> ( ( abs ` ( p - %s ) ) <_ W <-> ( abs ` ( q - %s ) ) <_ W ) )' % (PT, PT))], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( abs ` ( q - %s ) ) <_ W ) )' % (SDF, ZL, PT))
    pp = sp([sp([], 'simpr', 'q e. %s' % SDF), elp], 'sylib', '( q e. %s /\\ ( abs ` ( q - %s ) ) <_ W )' % (ZL, PT))
    toAq = sp([sp([], 'simpl', A0), sp([pp, w.inst('simpl')], 'syl', 'q e. %s' % ZL)], 'jca', Aq)
    pw = sp([pp, w.inst('simpr')], 'syl', '( abs ` ( q - %s ) ) <_ W' % PT)
    Lp = lambda st, f: w.s([toAq, st], 'syl', '( %s -> %s )' % (Ap, f))
    ptc = sp([sp([], '1cnd', '1 e. CC'), sp([sp([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), sp([lift(w, tr, Ap)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % PT)
    sp0 = sp([sp([lift(w, wc, Ap), sp([], '1cnd', '1 e. CC'), sp([sp([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), sp([lift(w, tr, Ap)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'x', 'x') if False else None], 'x', 'x') if False else None
    # s0 - PT = W
    ow1 = sp([sp([sp([], '1cnd', '1 e. CC'), lift(w, wc, Ap)], 'addcomd', '( 1 + W ) = ( W + 1 )')], 'oveq1d', '( ( 1 + W ) + ( _i x. T ) ) = ( ( W + 1 ) + ( _i x. T ) )')
    asso = sp([lift(w, wc, Ap), sp([], '1cnd', '1 e. CC'), sp([sp([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), sp([lift(w, tr, Ap)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addassd',
              '( ( W + 1 ) + ( _i x. T ) ) = ( W + %s )' % PT)
    s0pt = sp([sp([sp([ow1, asso], 'eqtrd', '%s = ( W + %s )' % (S0, PT))], 'oveq1d', '( %s - %s ) = ( ( W + %s ) - %s )' % (S0, PT, PT, PT)), sp([lift(w, wc, Ap), ptc], 'pncand', '( ( W + %s ) - %s ) = W' % (PT, PT))],
              'eqtrd', '( %s - %s ) = W' % (S0, PT))
    qc_p = Lp(qcc, 'q e. CC')
    tri = sp([lift(w, s0c, Ap), qc_p, ptc], 'abs3difd' if False else 'x', 'x') if False else sp([sp([lift(w, s0c, Ap), qc_p, ptc], 'x', 'x') if False else None], 'x', 'x') if False else None
    t3 = sp([sp([lift(w, s0c, Ap), qc_p, ptc], '3jca', '( %s e. CC /\\ q e. CC /\\ %s e. CC )' % (S0, PT)), w.inst('abs3dif')], 'syl', '( abs ` ( %s - q ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` ( %s - q ) ) )' % (S0, S0, PT, PT))
    aw = sp([sp([s0pt], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` W )' % (S0, PT)), sp([lift(w, wr, Ap), sp([lift(w, wp, Ap)], 'rpge0d', '0 <_ W')], 'absidd', '( abs ` W ) = W')], 'eqtrd', '( abs ` ( %s - %s ) ) = W' % (S0, PT))
    ab = sp([ptc, qc_p], 'abssubd', '( abs ` ( %s - q ) ) = ( abs ` ( q - %s ) )' % (PT, PT))
    lvp = {'W': lift(w, wr, Ap), '( abs ` ( %s - q ) )' % S0: sp([sp([lift(w, s0c, Ap), qc_p], 'subcld', '( %s - q ) e. CC' % S0)], 'abscld', '( abs ` ( %s - q ) ) e. RR' % S0),
           '( abs ` ( %s - %s ) )' % (S0, PT): sp([sp([lift(w, s0c, Ap), ptc], 'subcld', '( %s - %s ) e. CC' % (S0, PT))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (S0, PT)),
           '( abs ` ( %s - q ) )' % PT: sp([sp([ptc, qc_p], 'subcld', '( %s - q ) e. CC' % PT)], 'abscld', '( abs ` ( %s - q ) ) e. RR' % PT),
           '( abs ` ( q - %s ) )' % PT: sp([sp([qc_p, ptc], 'subcld', '( q - %s ) e. CC' % PT)], 'abscld', '( abs ` ( q - %s ) ) e. RR' % PT)}
    a2w = lin8(w, Ap, [t3, aw, ab, pw], '( abs ` %s ) <_ ( 2 x. W )' % DQ, lvp)
    RG = tsub(S['redivge'], {'M': OQ, 'Z': DQ})
    rga, rgc = ante_of(RG)
    tge = sp([sp([sp([Lp(oqr, '%s e. RR' % OQ), Lp(oq0, '0 <_ %s' % OQ)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (OQ, OQ)), sp([lift(w, wp, Ap), Lp(dqc, '%s e. CC' % DQ)], 'jca', '( W e. RR+ /\\ %s e. CC )' % DQ),
                  sp([Lp(rdw, 'W <_ ( Re ` %s )' % DQ), a2w], 'jca', '( W <_ ( Re ` %s ) /\\ ( abs ` %s ) <_ ( 2 x. W ) )' % (DQ, DQ))], '3jca', rga), w.inst('redivge')], 'syl', rgc)
    W4 = '( 4 x. W )'
    w4p = s([numst(w, A0, '4', 'RR+'), wp], 'rpmulcld', '%s e. RR+' % W4)
    sdfin = s([zlf, s([w.s([], 'ssrab2', '%s C_ %s' % (SDF, ZL))], 'a1i', '%s C_ %s' % (SDF, ZL))], 'ssfid', '%s e. Fin' % SDF)
    le1 = s([sdfin, sp([Lp(oqr, '%s e. RR' % OQ), lift(w, w4p, Ap)], 'rerpdivcld', '( %s / %s ) e. RR' % (OQ, W4)), Lp(trr, '( Re ` %s ) e. RR' % TERM('q')), tge], 'fsumle',
            'sum_ q e. %s ( %s / %s ) <_ sum_ q e. %s ( Re ` %s )' % (SDF, OQ, W4, SDF, TERM('q')))
    le2 = s([zlf, trr, tnn, s([w.s([], 'ssrab2', '%s C_ %s' % (SDF, ZL))], 'a1i', '%s C_ %s' % (SDF, ZL))], 'fsumless', 'sum_ q e. %s ( Re ` %s ) <_ sum_ q e. %s ( Re ` %s )' % (SDF, TERM('q'), ZL, TERM('q')))
    MS = 'sum_ q e. %s %s' % (SDF, OQ)
    dvs = s([sdfin, s([w4p], 'rpcnd', '%s e. CC' % W4), sp([Lp(oqr, '%s e. RR' % OQ)], 'recnd', '%s e. CC' % OQ), s([w4p], 'rpne0d', '%s =/= 0' % W4)], 'fsumdivc', '( %s / %s ) = sum_ q e. %s ( %s / %s )' % (MS, W4, SDF, OQ, W4))
    # Re SUM <_ abs SUM <_ abs QT + abs ( QT - SUM )
    dvc = s([s([s([hol, w.inst('holf')], 'syl', '( CC _D %s ) : %s --> CC' % (LFN, HP0)), s0h], 'ffvelcdmd', '( ( CC _D %s ) ` %s ) e. CC' % (LFN, S0))], 'x', 'x') if False else \
        s([s([hol, w.inst('holf')], 'syl', '( CC _D %s ) : %s --> CC' % (LFN, HP0)), s0h], 'ffvelcdmd', '( ( CC _D %s ) ` %s ) e. CC' % (LFN, S0))
    lc = fcc(w, A0, hol, LFN, HP0, S0, s0h)
    qtc = s([dvc, lc, ls0], 'divcld', '%s e. CC' % QT)
    tr2 = s([qtc, s([qtc, sumc], 'subcld', '( %s - %s ) e. CC' % (QT, SUM))], 'abs2dif2d', '( abs ` ( %s - ( %s - %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (QT, QT, SUM, QT, QT, SUM))
    nn_ = s([qtc, sumc], 'nncand', '( %s - ( %s - %s ) ) = %s' % (QT, QT, SUM, SUM))
    asum = s([s([s([nn_], 'fveq2d', '( abs ` ( %s - ( %s - %s ) ) ) = ( abs ` %s )' % (QT, QT, SUM, SUM))], 'eqcomd', '( abs ` %s ) = ( abs ` ( %s - ( %s - %s ) ) )' % (SUM, QT, QT, SUM)), tr2], 'eqbrtrd',
              '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (SUM, QT, QT, SUM))
    rab = s([sumc, w.inst('releabs')], 'syl', '( Re ` %s ) <_ ( abs ` %s )' % (SUM, SUM))
    LXT = '( log ` %s )' % XT
    nr = s([s([nx, w.inst('simpl')], 'syl', 'N e. NN')], 'nnred', 'N e. RR')
    xtp = s([s([s([nx, w.inst('simpl')], 'syl', 'N e. NN')], 'nnrpd', 'N e. RR+'), s([s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR'), s([], 'x', 'x') if False else numst(w, A0, '2', 'RR')], 'x', 'x') if False else
                                                                            s([s([s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR'), numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` T ) + 2 ) e. RR'),
                                                                               lin8(w, A0, [s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')], '0 < ( ( abs ` T ) + 2 )', {'( abs ` T )': s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')})],
                                                                              'elrpd', '( ( abs ` T ) + 2 ) e. RR+')], 'rpmulcld', '%s e. RR+' % XT)
    lxr = s([xtp], 'relogcld', '%s e. RR' % LXT)
    MSr = s([sdfin, sp([Lp(oqr, '%s e. RR' % OQ)], 'x', 'x') if False else Lp(oqr, '%s e. RR' % OQ)], 'fsumrecl', '%s e. RR' % MS)
    lv = {'W': wr, LXT: lxr, MS: MSr, '( %s / %s )' % (MS, W4): s([MSr, w4p], 'rerpdivcld', '( %s / %s ) e. RR' % (MS, W4)),
          'sum_ q e. %s ( %s / %s )' % (SDF, OQ, W4): s([sdfin, sp([Lp(oqr, '%s e. RR' % OQ), lift(w, w4p, Ap)], 'rerpdivcld', '( %s / %s ) e. RR' % (OQ, W4))], 'fsumrecl', 'sum_ q e. %s ( %s / %s ) e. RR' % (SDF, OQ, W4)),
          'sum_ q e. %s ( Re ` %s )' % (SDF, TERM('q')): s([sdfin, Lp(trr, '( Re ` %s ) e. RR' % TERM('q'))], 'fsumrecl', 'sum_ q e. %s ( Re ` %s ) e. RR' % (SDF, TERM('q'))),
          'sum_ q e. %s ( Re ` %s )' % (ZL, TERM('q')): s([zlf, trr], 'fsumrecl', 'sum_ q e. %s ( Re ` %s ) e. RR' % (ZL, TERM('q'))),
          '( Re ` %s )' % SUM: s([sumc], 'recld', '( Re ` %s ) e. RR' % SUM), '( abs ` %s )' % SUM: s([sumc], 'abscld', '( abs ` %s ) e. RR' % SUM),
          '( abs ` %s )' % QT: s([qtc], 'abscld', '( abs ` %s ) e. RR' % QT), '( abs ` ( %s - %s ) )' % (QT, SUM): s([s([qtc, sumc], 'subcld', '( %s - %s ) e. CC' % (QT, SUM))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (QT, SUM)),
          '( ( 5 / 4 ) / W )': s([numst(w, A0, '( 5 / 4 )', 'RR'), wp], 'rerpdivcld', '( ( 5 / 4 ) / W ) e. RR')}
    c = clo_atoms(w, A0, lv)
    bnd = lin.linarith(w, A0, [le1, le2, fre, rab, asum, ld, lk, dvs], '( %s / %s ) <_ ( ( ( ( 5 / 4 ) / W ) + 5 ) + ( %s x. %s ) )' % (MS, W4, KN, LXT), closure=c)
    RB = '( ( ( ( 5 / 4 ) / W ) + 5 ) + ( %s x. %s ) )' % (KN, LXT)
    mb = s([bnd, s([MSr, c.mem(RB, 'RR'), w4p], 'ledivmuld', '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (MS, W4, RB, MS, W4, RB))], 'mpbid', '%s <_ ( %s x. %s )' % (MS, W4, RB))
    wq = s([s([s([numst(w, A0, '4', 'CC'), wc, s([s([numst(w, A0, '( 5 / 4 )', 'RR'), wp], 'rerpdivcld', '( ( 5 / 4 ) / W ) e. RR')], 'recnd', '( ( 5 / 4 ) / W ) e. CC')], 'mulassd',
                  '( ( 4 x. W ) x. ( ( 5 / 4 ) / W ) ) = ( 4 x. ( W x. ( ( 5 / 4 ) / W ) ) )'), s([s([wc, s([wp], 'rpne0d', 'W =/= 0'), numst(w, A0, '( 5 / 4 )', 'CC')], 'divcan2d', '( W x. ( ( 5 / 4 ) / W ) ) = ( 5 / 4 )')],
                  'oveq2d', '( 4 x. ( W x. ( ( 5 / 4 ) / W ) ) ) = ( 4 x. ( 5 / 4 ) )')], 'eqtrd', '( ( 4 x. W ) x. ( ( 5 / 4 ) / W ) ) = ( 4 x. ( 5 / 4 ) )')], 'x', 'x') if False else \
        s([s([numst(w, A0, '4', 'CC'), wc, s([s([numst(w, A0, '( 5 / 4 )', 'RR'), wp], 'rerpdivcld', '( ( 5 / 4 ) / W ) e. RR')], 'recnd', '( ( 5 / 4 ) / W ) e. CC')], 'mulassd',
             '( ( 4 x. W ) x. ( ( 5 / 4 ) / W ) ) = ( 4 x. ( W x. ( ( 5 / 4 ) / W ) ) )'), s([s([wc, s([wp], 'rpne0d', 'W =/= 0'), numst(w, A0, '( 5 / 4 )', 'CC')], 'divcan2d', '( W x. ( ( 5 / 4 ) / W ) ) = ( 5 / 4 )')],
             'oveq2d', '( 4 x. ( W x. ( ( 5 / 4 ) / W ) ) ) = ( 4 x. ( 5 / 4 ) )')], 'eqtrd', '( ( 4 x. W ) x. ( ( 5 / 4 ) / W ) ) = ( 4 x. ( 5 / 4 ) )')
    fin = lin.linarith(w, A0, [mb, wq, w20, s([wp], 'rpgt0d', '0 < W')], '%s <_ ( 6 + ( ( %s x. W ) x. %s ) )' % (MS, KK, LXT), closure=c, products=True)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['sdzc']))
    return run8(w)


if __name__ == '__main__':
    gen_sdzc()
