"""Sortie ZR, REP: zrhalf (Lean norm_Fdet_ge_half_P1, the triangle step), zrdet (rep_detect_QR at one zero), zrdetg
(rep_detect_QR_of_good)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of


def gen_half():
    w = W('zrhalf', 'Lean ` norm_Fdet_ge_half_P1 ` , the final triangle inequality: ` abs ( F + Q P - E ) <_ P / 8 ` , ` abs E <_ P / 8 ` , ` Q >_ 3 / 4 ` give ` P / 2 <_ abs F ` .')
    A0 = ante_of(S['zrhalf'])[0]
    c = Ctx(w, A0)
    fc, ec, pr, p0, qr, q34, h1, h2 = [c.g(x) for x in ('F e. CC', 'E e. CC', 'P e. RR', '0 <_ P', 'Q e. RR', '( 3 / 4 ) <_ Q', '( abs ` ( ( F + ( Q x. P ) ) - E ) ) <_ ( P / 8 )', '( abs ` E ) <_ ( P / 8 )')]
    QP = '( Q x. P )'
    qpr = c([qr, pr], 'remulcld', '%s e. RR' % QP)
    qpc = c([qpr], 'recnd', '%s e. CC' % QP)
    Z = '( ( F + %s ) - E )' % QP
    zc = c([c([fc, qpc], 'addcld', '( F + %s ) e. CC' % QP), ec], 'subcld', '%s e. CC' % Z)
    cl = Closure(w, A0, {'F': ('CC', fc), 'E': ('CC', ec), QP: ('CC', qpc)})
    for a_ in ('F', 'E', QP):
        cl.atom(a_)
    e = ringeq(w, A0, QP, '( ( %s - F ) + E )' % Z, cl)
    zf = c([zc, fc], 'subcld', '( %s - F ) e. CC' % Z)
    t1 = c([zf, ec], 'abstrid', '( abs ` ( ( %s - F ) + E ) ) <_ ( ( abs ` ( %s - F ) ) + ( abs ` E ) )' % (Z, Z))
    t2 = c([zc, fc], 'abs2dif2d', '( abs ` ( %s - F ) ) <_ ( ( abs ` %s ) + ( abs ` F ) )' % (Z, Z))
    qp0 = c([qr, pr, lin8(w, A0, [q34], '0 <_ Q', {'Q': qr}), p0], 'mulge0d', '0 <_ %s' % QP)
    aq = c([c([e], 'fveq2d', '( abs ` %s ) = ( abs ` ( ( %s - F ) + E ) )' % (QP, Z)), c([qpr, qp0], 'absidd', '( abs ` %s ) = %s' % (QP, QP))], 'eqtr3d', '( abs ` ( ( %s - F ) + E ) ) = %s' % (Z, QP))
    hq = c([c([qr, numst8(w, A0, '( 3 / 4 )', 'RR')], 'resubcld', '( Q - ( 3 / 4 ) ) e. RR'), pr, lin8(w, A0, [q34], '0 <_ ( Q - ( 3 / 4 ) )', {'Q': qr}), p0], 'mulge0d', '0 <_ ( ( Q - ( 3 / 4 ) ) x. P )')
    ab = lambda x: c([x], 'abscld', '( abs ` %s ) e. RR' % strip_ante(formula_of(w, x), A0)[:-len(' e. CC')])
    lv = {'( abs ` ( ( %s - F ) + E ) )' % Z: c([c([zf, ec], 'addcld', '( ( %s - F ) + E ) e. CC' % Z)], 'abscld', '( abs ` ( ( %s - F ) + E ) ) e. RR' % Z),
          '( abs ` ( %s - F ) )' % Z: c([zf], 'abscld', '( abs ` ( %s - F ) ) e. RR' % Z), '( abs ` %s )' % Z: c([zc], 'abscld', '( abs ` %s ) e. RR' % Z),
          '( abs ` F )': c([fc], 'abscld', '( abs ` F ) e. RR'), '( abs ` E )': c([ec], 'abscld', '( abs ` E ) e. RR'), 'P': pr, 'Q': qr}
    fin = lin8(w, A0, [t1, t2, aq, hq, h1, h2], ante_of(S['zrhalf'])[1], lv, products=True)
    w.qed([fin], 'idi', S['zrhalf'])
    return run8(w)


GENS = {'zrhalf': gen_half}


def gen_exq():
    w = W('zrexq', 'For ` log D >_ 200 ` , ` exp ( -1 / D ^ ( 6 / 5 ) ) >_ 3 / 4 ` (the ` hexp ` step of Lean ` norm_Fdet_ge_half_P1 ` ; ~ eflegeo , ~ efneg ).')
    A0 = ante_of(S['zrexq'])[0]
    c = Ctx(w, A0)
    dr, d1, l200 = c.g('D e. RR'), c.g('1 < D'), c.g('; ; 2 0 0 <_ ( log ` D )')
    dp = c([dr, lin8(w, A0, [d1], '0 < D', {'D': dr})], 'elrpd', 'D e. RR+')
    lr = c([dp], 'relogcld', '( log ` D ) e. RR')
    eg = c([lr, lin8(w, A0, [l200], '0 <_ ( log ` D )', {'( log ` D )': lr}), w.inst('bvefge1p')], 'syl2anc', '( 1 + ( log ` D ) ) <_ ( exp ` ( log ` D ) )')
    el = c([dp, w.inst('reeflog')], 'syl', '( exp ` ( log ` D ) ) = D')
    d4 = lin8(w, A0, [eg, el, l200], '4 <_ D', {'D': dr, '( log ` D )': lr, '( exp ` ( log ` D ) )': c([lr], 'reefcld', '( exp ` ( log ` D ) ) e. RR')})
    X = '( D ^c ( 6 / 5 ) )'
    xp = c([dp, numst8(w, A0, '( 6 / 5 )', 'RR')], 'rpcxpcld', '%s e. RR+' % X)
    xr = c([xp], 'rpred', '%s e. RR' % X)
    xl = c([dr, lin8(w, A0, [d1], '1 <_ D', {'D': dr}), c([], '1red', '1 e. RR'), numst8(w, A0, '( 6 / 5 )', 'RR'), lin8(w, A0, [], '1 <_ ( 6 / 5 )', {})], 'cxplead', '( D ^c 1 ) <_ %s' % X)
    x4 = lin8(w, A0, [d4, c([c([dr], 'recnd', 'D e. CC')], 'cxp1d', '( D ^c 1 ) = D'), xl], '4 <_ %s' % X, {'D': dr, X: xr, '( D ^c 1 )': c([dp, c([], '1red', '1 e. RR')], 'rpcxpcld', '( D ^c 1 ) e. RR+') and c([c([dp, c([], '1red', '1 e. RR')], 'rpcxpcld', '( D ^c 1 ) e. RR+')], 'rpred', '( D ^c 1 ) e. RR')})
    IX = '( 1 / %s )' % X
    ixr = c([c([], '1red', '1 e. RR'), xr, c([xp], 'rpne0d', '%s =/= 0' % X)], 'redivcld', '%s e. RR' % IX)
    ix4 = c([numst8(w, A0, '4', 'RR+'), xp, c([], '1red', '1 e. RR'), lin8(w, A0, [], '0 <_ 1', {}), x4], 'lediv2ad', '%s <_ ( 1 / 4 )' % IX)
    ix0 = c([c([], '1red', '1 e. RR'), xp, lin8(w, A0, [], '0 <_ 1', {})], 'divge0d', '0 <_ %s' % IX)
    eg2 = c([ixr, ix0, lin8(w, A0, [ix4], '%s < 1' % IX, {IX: ixr})], 'eflegeo', '( exp ` %s ) <_ ( 1 / ( 1 - %s ) )' % (IX, IX))
    Y = '( 1 / ( 1 - %s ) )' % IX
    omr = c([c([], '1red', '1 e. RR'), ixr], 'resubcld', '( 1 - %s ) e. RR' % IX)
    omp = lin8(w, A0, [ix4], '0 < ( 1 - %s )' % IX, {IX: ixr})
    yv = c([c([], '1cnd', '1 e. CC'), c([omr], 'recnd', '( 1 - %s ) e. CC' % IX), c([omp], 'gt0ne0d', '( 1 - %s ) =/= 0' % IX)], 'divcan1d', '( %s x. ( 1 - %s ) ) = 1' % (Y, IX))
    yr = c([c([], '1red', '1 e. RR'), omr, c([omp], 'gt0ne0d', '( 1 - %s ) =/= 0' % IX)], 'redivcld', '%s e. RR' % Y)
    hy = c([yr, c([numst8(w, A0, '( 1 / 4 )', 'RR'), ixr], 'resubcld', '( ( 1 / 4 ) - %s ) e. RR' % IX), c([c([], '1red', '1 e. RR'), c([omr, omp], 'elrpd', '( 1 - %s ) e. RR+' % IX), lin8(w, A0, [], '0 <_ 1', {})], 'divge0d', '0 <_ %s' % Y),
            lin8(w, A0, [ix4], '0 <_ ( ( 1 / 4 ) - %s )' % IX, {IX: ixr})], 'mulge0d', '0 <_ ( %s x. ( ( 1 / 4 ) - %s ) )' % (Y, IX))
    EI = '( exp ` %s )' % IX
    eir = c([ixr], 'reefcld', '%s e. RR' % EI)
    ey = lin8(w, A0, [eg2, yv, hy], '%s <_ ( 4 / 3 )' % EI, {EI: eir, Y: yr, IX: ixr}, products=True)
    en = c([c([ixr], 'recnd', '%s e. CC' % IX), w.inst('efneg')], 'syl', '( exp ` -u %s ) = ( 1 / %s )' % (IX, EI))
    dn = c([c([], '1cnd', '1 e. CC'), c([xr], 'recnd', '%s e. CC' % X), c([xp], 'rpne0d', '%s =/= 0' % X)], 'divnegd', '-u %s = ( -u 1 / %s )' % (IX, X))
    e2 = c([c([c([dn], 'fveq2d', '( exp ` -u %s ) = %s' % (IX, EXQ))], 'eqcomd', '%s = ( exp ` -u %s )' % (EXQ, IX)), en], 'eqtrd', '%s = ( 1 / %s )' % (EXQ, EI))
    eip = c([ixr, w.inst('efgt0')], 'syl', '0 < %s' % EI)
    rc = c([c([eir, eip], 'elrpd', '%s e. RR+' % EI), numst8(w, A0, '( 4 / 3 )', 'RR+'), c([], '1red', '1 e. RR'), lin8(w, A0, [], '0 <_ 1', {}), ey], 'lediv2ad', '( 1 / ( 4 / 3 ) ) <_ ( 1 / %s )' % EI)
    rd = c([c([c([numst8(w, A0, '4', 'CC'), c([lin8(w, A0, [], '0 < 4', {})], 'gt0ne0d', '4 =/= 0')], 'jca', '( 4 e. CC /\\ 4 =/= 0 )'),
                  c([numst8(w, A0, '3', 'CC'), c([lin8(w, A0, [], '0 < 3', {})], 'gt0ne0d', '3 =/= 0')], 'jca', '( 3 e. CC /\\ 3 =/= 0 )')], 'jca',
                '( ( 4 e. CC /\\ 4 =/= 0 ) /\\ ( 3 e. CC /\\ 3 =/= 0 ) )'), w.inst('recdiv')], 'syl', '( 1 / ( 4 / 3 ) ) = ( 3 / 4 )')
    rc = c([c([rd], 'eqcomd', '( 3 / 4 ) = ( 1 / ( 4 / 3 ) )'), rc], 'eqbrtrd', '( 3 / 4 ) <_ ( 1 / %s )' % EI)
    q = lin8(w, A0, [rc, e2], '( 3 / 4 ) <_ %s' % EXQ, {'( 1 / %s )' % EI: c([c([], '1red', '1 e. RR'), eir, c([eip], 'gt0ne0d', '%s =/= 0' % EI)], 'redivcld', '( 1 / %s ) e. RR' % EI), EXQ: c([e2, c([c([], '1red', '1 e. RR'), eir, c([eip], 'gt0ne0d', '%s =/= 0' % EI)], 'redivcld', '( 1 / %s ) e. RR' % EI)], 'eqeltrd', '%s e. RR' % EXQ)})
    er_ = c([e2, c([c([], '1red', '1 e. RR'), eir, c([eip], 'gt0ne0d', '%s =/= 0' % EI)], 'redivcld', '( 1 / %s ) e. RR' % EI)], 'eqeltrd', '%s e. RR' % EXQ)
    w.qed([c([er_, q], 'jca', ante_of(S['zrexq'])[1])], 'idi', S['zrexq'])
    return run8(w)


GENS['zrexq'] = gen_exq


def gen_det():
    import zl1lib as ZL
    Z6 = ZL.Z6
    w = W('zrdet', 'Lean ` rep_detect_QR ` at one zero (blueprint 7.2(c), ` Q_R ` form): for a zero ` S ` of ` E = ( N DChrLF X ) ` under the hypotheses of ~ zl3dlbz , '
             '` ( 1 / 400 ) Q_R log D <_ abs F ( S ) ` ( ~ z6detall with ~ zl1lif , ~ zl3cvxh ; ~ z5epole , ~ z5ep0 ; ~ zrhalf , ~ zrexq , ~ z5dp1qrd ).')
    A0 = ante_of(S['zrdet'])[0]
    c = Ctx(w, A0)
    hz = c.g(Z6.HZD3); nn_ = c.g('N e. NN'); xb = c.g('X e. ( Base ` ( DChr ` N ) )')
    nx = c([nn_, xb], 'jca', ZL.NX)
    SH = '( ( %s /\\ S =/= 1 ) /\\ %s )' % (Z6.SRNG, Z6.HDN)
    srh = c.g(SH); t1 = c.g(Z6.T1); zr = c.g('( %s ` S ) = 0' % ZL.LF)
    tr_ = c.g(Z6.TRNG)
    HG = '( %s = %s -> %s <_ ( abs ` ( Im ` S ) ) )' % (ZL.CX, ZL.PRN, Z6.LAM60)
    hg = c.g(HG)
    LIFP = '( ( %s /\\ ( %s ` 1 ) = %s ) /\\ %s )' % (ZL.EHOLX, ZL.LF, ZL.RESVX, ZL.DSERX)
    lif = c([nx, w.inst('zl1lif')], 'syl', '( %s /\\ %s )' % (ZL.CHRBX, LIFP))
    chrb = c([lif], 'simpld', ZL.CHRBX)
    lp = c([lif], 'simprd', LIFP)
    eh1 = c([lp], 'simpld', '( %s /\\ ( %s ` 1 ) = %s )' % (ZL.EHOLX, ZL.LF, ZL.RESVX))
    ds = c([lp], 'simprd', ZL.DSERX)
    cvx = c([nx, w.inst('zl3cvxh')], 'syl', ZL.CVXHX)
    LIFX = ZL.CI(Z6.LIF)
    lifx = c([eh1, c([ds, cvx], 'jca', '( %s /\\ %s )' % (ZL.DSERX, ZL.CVXHX))], 'jca', LIFX)
    A7X = ZL.CI(Z6.A7)
    a7a = c([hz, nn_], 'jca', '( %s /\\ N e. NN )' % Z6.HZD3)
    a7b = c([chrb, srh], 'jca', '( %s /\\ %s )' % (ZL.CHRBX, SH))
    a7c = c([t1, c([lifx, zr], 'jca', '( %s /\\ ( %s ` S ) = 0 )' % (LIFX, ZL.LF))], 'jca', '( %s /\\ ( %s /\\ ( %s ` S ) = 0 ) )' % (Z6.T1, LIFX, ZL.LF))
    a7 = c([c([a7a, a7b], 'jca', '( ( %s /\\ N e. NN ) /\\ ( %s /\\ %s ) )' % (Z6.HZD3, ZL.CHRBX, SH)), a7c], 'jca', A7X)
    HD = ante_of(tsub(stmt('z6detall'), {'C': ZL.CX, 'E': ZL.LF}))
    assert HD[0] == A7X, 'antecedent mismatch'
    hdet = c([a7, w.inst('z6detall')], 'syl', HD[1])
    GOAL = ante_of(S['zrdet'])[1]
    P1 = 'sum_ r e. ( N RSet ( D ^c ( 1 / ; ; 1 0 0 ) ) ) ( 1 / r )'
    EPX = '( ( <. ( D ^c ( ; 3 1 / ; 5 0 ) ) , ( D ^c ( ; 6 3 / ; ; 1 0 0 ) ) , ( D ^c ( 6 / 5 ) ) >. EPole <. %s , N , ( D ^c ( 1 / ; ; 1 0 0 ) ) >. ) ` S )'
    EP = EPX % ZL.CX
    dr, d1, l200 = c.g('D e. RR'), c.g('1 < D'), c.g('; ; 2 0 0 <_ ( log ` D )')
    dp = c([dr, lin8(w, A0, [d1], '0 < D', {'D': dr})], 'elrpd', 'D e. RR+')
    lr = c([dp], 'relogcld', '( log ` D ) e. RR')
    sr_ = c([srh], 'simpld', '( %s /\\ S =/= 1 )' % Z6.SRNG)
    srng = c([sr_], 'simpld', Z6.SRNG)
    sc = c([srng], 'simpld', 'S e. CC')
    rs1 = c([c([srng], 'simprd', '( ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 )')], 'simprd', '( Re ` S ) <_ 1')
    rs0 = c([c([srng], 'simprd', '( ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 )')], 'simpld', '( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )')
    rsr = c([sc], 'recld', '( Re ` S ) e. RR')
    tr = c([tr_], 'simpld', 'T e. RR'); t0 = c([c([tr_], 'simprd', '( 0 <_ T /\\ T <_ ( Re ` S ) )')], 'simpld', '0 <_ T')
    tS = c([c([tr_], 'simprd', '( 0 <_ T /\\ T <_ ( Re ` S ) )')], 'simprd', 'T <_ ( Re ` S )')
    # LAM60 >_ 1 / 2
    ll0 = c([lr, lin8(w, A0, [l200], '1 <_ ( log ` D )', {'( log ` D )': lr})], 'logge0d', '0 <_ ( log ` ( log ` D ) )')
    lm = c([numst8(w, A0, '( 6 / 5 )', 'RR'), c([c([c([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR'), lr], 'remulcld', '( ( 1 - T ) x. ( log ` D ) ) e. RR'),
               lin8(w, A0, [], '0 <_ ( 6 / 5 )', {}),
               c([c([c([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR'), lr, lin8(w, A0, [tS, rs1], '0 <_ ( 1 - T )', {'T': tr, '( Re ` S )': rsr}), lin8(w, A0, [l200], '0 <_ ( log ` D )', {'( log ` D )': lr})],
                 'mulge0d', '0 <_ ( ( 1 - T ) x. ( log ` D ) )')], 'mulge0d', '0 <_ ( ( 6 / 5 ) x. ( ( 1 - T ) x. ( log ` D ) ) )')
    XE = '( ( ; ; ; 3 2 0 0 x. ( exp ` 1 ) ) x. ; 6 0 )'
    ep1 = c([c([], '1red', '1 e. RR')], 'reefcld', '( exp ` 1 ) e. RR')
    ep1p = c([c([], '1red', '1 e. RR'), w.inst('efgt0')], 'syl', '0 < ( exp ` 1 )')
    xer = c([c([numst8(w, A0, '; ; ; 3 2 0 0', 'RR'), ep1], 'remulcld', '( ; ; ; 3 2 0 0 x. ( exp ` 1 ) ) e. RR'), numst8(w, A0, '; 6 0', 'RR')], 'remulcld', '%s e. RR' % XE)
    h_e = c([numst8(w, A0, '; ; ; 3 2 0 0', 'RR'), ep1, lin8(w, A0, [], '0 <_ ; ; ; 3 2 0 0', {}), c([ep1p], 'ltled', '0 <_ ( exp ` 1 )')], 'mulge0d', '0 <_ ( ; ; ; 3 2 0 0 x. ( exp ` 1 ) )')
    eg1 = c([c([], '1red', '1 e. RR'), lin8(w, A0, [], '0 <_ 1', {}), w.inst('bvefge1p')], 'syl2anc', '( 1 + 1 ) <_ ( exp ` 1 )')
    xe1 = lin8(w, A0, [eg1], '1 <_ %s' % XE, {'( exp ` 1 )': ep1}, products=True)
    lx0 = c([xer, xe1], 'logge0d', '0 <_ ( log ` %s )' % XE)
    xee = lin8(w, A0, [c([ep1p], 'ltled', '0 <_ ( exp ` 1 )')], '( exp ` 1 ) <_ %s' % XE, {'( exp ` 1 )': ep1}, products=True)
    xep = c([xer, lin8(w, A0, [xe1], '0 < %s' % XE, {XE: xer})], 'elrpd', '%s e. RR+' % XE)
    lxe = c([xee, c([c([ep1, ep1p], 'elrpd', '( exp ` 1 ) e. RR+'), xep, w.inst('logleb')], 'syl2anc', '( ( exp ` 1 ) <_ %s <-> ( log ` ( exp ` 1 ) ) <_ ( log ` %s ) )' % (XE, XE))], 'mpbid',
            '( log ` ( exp ` 1 ) ) <_ ( log ` %s )' % XE)
    le1 = c([c([], '1red', '1 e. RR')], 'relogefd', '( log ` ( exp ` 1 ) ) = 1')
    lamr = Closure(w, A0, {'( log ` ( log ` D ) )': ('RR', c([c([lr, lin8(w, A0, [l200], '0 < ( log ` D )', {'( log ` D )': lr})], 'elrpd', '( log ` D ) e. RR+')], 'relogcld', '( log ` ( log ` D ) ) e. RR')),
                            'T': ('RR', tr), '( log ` D )': ('RR', lr), '( log ` %s )' % XE: ('RR', c([c([xer, lin8(w, A0, [xe1], '0 < %s' % XE, {XE: xer})], 'elrpd', '%s e. RR+' % XE)], 'relogcld', '( log ` %s ) e. RR' % XE))})
    for a_ in ('( log ` ( log ` D ) )', 'T', '( log ` D )', '( log ` %s )' % XE):
        lamr.atom(a_)
    lam_r = lamr.mem(Z6.LAM60, 'RR')
    lam_h = lin8(w, A0, [ll0, lm, lxe, le1], '( 1 / 2 ) <_ %s' % Z6.LAM60, {'( log ` ( log ` D ) )': lamr.mem('( log ` ( log ` D ) )', 'RR'), '( log ` %s )' % XE: lamr.mem('( log ` %s )' % XE, 'RR'),
                                                                              '( ( 1 - T ) x. ( log ` D ) )': c([c([c([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR'), lr], 'remulcld', '( ( 1 - T ) x. ( log ` D ) ) e. RR'),
                                                                              '( log ` ( exp ` 1 ) )': c([c([ep1, ep1p], 'elrpd', '( exp ` 1 ) e. RR+')], 'relogcld', '( log ` ( exp ` 1 ) ) e. RR')})
    # ( CX = PRN -> 1/2 <_ abs Im S )
    Ap = '( %s /\\ %s = %s )' % (A0, ZL.CX, ZL.PRN)
    cpp = Ctx(w, Ap)
    lh = cpp([cpp([], 'simpr', '%s = %s' % (ZL.CX, ZL.PRN)), lift(w, hg, Ap)], 'mpd', '%s <_ ( abs ` ( Im ` S ) )' % Z6.LAM60)
    AIS = '( abs ` ( Im ` S ) )'
    ais = cpp([cpp([lift(w, sc, Ap)], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')
    h2 = lin8(w, Ap, [lh, lift(w, lam_h, Ap)], '( 1 / 2 ) <_ %s' % AIS, {AIS: cpp([ais], 'abscld', '%s e. RR' % AIS), Z6.LAM60: lift(w, lam_r, Ap)})
    hh = w.s([h2], 'ex', '( %s -> ( %s = %s -> ( 1 / 2 ) <_ %s ) )' % (A0, ZL.CX, ZL.PRN, AIS))
    CHR1 = top_and(top_and(ZL.CHRBX)[0])[0]
    cf = c([c([chrb], 'simpld', top_and(ZL.CHRBX)[0])], 'simp1d', CHR1)
    cab = c([chrb], 'simprd', top_and(ZL.CHRBX)[1])
    ECA = ante_of(tsub(stmt('z5epcl'), {'C': ZL.CX}))
    epc = c([c([a7a, c([sc, c([cf, hh], 'jca', top_and(top_and(ECA[0])[1])[1])], 'jca', top_and(ECA[0])[1])], 'jca', ECA[0]), w.inst('z5epcl')], 'syl', ECA[1])
    FCA = ante_of(tsub(stmt('z6fdvcl'), {'C': ZL.CX}))
    re0 = lin8(w, A0, [rs0], '0 <_ ( Re ` S )', {'( Re ` S )': rsr})
    fdc = c([c([c([a7a, c([cf, cab], 'jca', top_and(top_and(FCA[0])[0])[1])], 'jca', top_and(FCA[0])[0]), c([sc, re0], 'jca', top_and(FCA[0])[1])], 'jca', FCA[0]), w.inst('z6fdvcl')], 'syl', FCA[1])
    # P1
    RR_ = '( D ^c ( 1 / ; ; 1 0 0 ) )'
    nv = c([nn_], 'elexd', 'N e. _V')
    rv = c([], 'ovexd', '%s e. _V' % RR_)
    p10 = c([nv, rv, w.inst('z5p1ge0')], 'syl2anc', '0 <_ %s' % P1)
    rs = c([nv, rv, w.inst('z5rsetfi')], 'syl2anc', '( ( N RSet %s ) C_ ( 1 ... ( |_ ` %s ) ) /\\ ( N RSet %s ) e. Fin )' % (RR_, RR_, RR_))
    Ar = '( %s /\\ r e. ( N RSet %s ) )' % (A0, RR_)
    crr = Ctx(w, Ar)
    rnn = crr([crr([lift(w, c([rs], 'simpld', '( N RSet %s ) C_ ( 1 ... ( |_ ` %s ) )' % (RR_, RR_)), Ar), crr([], 'simpr', 'r e. ( N RSet %s )' % RR_)], 'sseldd', 'r e. ( 1 ... ( |_ ` %s ) )' % RR_),
               w.inst('elfznn')], 'syl', 'r e. NN')
    p1r = c([c([rs], 'simprd', '( N RSet %s ) e. Fin' % RR_), crr([crr([], '1red', '1 e. RR'), crr([rnn], 'nnred', 'r e. RR'), crr([rnn], 'nnne0d', 'r =/= 0')], 'redivcld', '( 1 / r ) e. RR')],
             'fsumrecl', '%s e. RR' % P1)
    # the pole term
    Ap1 = '( %s /\\ %s = %s )' % (A0, ZL.CX, ZL.PRN)
    c1 = Ctx(w, Ap1)
    L1 = lambda st: lift(w, st, Ap1)
    EPA = ante_of(tsub(stmt('z5epole'), {'K': '; 6 0'}))
    gam = c1.a1(w.s([], 'z5dgamh', stmt('z5dgamh')), stmt('z5dgamh'))
    Q = top_and(EPA[0])
    t1_ = c1([L1(tr), c1([L1(t0), lin8(w, Ap1, [L1(tS), L1(rs1)], 'T <_ 1', {'T': L1(tr), '( Re ` S )': L1(rsr)})], 'jca', '( 0 <_ T /\\ T <_ 1 )')], 'jca', '( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) )')
    k60 = c1([numst8(w, Ap1, '; 6 0', 'RR'), lin8(w, Ap1, [], '1 <_ ; 6 0', {})], 'jca', '( ; 6 0 e. RR /\\ 1 <_ ; 6 0 )')
    lh1 = c1([c1([], 'simpr', '%s = %s' % (ZL.CX, ZL.PRN)), L1(hg)], 'mpd', '%s <_ ( abs ` ( Im ` S ) )' % Z6.LAM60)
    ep_a = c1([c1([L1(a7a), c1([c1([t1_, k60], 'jca', '( ( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) ) /\\ ( ; 6 0 e. RR /\\ 1 <_ ; 6 0 ) )'),
                                   c1([c1([gam, c1([L1(sc), c1([L1(tS), L1(rs1)], 'jca', '( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 )')], 'jca', '( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) )')],
                                           'jca', top_and(top_and(Q[1])[1])[0]), lh1], 'jca', top_and(Q[1])[1])], 'jca', Q[1])], 'jca', EPA[0]), w.inst('z5epole')], 'syl', EPA[1])
    ceq = c1([], 'simpr', '%s = %s' % (ZL.CX, ZL.PRN))
    eqe, newe = w.congr(EP, {}, Ap1, {}, rules={ZL.CX: (ZL.PRN, ceq)})
    EPP = EPX % ZL.PRN
    assert newe == EPP, newe
    ba = c1([c1([eqe], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (EP, EPP)), ep_a], 'eqbrtrd', '( abs ` %s ) <_ ( %s / 8 )' % (EP, P1))
    Ap2 = '( %s /\\ %s =/= %s )' % (A0, ZL.CX, ZL.PRN)
    c2 = Ctx(w, Ap2)
    L2 = lambda st: lift(w, st, Ap2)
    PRH = '( h e. NN |-> if ( ( h gcd N ) = 1 , 1 , 0 ) )'
    ecb, _ = w.congr('if ( ( n gcd N ) = 1 , 1 , 0 )', {'n': 'h'}, 'n = h', {'n': w.s([], 'id', '( n = h -> n = h )')})
    cbv = w.s([ecb], 'cbvmptv', '%s = %s' % (ZL.PRN, PRH))
    neh = c2([c2([], 'simpr', '%s =/= %s' % (ZL.CX, ZL.PRN)), c2([c2.a1(cbv, '%s = %s' % (ZL.PRN, PRH))], 'neeq2d', '( %s =/= %s <-> %s =/= %s )' % (ZL.CX, ZL.PRN, ZL.CX, PRH))], 'mpbid', '%s =/= %s' % (ZL.CX, PRH))
    E0A = ante_of(tsub(stmt('z5ep0'), {'A': '( D ^c ( ; 3 1 / ; 5 0 ) )', 'B': '( D ^c ( ; 6 3 / ; ; 1 0 0 ) )', 'X': '( D ^c ( 6 / 5 ) )', 'C': ZL.CX, 'R': RR_,
                                             'U': '_V', 'V': '_V', 'W': '_V', 'T': '_V', 'Y': '_V', 'Z': '_V'}))
    sets = c2([c2([c2([], 'ovexd', '( D ^c ( ; 3 1 / ; 5 0 ) ) e. _V'), c2([], 'ovexd', '( D ^c ( ; 6 3 / ; ; 1 0 0 ) ) e. _V'), c2([], 'ovexd', '( D ^c ( 6 / 5 ) ) e. _V')], '3jca', top_and(top_and(top_and(E0A[0])[0])[0])[0]),
               c2([c2.a1(w.s([], 'mptex', '%s e. _V' % ZL.CX), '%s e. _V' % ZL.CX), L2(nv), c2([], 'ovexd', '%s e. _V' % RR_)], '3jca', top_and(top_and(top_and(E0A[0])[0])[0])[1])], 'jca', top_and(top_and(E0A[0])[0])[0])
    e0 = c2([c2([c2([sets, L2(sc)], 'jca', top_and(E0A[0])[0]), neh], 'jca', E0A[0]), w.inst('z5ep0')], 'syl', E0A[1])
    bb = c2([c2([c2([e0], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % EP), c2.a1(w.s([], 'abs0', '( abs ` 0 ) = 0'), '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % EP),
             lin8(w, Ap2, [L2(p10)], '0 <_ ( %s / 8 )' % P1, {P1: L2(p1r)})], 'eqbrtrd', '( abs ` %s ) <_ ( %s / 8 )' % (EP, P1))
    epb = c([w.s([ba], 'ex', '( %s -> ( %s = %s -> ( abs ` %s ) <_ ( %s / 8 ) ) )' % (A0, ZL.CX, ZL.PRN, EP, P1)), w.s([bb], 'ex', '( %s -> ( %s =/= %s -> ( abs ` %s ) <_ ( %s / 8 ) ) )' % (A0, ZL.CX, ZL.PRN, EP, P1))],
            'pm2.61dne', '( abs ` %s ) <_ ( %s / 8 )' % (EP, P1))
    # half and Q_R
    xq = c([hz, w.inst('zrexq')], 'syl', ante_of(S['zrexq'])[1])
    HA = ante_of(tsub(S['zrhalf'], {'F': FDVX[len('( abs ` '):-2], 'E': EP, 'P': P1, 'Q': EXQ}))
    hl = c([c([c([fdc, epc], 'jca', top_and(HA[0])[0]), c([p1r, p10], 'jca', top_and(HA[0])[1]), c([c([xq], 'simpld', '%s e. RR' % EXQ), c([c([xq], 'simprd', '( 3 / 4 ) <_ %s' % EXQ), c([hdet, epb], 'jca', top_and(top_and(top_and(HA[0])[2])[1])[1])], 'jca', top_and(top_and(HA[0])[2])[1])], 'jca', top_and(HA[0])[2])],
               '3jca', HA[0]), w.inst('zrhalf')], 'syl', HA[1])
    qa = c([nn_, dp, w.inst('z5dp1qrd')], 'syl2anc', ante_of(stmt('z5dp1qrd'))[1])
    QR = QRPD('D')
    QS = '{ q e. Prime | ( q || N /\\ q <_ %s ) }' % RR_
    QD = '{ q e. Prime | q || N }'
    PD = '{ p e. Prime | p || N }'
    ecp, _ = w.wcongr('p || N', {'p': 'q'}, 'p = q', {'p': w.s([], 'id', '( p = q -> p = q )')})
    cbq = w.s([ecp], 'cbvrabv', '%s = %s' % (PD, QD))
    qdf = c([c.a1(cbq, '%s = %s' % (PD, QD)), c([nn_, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PD)], 'eqeltrrd', '%s e. Fin' % QD)
    qss = c.a1(w.s([w.s([w.s([], 'simpl', '( ( q || N /\\ q <_ %s ) -> q || N )' % RR_)], 'a1i', '( q e. Prime -> ( ( q || N /\\ q <_ %s ) -> q || N ) )' % RR_)], 'ss2rabi', '%s C_ %s' % (QS, QD)), '%s C_ %s' % (QS, QD))
    qsf = c([qdf, qss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % QS)
    Aq_ = '( %s /\\ p e. %s )' % (A0, QS)
    cq_ = Ctx(w, Aq_)
    pn = cq_([cq_([cq_([], 'simpr', 'p e. %s' % QS), w.inst('elrabi')], 'syl', 'p e. Prime'), w.inst('prmnn')], 'syl', 'p e. NN')
    tr1 = cq_([cq_([], '1red', '1 e. RR'), cq_([cq_([], '1red', '1 e. RR'), cq_([pn], 'nnred', 'p e. RR'), cq_([pn], 'nnne0d', 'p =/= 0')], 'redivcld', '( 1 / p ) e. RR')], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    qrr = c([qsf, tr1], 'fprodrecl', '%s e. RR' % QR)
    lvf = {P1: p1r, FDVX: c([fdc], 'abscld', '%s e. RR' % FDVX), '( log ` D )': lr, QR: qrr}
    fin = lin8(w, A0, [hl, qa], GOAL, lvf, products=True)
    w.qed([fin], 'idi', S['zrdet'])
    return run8(w)


GENS['zrdet'] = gen_det


def gen_detg():
    import zl1lib as ZL
    Z6 = ZL.Z6
    from zr_k import ri_facts, cell_facts
    from zr_i import scale_facts
    w = W('zrdetg', 'Lean ` rep_detect_QR_of_good ` (blueprint 7.2(c)): every zero ` A ` in the cell of an index ` Q ` of a parity system is detected, '
             '` ( 1 / 400 ) Q_R log D <_ abs F ( A ) ` , ` D = N ( T + 2 ) ` , the principal-character height clause supplied by ` G ` ( ~ zrdet , ~ zl1prn ).')
    A0 = ante_of(S['zrdetg'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0 = [c.g(x) for x in ('N e. NN', 'Y C_ ( Base ` ( DChr ` N ) )', 'S e. RR', '( ; 9 9 / ; ; 1 0 0 ) <_ S', 'S <_ 1', 'T e. RR', '0 <_ T')]
    l200, t1, hgood = c.g('; ; 2 0 0 <_ %s' % LD), c.g(T1G), c.g(HGOOD)
    qin, ain = c.g('Q e. %s' % RI('P')), c.g('A e. %s' % CELL('( 1st ` Q )', '( 2nd ` Q )'))
    qxp, cne, par, q2z, q1, q2 = ri_facts(w, A0, qin, 'Q')
    fa = cell_facts(w, A0, ain, 'A', '( 1st ` Q )', '( 2nd ` Q )', sr, tr)
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    xb = c([ys, q1], 'sseldd', '( 1st ` Q ) e. ( Base ` ( DChr ` N ) )')
    SUB = {'D': DSC, 'X': '( 1st ` Q )', 'S': 'A', 'T': 'S'}
    DA = ante_of(tsub(S['zrdet'], SUB))
    hz = c([dr, lin8(w, A0, [d2], '1 < %s' % DSC, {DSC: dr}), l200], '3jca', tsub(Z6.HZD3, SUB))
    nx = c([nn_, xb], 'jca', tsub(ZL.NX, SUB))
    rA = fa['rer']
    ra99 = lin8(w, A0, [s99, fa['re1']], '( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` A )', {'S': sr, '( Re ` A )': rA})
    srng = c([fa['cc'], c([ra99, fa['re2']], 'jca', '( ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` A ) /\\ ( Re ` A ) <_ 1 )')], 'jca', tsub(Z6.SRNG, SUB))
    an1 = c([fa['zp']], 'simpld', 'A =/= 1'); aez = c([fa['zp']], 'simprd', '( %s ` A ) = 0' % EX('( 1st ` Q )'))
    AI = '( abs ` ( Im ` A ) )'
    air = c([c([fa['cc']], 'imcld', '( Im ` A ) e. RR') and c([c([fa['cc']], 'imcld', '( Im ` A ) e. RR')], 'recnd', '( Im ` A ) e. CC')], 'abscld', '%s e. RR' % AI)
    nr = c([nn_], 'nnred', 'N e. RR')
    hn = c([nr, c([tr, air], 'resubcld', '( T - %s ) e. RR' % AI), lin8(w, A0, [c([nn_], 'nnge1d', '1 <_ N')], '0 <_ N', {'N': nr}), lin8(w, A0, [fa['im']], '0 <_ ( T - %s )' % AI, {AI: air, 'T': tr})],
           'mulge0d', '0 <_ ( N x. ( T - %s ) )' % AI)
    hdn = lin8(w, A0, [hn], tsub(Z6.HDN, SUB), {'N': nr, AI: air, 'T': tr}, products=True)
    trng = c([sr, c([lin8(w, A0, [s99], '0 <_ S', {'S': sr}), fa['re1']], 'jca', '( 0 <_ S /\\ S <_ ( Re ` A ) )')], 'jca', tsub(Z6.TRNG, SUB))
    # height clause
    CXQ = tsub(ZL.CX, SUB)
    Ap = '( %s /\\ %s = %s )' % (A0, CXQ, ZL.PRN)
    cp = Ctx(w, Ap)
    pr = cp([lift(w, nx, Ap), w.inst('zl1prn')], 'syl', '( %s = %s <-> ( 1st ` Q ) = ( 0g ` ( DChr ` N ) ) )' % (CXQ, ZL.PRN))
    x0 = cp([cp([], 'simpr', '%s = %s' % (CXQ, ZL.PRN)), pr], 'mpbid', '( 1st ` Q ) = ( 0g ` ( DChr ` N ) )')
    BODYX = '( x = ( 0g ` ( DChr ` N ) ) -> A. z e. G %s <_ ( abs ` ( Im ` z ) ) )' % LAMG
    hx, newx = ral_at(w, Ap, lift(w, hgood, Ap), 'x', '( 1st ` Q )', BODYX, lift(w, q1, Ap))
    hz_ = cp([x0, hx], 'mpd', 'A. z e. G %s <_ ( abs ` ( Im ` z ) )' % LAMG)
    hA, _ = ral_at(w, Ap, hz_, 'z', 'A', '%s <_ ( abs ` ( Im ` z ) )' % LAMG, lift(w, fa['g'], Ap))
    hg = w.s([hA], 'ex', '( %s -> ( %s = %s -> %s <_ %s ) )' % (A0, CXQ, ZL.PRN, LAMG, AI))
    Q = top_and(DA[0])
    ant = c([c([c([hz, nx], 'jca', '( %s /\\ %s )' % (tsub(Z6.HZD3, SUB), tsub(ZL.NX, SUB))),
                c([c([c([srng, an1], 'jca', '( %s /\\ A =/= 1 )' % tsub(Z6.SRNG, SUB)), hdn], 'jca', '( ( %s /\\ A =/= 1 ) /\\ %s )' % (tsub(Z6.SRNG, SUB), tsub(Z6.HDN, SUB))),
                   c([t1, aez], 'jca', '( %s /\\ ( %s ` A ) = 0 )' % (tsub(Z6.T1, SUB), EX('( 1st ` Q )')))], 'jca',
                  '( ( ( %s /\\ A =/= 1 ) /\\ %s ) /\\ ( %s /\\ ( %s ` A ) = 0 ) )' % (tsub(Z6.SRNG, SUB), tsub(Z6.HDN, SUB), tsub(Z6.T1, SUB), EX('( 1st ` Q )')))], 'jca', Q[0]),
             c([trng, hg], 'jca', Q[1])], 'jca', DA[0])
    fin = c([ant, w.inst('zrdet')], 'syl', DA[1])
    w.qed([fin], 'idi', S['zrdetg'])
    return run8(w)


GENS['zrdetg'] = gen_detg
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
