"""Sortie EF3: the window integral (ef3win: Lean edge_interval_bound) and the left edge (ef3left: left_edge_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
from c10_f import crfacts
import lin
lin.FASTPATH = True
import ef3_a, ef3_c, ef3_e, ef3_f, ef3_g
from ef3_g import PWM, PWT, BQ, GU, LXV, ZU

W0 = 'W'
VC = '( W + ( 1 / 4 ) )'
WHI = '( W + ( 1 / 2 ) )'
WW = '( W (,) %s )' % WHI
WC = '( W [,] %s )' % WHI
LL = '( abs ` ( %s ` ( S + ( _i x. l ) ) ) )' % LDI()
IG = 'S. %s ( 1 / ( 1 + ( abs ` l ) ) ) _d l' % WW
SWQ = 'sum_ q e. %s ( %s x. %s )' % (ZS('F', VC), WQ(), RS('S'))
SLH_ = '( S e. RR /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S <_ ( 5 / 8 ) ) )'
S['ef3win'] = ('( ( ( %s /\\ Y e. RR+ ) /\\ ( %s /\\ W e. RR ) /\\ ( A. x e. %s ( F ` ( S + ( _i x. x ) ) ) =/= 0 /\\ A. p e. %s ( Re ` p ) =/= S ) ) -> '
               '( ( l e. %s |-> %s ) e. L^1 /\\ S. %s %s _d l <_ ( ( Y ^c S ) x. ( ( ( %s x. ( log ` %s ) ) x. %s ) + ( ; ; 1 3 5 x. %s ) ) ) ) )') % (
    DD(), SLH_, WC, ZS('F', VC), WW, LL, WW, LL, KLD, XA(VC), IG, SWQ)


def gen_win():
    from ef3_d import ld0_in
    w = W('ef3win', 'Lean ` edge_interval_bound ` : over a half-unit window of the left edge, ` integral abs ( ( F \' / F ) Y ^ z / z ) <_ Y ^ S ( 70000000 log X integral 1 / ( 1 + abs l ) + 135 sum w_q abs ( S - Re q ) ^ ( -1/2 ) ` ( ~ ef3pw and ~ ef1ir with ` D = 15 / 8 ` ).')
    A0, G = ante_of(S['ef3win'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    dd, yp = conj_split(w, A0, s([], 'simp1', H1))
    slh, wr = conj_split(w, A0, s([], 'simp2', H2))
    sr, sbb = conj_split(w, A0, slh); s9, s58 = conj_split(w, A0, sbb)
    alx, alp = conj_split(w, A0, s([], 'simp3', H3))
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    whr = s([wr, numst(w, A0, '( 1 / 2 )', 'RR')], 'readdcld', '%s e. RR' % WHI)
    vcr = s([wr, numst(w, A0, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % VC)
    lv0 = {'W': wr, 'S': sr}
    # the window lies in LD0
    Ay = '( %s /\\ y e. %s )' % (A0, WC)
    sy = St(w, Ay)
    Ly = lambda x: lift(w, x, Ay)
    yin = sy([], 'simpr', 'y e. %s' % WC)
    yr = sy([sy([Ly(wr), Ly(whr)], 'iccssred', '%s C_ RR' % WC), yin], 'sseldd', 'y e. RR')
    eqy, _ = w.wcongr('( F ` ( S + ( _i x. x ) ) ) =/= 0', {'x': 'y'}, 'x = y', {'x': w.s([], 'id', '( x = y -> x = y )')})
    fy = sy([eqy, Ly(alx), yin], 'rspcdva', '( F ` ( S + ( _i x. y ) ) ) =/= 0')
    cy = crfacts(w, Ay, 'S', 'y', Ly(sr), yr)
    rpy = sy([lin8(w, Ay, [Ly(s9)], '0 < S', {'S': Ly(sr)}), cy[1]], 'breqtrrd', '0 < ( Re ` ( S + ( _i x. y ) ) )')
    ldy = ld0_in(w, Ay, '( S + ( _i x. y ) )', cy[0], rpy, fy)
    BY = '( S + ( _i x. y ) ) e. %s' % LD0
    eqx, _ = w.wcongr(BY, {'y': 'x'}, 'y = x', {'y': w.s([], 'id', '( y = x -> y = x )')})
    alld = s([s([ldy], 'ralrimiva', 'A. y e. %s %s' % (WC, BY)), w.s([eqx], 'cbvralvw', '( A. y e. %s %s <-> A. x e. %s ( S + ( _i x. x ) ) e. %s )' % (WC, BY, WC, LD0))], 'sylib', 'A. x e. %s ( S + ( _i x. x ) ) e. %s' % (WC, LD0))
    ldc = s([s([hol, yp], 'jca', '( %s /\\ Y e. RR+ )' % HOLF('F', HP0)), w.inst('ef3ldc')], 'syl', '%s e. ( %s -cn-> CC )' % (LDI(), LD0))
    VLA = tsub(ante_of(S['ef3vle'])[0], {'G': LDI(), 'D': LD0, 'P': 'W', 'Q': WHI})
    va1, va2, va3 = top_and(VLA)
    vle = s([s([s([ldc, sr], 'jca', va1), s([s([wr, whr], 'jca', '( W e. RR /\\ %s e. RR )' % WHI), lin8(w, A0, [], 'W < %s' % WHI, lv0)], 'jca', va2), alld], '3jca', VLA), w.inst('ef3vle')], 'syl',
            tsub(ante_of(S['ef3vle'])[1], {'G': LDI(), 'D': LD0, 'P': 'W', 'Q': WHI}))
    ibL = conj_split(w, A0, vle)[0]
    ZV = ZS('F', VC)
    zs = s([s([dd, vcr], 'jca', '( %s /\\ %s e. RR )' % (DD(), VC)), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': VC}))
    zf, zo, _ = conj_split(w, A0, zs)
    # constants
    KL = '( %s x. ( log ` %s ) )' % (KLD, XA(VC))
    xr_ = s([ar, s([s([s([vcr], 'recnd', '%s e. CC' % VC)], 'abscld', '( abs ` %s ) e. RR' % VC), numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % VC)], 'remulcld', '%s e. RR' % XA(VC))
    x2 = s([s([dd, vcr], 'jca', '( %s /\\ %s e. RR )' % (DD(), VC)), w.inst('ef2x2')], 'syl', '2 <_ %s' % XA(VC))
    lxr = s([s([xr_, lin8(w, A0, [x2], '0 < %s' % XA(VC), {XA(VC): xr_})], 'elrpd', '%s e. RR+' % XA(VC))], 'relogcld', '( log ` %s ) e. RR' % XA(VC))
    klr = s([numst(w, A0, KLD, 'RR'), lxr], 'remulcld', '%s e. RR' % KL)
    YS = '( Y ^c S )'
    ysp = s([yp, sr], 'rpcxpcld', '%s e. RR+' % YS)
    ysr = s([ysp], 'rpred', '%s e. RR' % YS)
    # per-zero constants ( context Aq )
    Aq = '( %s /\\ q e. %s )' % (A0, ZV)
    sq = St(w, Aq)
    Lq = lambda x: lift(w, x, Aq)
    qin = sq([], 'simpr', 'q e. %s' % ZV)
    z = zs_unpack(w, Aq, 'F', VC, Lq(vcr), 'q', qin)
    on = sq([Lq(zo), qin, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
    mr = sq([on], 'nnred', '( F holord q ) e. RR')
    reb = sq([sq([Lq(vcr), qin], 'jca', '( %s e. RR /\\ q e. %s )' % (VC, ZV)), w.inst('ef2reb')], 'syl', tsub(ante_of(stmt('ef2reb'))[1], {'P': 'q', 'T': VC}))
    rlo, rhi, imb = conj_split(w, Aq, reb)
    qre = sq([z['cc']], 'recld', '( Re ` q ) e. RR'); qim = sq([z['cc']], 'imcld', '( Im ` q ) e. RR')
    aim = sq([sq([qim], 'recnd', '( Im ` q ) e. CC')], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
    a = '( 1 + ( abs ` ( Im ` q ) ) )'
    ap = sq([sq([numst(w, Aq, '1', 'RR'), aim], 'readdcld', '%s e. RR' % a), lin8(w, Aq, [sq([sq([qim], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '0 < %s' % a, {'( abs ` ( Im ` q ) )': aim})], 'elrpd', '%s e. RR+' % a)
    wqr = sq([mr, ap], 'rerpdivcld', '%s e. RR' % WQ())
    m0 = lin8(w, Aq, [sq([on], 'nnge1d', '1 <_ ( F holord q )')], '0 <_ ( F holord q )', {'( F holord q )': mr})
    wq0 = sq([mr, ap, m0], 'divge0d', '0 <_ %s' % WQ())
    eqp = w.s([w.s([], 'fveq2', '( p = q -> ( Re ` p ) = ( Re ` q ) )')], 'neeq1d', '( p = q -> ( ( Re ` p ) =/= S <-> ( Re ` q ) =/= S ) )')
    rne = sq([eqp, Lq(alp), qin], 'rspcdva', '( Re ` q ) =/= S')
    dq = '( abs ` ( S - ( Re ` q ) ) )'
    sqc = sq([sq([Lq(sr)], 'recnd', 'S e. CC'), sq([qre], 'recnd', '( Re ` q ) e. CC')], 'subcld', '( S - ( Re ` q ) ) e. CC')
    dqp = sq([sqc, sq([sq([Lq(sr)], 'recnd', 'S e. CC'), sq([qre], 'recnd', '( Re ` q ) e. CC'), sq([rne], 'necomd', 'S =/= ( Re ` q )')], 'subne0d', '( S - ( Re ` q ) ) =/= 0')], 'absrpcld', '%s e. RR+' % dq)
    dqr = sq([dqp], 'rpred', '%s e. RR' % dq)
    rsr = sq([sq([dqp, sq([numst(w, Aq, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % RS('S'))], 'rpred', '%s e. RR' % RS('S'))
    rs0 = sq([sq([dqp, sq([numst(w, Aq, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % RS('S'))], 'rpge0d', '0 <_ %s' % RS('S'))
    # d <_ 49 / 16
    srq = sq([Lq(sr), qre], 'resubcld', '( S - ( Re ` q ) ) e. RR')
    lvd = {'S': Lq(sr), '( Re ` q )': qre}
    d49 = sq([sq([lin8(w, Aq, [rlo, Lq(s58)], '-u ( ; 4 9 / ; 1 6 ) <_ ( S - ( Re ` q ) )', lvd) if False else lin8(w, Aq, [rhi, Lq(s9)], '-u ( ; 4 9 / ; 1 6 ) <_ ( S - ( Re ` q ) )', lvd),
                   lin8(w, Aq, [rlo, Lq(s58)], '( S - ( Re ` q ) ) <_ ( ; 4 9 / ; 1 6 )', lvd)], 'jca', '( -u ( ; 4 9 / ; 1 6 ) <_ ( S - ( Re ` q ) ) /\\ ( S - ( Re ` q ) ) <_ ( ; 4 9 / ; 1 6 ) )'),
              sq([srq, numst(w, Aq, '( ; 4 9 / ; 1 6 )', 'RR')], 'absled', '( %s <_ ( ; 4 9 / ; 1 6 ) <-> ( -u ( ; 4 9 / ; 1 6 ) <_ ( S - ( Re ` q ) ) /\\ ( S - ( Re ` q ) ) <_ ( ; 4 9 / ; 1 6 ) ) )' % dq)], 'mpbird', '%s <_ ( ; 4 9 / ; 1 6 )' % dq)
    # ef1ir on the window
    IRS = {'B': '( Im ` q )', 'E': dq, 'P': 'W', 'Q': WHI, 'D': '( ; 1 5 / 8 )', 't': 'l'}
    IRA = tsub(ante_of(stmt('ef1ir'))[0], IRS)
    IRC = tsub(ante_of(stmt('ef1ir'))[1], IRS)
    i1, i2 = top_and(IRA)
    i2a, i2b = top_and(i2)
    imv = sq([qim, Lq(vcr)], 'resubcld', '( ( Im ` q ) - %s ) e. RR' % VC)
    ib1 = sq([imb, sq([imv, numst(w, Aq, '( ; 1 3 / 8 )', 'RR')], 'absled', '( ( abs ` ( ( Im ` q ) - %s ) ) <_ ( ; 1 3 / 8 ) <-> ( -u ( ; 1 3 / 8 ) <_ ( ( Im ` q ) - %s ) /\\ ( ( Im ` q ) - %s ) <_ ( ; 1 3 / 8 ) ) )' % (VC, VC, VC))], 'mpbid',
             '( -u ( ; 1 3 / 8 ) <_ ( ( Im ` q ) - %s ) /\\ ( ( Im ` q ) - %s ) <_ ( ; 1 3 / 8 ) )' % (VC, VC))
    ib1a, ib1b = conj_split(w, Aq, ib1)
    lvi = {'( Im ` q )': qim, 'W': Lq(wr)}
    ira = sq([sq([qim, dqp], 'jca', i1), sq([sq([Lq(wr), Lq(whr), lin8(w, Aq, [], 'W <_ %s' % WHI, lvi)], '3jca', i2a),
                                              sq([numst(w, Aq, '( ; 1 5 / 8 )', 'RR'), lin8(w, Aq, [ib1a], '( %s - ( Im ` q ) ) <_ ( ; 1 5 / 8 )' % WHI, lvi), lin8(w, Aq, [ib1b], '( ( Im ` q ) - W ) <_ ( ; 1 5 / 8 )', lvi)], '3jca', i2b)], 'jca', i2)], 'jca', IRA)
    ir = sq([ira, w.inst('ef1ir')], 'syl', IRC)
    ibB, ileB = conj_split(w, Aq, ir)
    # ( 15/8 + d ) ^c ( 1 / 2 ) <_ 9 / 4
    DE = '( ( ; 1 5 / 8 ) + %s )' % dq
    der = sq([numst(w, Aq, '( ; 1 5 / 8 )', 'RR'), dqr], 'readdcld', '%s e. RR' % DE)
    c2 = sq([sq([sq([der, lin8(w, Aq, [sq([dqp], 'rpge0d', '0 <_ %s' % dq)], '0 <_ %s' % DE, {dq: dqr})], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (DE, DE)),
                  sq([numst(w, Aq, '( ; 8 1 / ; 1 6 )', 'RR'), numst(w, Aq, '( ; 8 1 / ; 1 6 )', 'ge0')], 'jca', '( ( ; 8 1 / ; 1 6 ) e. RR /\\ 0 <_ ( ; 8 1 / ; 1 6 ) )'), numst(w, Aq, '( 1 / 2 )', 'RR+')], '3jca',
                 '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( ( ; 8 1 / ; 1 6 ) e. RR /\\ 0 <_ ( ; 8 1 / ; 1 6 ) ) /\\ ( 1 / 2 ) e. RR+ )' % (DE, DE)), w.inst('cxple2')], 'syl',
             '( %s <_ ( ; 8 1 / ; 1 6 ) <-> ( %s ^c ( 1 / 2 ) ) <_ ( ( ; 8 1 / ; 1 6 ) ^c ( 1 / 2 ) ) )' % (DE, DE))
    c3 = sq([lin8(w, Aq, [d49], '%s <_ ( ; 8 1 / ; 1 6 )' % DE, {dq: dqr}), c2], 'mpbid', '( %s ^c ( 1 / 2 ) ) <_ ( ( ; 8 1 / ; 1 6 ) ^c ( 1 / 2 ) )' % DE)
    cl0 = Closure(w, 'T.', {}) if False else None
    s81 = w.s([w.s([w.s([], '9re' if False else 'id', 'x')], 'id', 'x')], 'id', 'x') if False else None
    e81 = sq([sq([numst(w, Aq, '( ; 8 1 / ; 1 6 )', 'CC'), w.inst('cxpsqrt')], 'syl', '( ( ; 8 1 / ; 1 6 ) ^c ( 1 / 2 ) ) = ( sqrt ` ( ; 8 1 / ; 1 6 ) )'),
              sq([sq([ringeq(w, Aq, '( ; 8 1 / ; 1 6 )', '( ( 9 / 4 ) x. ( 9 / 4 ) )', Closure(w, Aq, {})), sq([numst(w, Aq, '( 9 / 4 )', 'CC')], 'sqvald', '( ( 9 / 4 ) ^ 2 ) = ( ( 9 / 4 ) x. ( 9 / 4 ) )')], 'eqtr4d', '( ; 8 1 / ; 1 6 ) = ( ( 9 / 4 ) ^ 2 )')], 'fveq2d',
                 '( sqrt ` ( ; 8 1 / ; 1 6 ) ) = ( sqrt ` ( ( 9 / 4 ) ^ 2 ) )')], 'eqtrd', '( ( ; 8 1 / ; 1 6 ) ^c ( 1 / 2 ) ) = ( sqrt ` ( ( 9 / 4 ) ^ 2 ) )')
    e82 = sq([e81, sq([sq([numst(w, Aq, '( 9 / 4 )', 'RR'), numst(w, Aq, '( 9 / 4 )', 'ge0')], 'jca', '( ( 9 / 4 ) e. RR /\\ 0 <_ ( 9 / 4 ) )'), w.inst('sqrtsq')], 'syl', '( sqrt ` ( ( 9 / 4 ) ^ 2 ) ) = ( 9 / 4 )')], 'eqtrd', '( ( ; 8 1 / ; 1 6 ) ^c ( 1 / 2 ) ) = ( 9 / 4 )')
    c4 = sq([c3, e82], 'breqtrd', '( %s ^c ( 1 / 2 ) ) <_ ( 9 / 4 )' % DE)
    dhr = sq([sq([sq([der, lin8(w, Aq, [sq([dqp], 'rpgt0d', '0 < %s' % dq)], '0 < %s' % DE, {dq: dqr})], 'elrpd', '%s e. RR+' % DE), numst(w, Aq, '( 1 / 2 )', 'RR')], 'rpcxpcld', '( %s ^c ( 1 / 2 ) ) e. RR+' % DE)], 'rpred', '( %s ^c ( 1 / 2 ) ) e. RR' % DE)
    IB = 'S. %s %s _d l' % (WW, BQ('q', 'l'))
    ib9 = sq([sq([ileB, sq([sq([dhr, numst(w, Aq, '( 9 / 4 )', 'RR'), numst(w, Aq, '4', 'RR'), numst(w, Aq, '4', 'ge0'), c4], 'lemul2ad', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) <_ ( 4 x. ( 9 / 4 ) )' % DE),
                                     ringeq(w, Aq, '( 4 x. ( 9 / 4 ) )', '9', Closure(w, Aq, {}))], 'breqtrd', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) <_ 9' % DE)], 'id', 'x')], 'id', 'x') if False else None
    m9 = sq([sq([dhr, numst(w, Aq, '( 9 / 4 )', 'RR'), numst(w, Aq, '4', 'RR'), numst(w, Aq, '4', 'ge0'), c4], 'lemul2ad', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) <_ ( 4 x. ( 9 / 4 ) )' % DE), ringeq(w, Aq, '( 4 x. ( 9 / 4 ) )', '9', Closure(w, Aq, {}))], 'breqtrd', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) <_ 9' % DE)
    # pointwise ( context Aql )
    Aql = '( %s /\\ l e. %s )' % (Aq, WW)
    sl = St(w, Aql)
    Ll = lambda x: lift(w, x, Aql)
    lr = sl([sl([w.s([], 'ioossre', '%s C_ RR' % WW)], 'a1i', '%s C_ RR' % WW), sl([], 'simpr', 'l e. %s' % WW)], 'sseldd', 'l e. RR')
    lq = '( abs ` ( l - ( Im ` q ) ) )'
    lqr = sl([sl([sl([lr, Ll(qim)], 'resubcld', '( l - ( Im ` q ) ) e. RR')], 'recnd', '( l - ( Im ` q ) ) e. CC')], 'abscld', '%s e. RR' % lq)
    lq0 = sl([sl([sl([lr, Ll(qim)], 'resubcld', '( l - ( Im ` q ) ) e. RR')], 'recnd', '( l - ( Im ` q ) ) e. CC')], 'absge0d', '0 <_ %s' % lq)
    bb = sl([sl([sl([lqr, Ll(dqr)], 'readdcld', '( %s + %s ) e. RR' % (lq, dq)), lin8(w, Aql, [lq0, Ll(sq([dqp], 'rpgt0d', '0 < %s' % dq))], '0 < ( %s + %s )' % (lq, dq), {lq: lqr, dq: Ll(dqr)})], 'elrpd', '( %s + %s ) e. RR+' % (lq, dq)),
             sl([numst(w, Aql, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % BQ('q', 'l'))
    bqr = sl([bb], 'rpred', '%s e. RR' % BQ('q', 'l'))
    RB = '( %s x. %s )' % (RS('S'), BQ('q', 'l'))
    WRB = '( %s x. %s )' % (WQ(), RB)
    rbr = sl([Ll(rsr), bqr], 'remulcld', '%s e. RR' % RB)
    wrbr = sl([Ll(wqr), rbr], 'remulcld', '%s e. RR' % WRB)
    ptr = sl([numst(w, Aql, '; 1 5', 'RR'), wrbr], 'remulcld', '%s e. RR' % PWT('q', 'l'))
    # integrability of the zero term ( context Aq )
    ib1 = sq([sq([rsr], 'recnd', '%s e. CC' % RS('S')), sl([bqr], 'recnd', '%s e. CC' % BQ('q', 'l')), ibB], 'iblmulc2', '( l e. %s |-> %s ) e. L^1' % (WW, RB))
    ib2 = sq([sq([wqr], 'recnd', '%s e. CC' % WQ()), sl([rbr], 'recnd', '%s e. CC' % RB), ib1], 'iblmulc2', '( l e. %s |-> %s ) e. L^1' % (WW, WRB))
    ib3 = sq([numst(w, Aq, '; 1 5', 'CC'), sl([wrbr], 'recnd', '%s e. CC' % WRB), ib2], 'iblmulc2', '( l e. %s |-> %s ) e. L^1' % (WW, PWT('q', 'l')))
    it1 = sq([sq([rsr], 'recnd', '%s e. CC' % RS('S')), sl([bqr], 'recnd', '%s e. CC' % BQ('q', 'l')), ibB], 'itgmulc2', '( %s x. %s ) = S. %s %s _d l' % (RS('S'), IB, WW, RB))
    it2 = sq([sq([wqr], 'recnd', '%s e. CC' % WQ()), sl([rbr], 'recnd', '%s e. CC' % RB), ib1], 'itgmulc2', '( %s x. S. %s %s _d l ) = S. %s %s _d l' % (WQ(), WW, RB, WW, WRB))
    it3 = sq([numst(w, Aq, '; 1 5', 'CC'), sl([wrbr], 'recnd', '%s e. CC' % WRB), ib2], 'itgmulc2', '( ; 1 5 x. S. %s %s _d l ) = S. %s %s _d l' % (WW, WRB, WW, PWT('q', 'l')))
    IT = 'S. %s %s _d l' % (WW, PWT('q', 'l'))
    ite = sq([sq([sq([sq([it1], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. S. %s %s _d l )' % (WQ(), RS('S'), IB, WQ(), WW, RB)), it2], 'eqtrd', '( %s x. ( %s x. %s ) ) = S. %s %s _d l' % (WQ(), RS('S'), IB, WW, WRB))], 'oveq2d',
                  '( ; 1 5 x. ( %s x. ( %s x. %s ) ) ) = ( ; 1 5 x. S. %s %s _d l )' % (WQ(), RS('S'), IB, WW, WRB)), it3], 'eqtrd', '( ; 1 5 x. ( %s x. ( %s x. %s ) ) ) = %s' % (WQ(), RS('S'), IB, IT))
    ibr = sq([bqr, ibB], 'itgrecl', '%s e. RR' % IB)
    b9 = sq([ibr, sq([numst(w, Aq, '4', 'RR'), dhr], 'remulcld', '( 4 x. ( %s ^c ( 1 / 2 ) ) ) e. RR' % DE), numst(w, Aq, '9', 'RR'), ileB, m9], 'letrd', '%s <_ 9' % IB)
    wr0 = sq([wqr, rsr, wq0, rs0], 'mulge0d', '0 <_ ( %s x. %s )' % (WQ(), RS('S')))
    clq = Closure(w, Aq, {WQ(): ('RR', wqr), RS('S'): ('RR', rsr)})
    for k in (WQ(), RS('S')):
        clq.atom(k)
    WR = '( %s x. %s )' % (WQ(), RS('S'))
    wqc = sq([wqr], 'recnd', '%s e. CC' % WQ()); rsc = sq([rsr], 'recnd', '%s e. CC' % RS('S')); ibc = sq([ibr], 'recnd', '%s e. CC' % IB)
    ma1 = sq([wqc, rsc, ibc], 'mulassd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (WR, IB, WQ(), RS('S'), IB))
    ma2 = sq([numst(w, Aq, '; 1 5', 'CC'), sq([wqc, rsc], 'mulcld', '%s e. CC' % WR), ibc], 'mulassd', '( ( ; 1 5 x. %s ) x. %s ) = ( ; 1 5 x. ( %s x. %s ) )' % (WR, IB, WR, IB))
    r1 = sq([sq([sq([ma1], 'oveq2d', '( ; 1 5 x. ( %s x. %s ) ) = ( ; 1 5 x. ( %s x. ( %s x. %s ) ) )' % (WR, IB, WQ(), RS('S'), IB)), ma2], 'eqtr2d' if False else 'id', 'x')], 'id', 'x') if False else \
        sq([sq([ma2, sq([ma1], 'oveq2d', '( ; 1 5 x. ( %s x. %s ) ) = ( ; 1 5 x. ( %s x. ( %s x. %s ) ) )' % (WR, IB, WQ(), RS('S'), IB))], 'eqtrd', '( ( ; 1 5 x. %s ) x. %s ) = ( ; 1 5 x. ( %s x. ( %s x. %s ) ) )' % (WR, IB, WQ(), RS('S'), IB))], 'eqcomd',
           '( ; 1 5 x. ( %s x. ( %s x. %s ) ) ) = ( ( ; 1 5 x. %s ) x. %s )' % (WQ(), RS('S'), IB, WR, IB))
    wr15 = sq([numst(w, Aq, '; 1 5', 'RR'), sq([wqr, rsr], 'remulcld', '%s e. RR' % WR)], 'remulcld', '( ; 1 5 x. %s ) e. RR' % WR)
    le9 = sq([ibr, numst(w, Aq, '9', 'RR'), wr15, sq([numst(w, Aq, '; 1 5', 'RR'), sq([wqr, rsr], 'remulcld', '%s e. RR' % WR), numst(w, Aq, '; 1 5', 'ge0'), wr0], 'mulge0d', '0 <_ ( ; 1 5 x. %s )' % WR), b9], 'lemul2ad',
             '( ( ; 1 5 x. %s ) x. %s ) <_ ( ( ; 1 5 x. %s ) x. 9 )' % (WR, IB, WR))
    r2 = ringeq(w, Aq, '( ( ; 1 5 x. %s ) x. 9 )' % WR, '( ; ; 1 3 5 x. %s )' % WR, clq)
    tq = sq([sq([ite, r1], 'eqtr3d', '%s = ( ( ; 1 5 x. %s ) x. %s )' % (IT, WR, IB)), sq([le9, r2], 'breqtrd', '( ( ; 1 5 x. %s ) x. %s ) <_ ( ; ; 1 3 5 x. %s )' % (WR, IB, WR))], 'eqbrtrd', '%s <_ ( ; ; 1 3 5 x. %s )' % (IT, WR))
    itr = sq([ptr, ib3], 'itgrecl', '%s e. RR' % IT)
    # sums over the zeros ( context A0 )
    wsv = s([w.s([], 'ioombl', '%s e. dom vol' % WW)], 'a1i', '%s e. dom vol' % WW)
    ptc_x = w.s([w.s([sl([ptr], 'recnd', '%s e. CC' % PWT('q', 'l'))], 'anasss', '( ( %s /\\ ( q e. %s /\\ l e. %s ) ) -> %s e. CC )' % (A0, ZV, WW, PWT('q', 'l')))], 'ancom2s',
                '( ( %s /\\ ( l e. %s /\\ q e. %s ) ) -> %s e. CC )' % (A0, WW, ZV, PWT('q', 'l')))
    SP = 'sum_ q e. %s %s' % (ZV, PWT('q', 'l'))
    fs = s([wsv, zf, ptc_x, ib3], 'itgfsum', '( ( l e. %s |-> %s ) e. L^1 /\\ S. %s %s _d l = sum_ q e. %s %s )' % (WW, SP, WW, SP, ZV, IT))
    ibS, itS = conj_split(w, A0, fs)
    SIT = 'sum_ q e. %s %s' % (ZV, IT)
    swr = s([zf, sq([wqr, rsr], 'remulcld', '%s e. RR' % WR)], 'fsumrecl', '%s e. RR' % SWQ)
    sb1 = s([zf, itr, sq([numst(w, Aq, '; ; 1 3 5', 'RR'), sq([wqr, rsr], 'remulcld', '%s e. RR' % WR)], 'remulcld', '( ; ; 1 3 5 x. %s ) e. RR' % WR), tq], 'fsumle', '%s <_ sum_ q e. %s ( ; ; 1 3 5 x. %s )' % (SIT, ZV, WR))
    sb2 = s([zf, numst(w, A0, '; ; 1 3 5', 'CC'), sq([sq([wqr, rsr], 'remulcld', '%s e. RR' % WR)], 'recnd', '%s e. CC' % WR)], 'fsummulc2', '( ; ; 1 3 5 x. %s ) = sum_ q e. %s ( ; ; 1 3 5 x. %s )' % (SWQ, ZV, WR))
    sb3 = s([sb1, sb2], 'breqtrrd', '%s <_ ( ; ; 1 3 5 x. %s )' % (SIT, SWQ))
    # the Landau term ( context Al )
    Al = '( %s /\\ l e. %s )' % (A0, WW)
    sa = St(w, Al)
    La = lambda x: lift(w, x, Al)
    lr0 = sa([sa([w.s([], 'ioossre', '%s C_ RR' % WW)], 'a1i', '%s C_ RR' % WW), sa([], 'simpr', 'l e. %s' % WW)], 'sseldd', 'l e. RR')
    alr = sa([sa([lr0], 'recnd', 'l e. CC')], 'abscld', '( abs ` l ) e. RR')
    gp = sa([sa([sa([numst(w, Al, '1', 'RR'), alr], 'readdcld', '( 1 + ( abs ` l ) ) e. RR'), lin8(w, Al, [sa([sa([lr0], 'recnd', 'l e. CC')], 'absge0d', '0 <_ ( abs ` l )')], '0 < ( 1 + ( abs ` l ) )', {'( abs ` l )': alr})], 'elrpd', '( 1 + ( abs ` l ) ) e. RR+')], 'rpreccld', '%s e. RR+' % GU('l'))
    gr = sa([gp], 'rpred', '%s e. RR' % GU('l'))
    ibg = s([wr, whr, w.inst('ef1iac') if False else None], 'id', 'x') if False else s([wr, whr, w.inst('ef1iac')], 'syl2anc', '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) e. L^1' % WW)
    cbg = w.s([w.s([w.s([w.s([], 'fveq2', '( t = l -> ( abs ` t ) = ( abs ` l ) )')], 'oveq2d', '( t = l -> ( 1 + ( abs ` t ) ) = ( 1 + ( abs ` l ) ) )')], 'oveq2d', '( t = l -> ( 1 / ( 1 + ( abs ` t ) ) ) = %s )' % GU('l'))], 'cbvmptv',
              '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) = ( l e. %s |-> %s )' % (WW, WW, GU('l')))
    ibg2 = s([s([cbg], 'a1i', '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) = ( l e. %s |-> %s )' % (WW, WW, GU('l'))), ibg], 'eqeltrrd' if False else 'id', 'x') if False else s([s([cbg], 'a1i', '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) = ( l e. %s |-> %s )' % (WW, WW, GU('l'))), ibg], 'eqeltrrd', '( l e. %s |-> %s ) e. L^1' % (WW, GU('l')))
    KG = '( %s x. %s )' % (KL, GU('l'))
    ibK = s([s([klr], 'recnd', '%s e. CC' % KL), sa([gr], 'recnd', '%s e. CC' % GU('l')), ibg2], 'iblmulc2', '( l e. %s |-> %s ) e. L^1' % (WW, KG))
    itK = s([s([klr], 'recnd', '%s e. CC' % KL), sa([gr], 'recnd', '%s e. CC' % GU('l')), ibg2], 'itgmulc2', '( %s x. %s ) = S. %s %s _d l' % (KL, IG, WW, KG))
    kgr = sa([La(klr), gr], 'remulcld', '%s e. RR' % KG)
    Alq = '( %s /\\ q e. %s )' % (Al, ZV)
    ptr_a = w.s([ptr], 'an32s', '( ( %s /\\ q e. %s ) -> %s e. RR )' % (Al, ZV, PWT('q', 'l')))
    spr = sa([La(zf), ptr_a], 'fsumrecl', '%s e. RR' % SP)
    INN = '( %s + %s )' % (KG, SP)
    ibI = s([sa([kgr], 'recnd', '%s e. CC' % KG), ibK, sa([spr], 'recnd', '%s e. CC' % SP), ibS], 'ibladd', '( l e. %s |-> %s ) e. L^1' % (WW, INN))
    itI = s([sa([kgr], 'recnd', '%s e. CC' % KG), ibK, sa([spr], 'recnd', '%s e. CC' % SP), ibS], 'itgadd', 'S. %s %s _d l = ( S. %s %s _d l + S. %s %s _d l )' % (WW, INN, WW, KG, WW, SP))
    PMl = '( %s x. %s )' % (YS, INN)
    innr = sa([kgr, spr], 'readdcld', '%s e. RR' % INN)
    ibP = s([s([ysr], 'recnd', '%s e. CC' % YS), sa([innr], 'recnd', '%s e. CC' % INN), ibI], 'iblmulc2', '( l e. %s |-> %s ) e. L^1' % (WW, PMl))
    itP = s([s([ysr], 'recnd', '%s e. CC' % YS), sa([innr], 'recnd', '%s e. CC' % INN), ibI], 'itgmulc2', '( %s x. S. %s %s _d l ) = S. %s %s _d l' % (YS, WW, INN, WW, PMl))
    # pointwise bound by ef3pw
    lin_ = sa([sa([w.s([], 'ioossicc', '%s C_ %s' % (WW, WC))], 'a1i', '%s C_ %s' % (WW, WC)), sa([], 'simpr', 'l e. %s' % WW)], 'sseldd', 'l e. %s' % WC)
    eqxl, _ = w.wcongr('( F ` ( S + ( _i x. x ) ) ) =/= 0', {'x': 'l'}, 'x = l', {'x': w.s([], 'id', '( x = l -> x = l )')})
    fl = sa([eqxl, La(alx), lin_], 'rspcdva', '( F ` ( S + ( _i x. l ) ) ) =/= 0')
    lb = sa([sa([], 'simpr', 'l e. %s' % WW), w.inst('eliooord')], 'syl', '( W < l /\\ l < %s )' % WHI)
    lb1, lb2 = conj_split(w, Al, lb)
    lvc = sa([lr0, La(vcr)], 'resubcld', '( l - %s ) e. RR' % VC)
    lvl = {'l': lr0, 'W': La(wr)}
    ab4 = sa([sa([lin8(w, Al, [lb1], '-u ( 1 / 4 ) <_ ( l - %s )' % VC, lvl), lin8(w, Al, [lb2], '( l - %s ) <_ ( 1 / 4 )' % VC, lvl)], 'jca', '( -u ( 1 / 4 ) <_ ( l - %s ) /\\ ( l - %s ) <_ ( 1 / 4 ) )' % (VC, VC)),
              sa([lvc, numst(w, Al, '( 1 / 4 )', 'RR')], 'absled', '( ( abs ` ( l - %s ) ) <_ ( 1 / 4 ) <-> ( -u ( 1 / 4 ) <_ ( l - %s ) /\\ ( l - %s ) <_ ( 1 / 4 ) ) )' % (VC, VC, VC))], 'mpbird', '( abs ` ( l - %s ) ) <_ ( 1 / 4 )' % VC)
    PWA = tsub(ante_of(S['ef3pw'])[0], {'U': 'l', 'V': VC})
    pa1, pa2, pa3 = top_and(PWA)
    pwa = sa([sa([La(dd), La(yp)], 'jca', pa1), sa([La(slh), sa([La(vcr), lr0], 'jca', '( %s e. RR /\\ l e. RR )' % VC)], 'jca', pa2), sa([ab4, fl, La(alp)], '3jca', pa3)], '3jca', PWA)
    pw = sa([pwa, w.inst('ef3pw')], 'syl', tsub(ante_of(S['ef3pw'])[1], {'U': 'l', 'V': VC}))
    llr = sa([sa([lift(w, s([s([], 'id', 'x')], 'id', 'x'), Al) if False else sa([La(ldc), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LDI(), LD0)),
                   inst_all_l(w, Al, La(alld), lin_)], 'ffvelcdmd', '( %s ` ( S + ( _i x. l ) ) ) e. CC' % LDI())], 'abscld', '%s e. RR' % LL)
    pmr = sa([La(ysr), innr], 'remulcld', '%s e. RR' % PMl)
    ile = s([ibL, ibP, llr, pmr, pw], 'itgle', 'S. %s %s _d l <_ S. %s %s _d l' % (WW, LL, WW, PMl))
    # value of the majorant integral
    IK = 'S. %s %s _d l' % (WW, KG)
    ISP = 'S. %s %s _d l' % (WW, SP)
    igr = s([gr, ibg2], 'itgrecl', '%s e. RR' % IG)
    v1 = s([s([itP], 'eqcomd', 'S. %s %s _d l = ( %s x. S. %s %s _d l )' % (WW, PMl, YS, WW, INN)), s([s([itI, s([s([itK], 'eqcomd', '%s = ( %s x. %s )' % (IK, KL, IG)), itS], 'oveq12d', '( %s + %s ) = ( ( %s x. %s ) + %s )' % (IK, ISP, KL, IG, SIT))], 'eqtrd',
                                                                                                         'S. %s %s _d l = ( ( %s x. %s ) + %s )' % (WW, INN, KL, IG, SIT))], 'oveq2d', '( %s x. S. %s %s _d l ) = ( %s x. ( ( %s x. %s ) + %s ) )' % (YS, WW, INN, YS, KL, IG, SIT))], 'eqtrd',
           'S. %s %s _d l = ( %s x. ( ( %s x. %s ) + %s ) )' % (WW, PMl, YS, KL, IG, SIT))
    sitr = s([zf, itr], 'fsumrecl', '%s e. RR' % SIT)
    klig = s([klr, igr], 'remulcld', '( %s x. %s ) e. RR' % (KL, IG))
    v2 = s([sb3, s([sitr, s([numst(w, A0, '; ; 1 3 5', 'RR'), swr], 'remulcld', '( ; ; 1 3 5 x. %s ) e. RR' % SWQ), klig], 'leadd2d', '( %s <_ ( ; ; 1 3 5 x. %s ) <-> ( ( %s x. %s ) + %s ) <_ ( ( %s x. %s ) + ( ; ; 1 3 5 x. %s ) ) )' % (SIT, SWQ, KL, IG, SIT, KL, IG, SWQ))], 'mpbid',
           '( ( %s x. %s ) + %s ) <_ ( ( %s x. %s ) + ( ; ; 1 3 5 x. %s ) )' % (KL, IG, SIT, KL, IG, SWQ))
    RH = '( ( %s x. %s ) + ( ; ; 1 3 5 x. %s ) )' % (KL, IG, SWQ)
    v3 = s([s([klig, sitr], 'readdcld', '( ( %s x. %s ) + %s ) e. RR' % (KL, IG, SIT)), s([klig, s([numst(w, A0, '; ; 1 3 5', 'RR'), swr], 'remulcld', '( ; ; 1 3 5 x. %s ) e. RR' % SWQ)], 'readdcld', '%s e. RR' % RH), ysr, s([ysp], 'rpge0d', '0 <_ %s' % YS), v2], 'lemul2ad',
           '( %s x. ( ( %s x. %s ) + %s ) ) <_ ( %s x. %s )' % (YS, KL, IG, SIT, YS, RH))
    fin = s([s([ile, v1], 'breqtrd', 'S. %s %s _d l <_ ( %s x. ( ( %s x. %s ) + %s ) )' % (WW, LL, YS, KL, IG, SIT)), v3], 'letrd' if False else 'id', 'x') if False else None
    ilr = s([llr, ibL], 'itgrecl', 'S. %s %s _d l e. RR' % (WW, LL))
    t1 = s([ile, v1], 'breqtrd', 'S. %s %s _d l <_ ( %s x. ( ( %s x. %s ) + %s ) )' % (WW, LL, YS, KL, IG, SIT))
    fin = s([ilr, s([ysr, s([klig, sitr], 'readdcld', '( ( %s x. %s ) + %s ) e. RR' % (KL, IG, SIT))], 'remulcld', '( %s x. ( ( %s x. %s ) + %s ) ) e. RR' % (YS, KL, IG, SIT)),
             s([ysr, s([klig, s([numst(w, A0, '; ; 1 3 5', 'RR'), swr], 'remulcld', '( ; ; 1 3 5 x. %s ) e. RR' % SWQ)], 'readdcld', '%s e. RR' % RH)], 'remulcld', '( %s x. %s ) e. RR' % (YS, RH)), t1, v3], 'letrd', 'S. %s %s _d l <_ ( %s x. %s )' % (WW, LL, YS, RH))
    w.qed([ibL, fin], 'jca', S['ef3win'])
    return run8(w)


def inst_all_l(w, A, al, lin_):
    eq, new = w.wcongr('( S + ( _i x. x ) ) e. %s' % LD0, {'x': 'l'}, 'x = l', {'x': w.s([], 'id', '( x = l -> x = l )')})
    return w.s([eq, al, lin_], 'rspcdva', '( %s -> ( S + ( _i x. l ) ) e. %s )' % (A, LD0))


TOP = '( P + ( M / 2 ) )'
NEio = 'A. i e. ( 0 ..^ M ) A. o e. %s ( Re ` o ) =/= S' % ZK('i')
PHIio = 'sum_ i e. ( 0 ..^ M ) sum_ o e. %s ( %s x. %s )' % (ZK('i'), WQ('o'), RS('S', 'o'))
HNZ = 'A. t e. ( P [,] %s ) ( F ` ( S + ( _i x. t ) ) ) =/= 0' % TOP
LCC = ante_of(S['ef3left'])[1]
S['ef3lcore'] = ('( ( ( %s /\\ ( Y e. RR /\\ 1 < Y ) /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s <_ ( %s x. ( %s ^ 2 ) ) /\\ ( Q e. RR /\\ P < Q /\\ Q <_ %s ) ) ) -> %s )') % (
    DD(), SGH, SLH_, NEio, HNZ, PHIio, KS, LT4, TOP, LCC)


def gen_lcore():
    from ef3_d import ld0_in
    from ef3_f import sgh_parts, lt4_facts, zk_t0r
    from ef3_a import icc_mem
    w = W('ef3lcore', 'Lean ` left_edge_le ` , with the hypotheses written with the letters ` i ` , ` o ` : the left-edge integral over ` [ P , Q ] ` , ` Q <_ P + M / 2 ` , is at most ` 500000000 Y ^ S log ^ 2 ( A ( T + 4 ) ) ` (windows ~ ef3win , ~ ef3adj , ~ ef1ial ).')
    A0, G = ante_of(S['ef3lcore'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    dd, yh, sgh = conj_split(w, A0, s([], 'simp1', H1))
    slh, neio = conj_split(w, A0, s([], 'simp2', H2))
    hnz, hph, qq = conj_split(w, A0, s([], 'simp3', H3))
    qr, pq, qtop = conj_split(w, A0, qq)
    sr, sbb = conj_split(w, A0, slh); s9, s58 = conj_split(w, A0, sbb)
    yr, y1 = conj_split(w, A0, yh)
    d = sgh_parts(w, A0, sgh)
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    f = lt4_facts(w, A0, ar, a1, d['tr'], d['t2'])
    lv0 = {'Y': yr, 'P': d['pr'], 'Q': qr, 'T': d['tr']}
    yp = s([yr, lin8(w, A0, [y1], '0 < Y', lv0)], 'elrpd', 'Y e. RR+')
    mr = s([d['mn']], 'nn0red', 'M e. RR')
    topr = s([d['pr'], s([mr, numst(w, A0, '2', 'RR+')], 'rerpdivcld', '( M / 2 ) e. RR')], 'readdcld', '%s e. RR' % TOP)
    lvt = {'P': d['pr'], 'Q': qr, TOP: topr}
    ldc = s([s([hol, yp], 'jca', '( %s /\\ Y e. RR+ )' % HOLF('F', HP0)), w.inst('ef3ldc')], 'syl', '%s e. ( %s -cn-> CC )' % (LDI(), LD0))
    # vertical segments in LD0 over [ P , B ] for B <_ TOP
    def seg_in(B, br, ble):
        I = '( P [,] %s )' % B
        Ay = '( %s /\\ y e. %s )' % (A0, I)
        sy = St(w, Ay)
        Ly = lambda x: lift(w, x, Ay)
        yin = sy([], 'simpr', 'y e. %s' % I)
        e = sy([Ly(d['pr']), Ly(br), w.inst('elicc2')], 'syl2anc', '( y e. %s <-> ( y e. RR /\\ P <_ y /\\ y <_ %s ) )' % (I, B))
        yy, y0, yb = conj_split(w, Ay, sy([yin, e], 'mpbid', '( y e. RR /\\ P <_ y /\\ y <_ %s )' % B))
        yt = icc_mem(w, Ay, 'y', 'P', TOP, yy, Ly(d['pr']), Ly(topr), y0, lin8(w, Ay, [yb, Ly(ble)], 'y <_ %s' % TOP, {'y': yy, B: Ly(br), TOP: Ly(topr)}))
        eqt, _ = w.wcongr('( F ` ( S + ( _i x. t ) ) ) =/= 0', {'t': 'y'}, 't = y', {'t': w.s([], 'id', '( t = y -> t = y )')})
        fy = sy([eqt, Ly(hnz), yt], 'rspcdva', '( F ` ( S + ( _i x. y ) ) ) =/= 0')
        cy = crfacts(w, Ay, 'S', 'y', Ly(sr), yy)
        rpy = sy([lin8(w, Ay, [Ly(s9)], '0 < S', {'S': Ly(sr)}), cy[1]], 'breqtrrd', '0 < ( Re ` ( S + ( _i x. y ) ) )')
        ldy = ld0_in(w, Ay, '( S + ( _i x. y ) )', cy[0], rpy, fy)
        BY = '( S + ( _i x. y ) ) e. %s' % LD0
        eqx, _ = w.wcongr(BY, {'y': 'x'}, 'y = x', {'y': w.s([], 'id', '( y = x -> y = x )')})
        return s([s([ldy], 'ralrimiva', 'A. y e. %s %s' % (I, BY)), w.s([eqx], 'cbvralvw', '( A. y e. %s %s <-> A. x e. %s ( S + ( _i x. x ) ) e. %s )' % (I, BY, I, LD0))], 'sylib', 'A. x e. %s ( S + ( _i x. x ) ) e. %s' % (I, LD0))
    def vle(B, br, ble, plb):
        VLA = tsub(ante_of(S['ef3vle'])[0], {'G': LDI(), 'D': LD0, 'P': 'P', 'Q': B})
        va1, va2, va3 = top_and(VLA)
        return s([s([s([ldc, sr], 'jca', va1), s([s([d['pr'], br], 'jca', '( P e. RR /\\ %s e. RR )' % B), plb], 'jca', va2), seg_in(B, br, ble)], '3jca', VLA), w.inst('ef3vle')], 'syl',
                 tsub(ante_of(S['ef3vle'])[1], {'G': LDI(), 'D': LD0, 'P': 'P', 'Q': B}))
    vQ = vle('Q', qr, qtop, pq)
    ptop = lin8(w, A0, [pq, qtop], 'P < %s' % TOP, lvt)
    vT = vle(TOP, topr, lin8(w, A0, [], '%s <_ %s' % (TOP, TOP), lvt), ptop)
    ibQ, bQ = conj_split(w, A0, vQ)
    ibT, _ = conj_split(w, A0, vT)
    IPT = '( P (,) %s )' % TOP
    # pointwise facts of LL on ( P , TOP )
    alT = seg_in(TOP, topr, lin8(w, A0, [], '%s <_ %s' % (TOP, TOP), lvt))
    def ll_facts(A, I_sub, ss_st):
        """under ( A /\\ l e. I_sub ) with ss_st : ( A -> I_sub C_ IPT ): LL e. RR, 0 <_ LL"""
        Al = '( %s /\\ l e. %s )' % (A, I_sub)
        sa = St(w, Al)
        lin_ = sa([lift(w, ss_st, Al), sa([], 'simpr', 'l e. %s' % I_sub)], 'sseldd', 'l e. %s' % IPT)
        lic = sa([sa([w.s([], 'ioossicc', '%s C_ ( P [,] %s )' % (IPT, TOP))], 'a1i', '%s C_ ( P [,] %s )' % (IPT, TOP)), lin_], 'sseldd', 'l e. ( P [,] %s )' % TOP)
        eq, _ = w.wcongr('( S + ( _i x. x ) ) e. %s' % LD0, {'x': 'l'}, 'x = l', {'x': w.s([], 'id', '( x = l -> x = l )')})
        ld = sa([eq, lift(w, alT, Al), lic], 'rspcdva', '( S + ( _i x. l ) ) e. %s' % LD0)
        vc = sa([sa([lift(w, ldc, Al), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LDI(), LD0)), ld], 'ffvelcdmd', '( %s ` ( S + ( _i x. l ) ) ) e. CC' % LDI())
        return sa([vc], 'abscld', '%s e. RR' % LL), sa([vc], 'absge0d', '0 <_ %s' % LL)
    sid = s([w.s([], 'ssid', '%s C_ %s' % (IPT, IPT))], 'a1i', '%s C_ %s' % (IPT, IPT))
    llT, ll0T = ll_facts(A0, IPT, sid)
    IQT = '( Q (,) %s )' % TOP
    sQT = s([s([s([s([d['pr']], 'rexrd', 'P e. RR*'), s([topr], 'rexrd', '%s e. RR*' % TOP)], 'jca', '( P e. RR* /\\ %s e. RR* )' % TOP), s([lin8(w, A0, [pq], 'P <_ Q', lvt), lin8(w, A0, [], '%s <_ %s' % (TOP, TOP), lvt)], 'jca', '( P <_ Q /\\ %s <_ %s )' % (TOP, TOP))], 'jca',
                '( ( P e. RR* /\\ %s e. RR* ) /\\ ( P <_ Q /\\ %s <_ %s ) )' % (TOP, TOP, TOP)), w.inst('ioossioo')], 'syl', '%s C_ %s' % (IQT, IPT))
    llQ, ll0Q = ll_facts(A0, IQT, sQT)
    ibQT = s([sQT, s([w.s([], 'ioombl', '%s e. dom vol' % IQT)], 'a1i', '%s e. dom vol' % IQT), St(w, '( %s /\\ l e. %s )' % (A0, IPT))([llT], 'recnd', '%s e. CC' % LL), ibT], 'iblss', '( l e. %s |-> %s ) e. L^1' % (IQT, LL))
    qin = icc_mem(w, A0, 'Q', 'P', TOP, qr, d['pr'], topr, lin8(w, A0, [pq], 'P <_ Q', lvt), qtop)
    ITT = 'S. %s %s _d l' % (IPT, LL); IQQ = 'S. ( P (,) Q ) %s _d l' % LL; IQ2 = 'S. %s %s _d l' % (IQT, LL)
    spl = s([d['pr'], topr, qin, St(w, '( %s /\\ l e. %s )' % (A0, IPT))([llT], 'recnd', '%s e. CC' % LL), ibQ, ibQT], 'itgsplitioo', '%s = ( %s + %s )' % (ITT, IQQ, IQ2))
    g0 = s([ibQT, llQ, ll0Q], 'itgge0', '0 <_ %s' % IQ2)
    iqr = s([conj_split(w, A0, vQ)[0] and ll_facts(A0, '( P (,) Q )', s([s([s([s([d['pr']], 'rexrd', 'P e. RR*'), s([topr], 'rexrd', '%s e. RR*' % TOP)], 'jca', '( P e. RR* /\\ %s e. RR* )' % TOP), s([lin8(w, A0, [], 'P <_ P', lvt), qtop], 'jca', '( P <_ P /\\ Q <_ %s )' % TOP)], 'jca',
                                                                                      '( ( P e. RR* /\\ %s e. RR* ) /\\ ( P <_ P /\\ Q <_ %s ) )' % (TOP, TOP)), w.inst('ioossioo')], 'syl', '( P (,) Q ) C_ %s' % IPT))[0], ibQ], 'itgrecl', '%s e. RR' % IQQ)
    iq2r = s([llQ, ibQT], 'itgrecl', '%s e. RR' % IQ2)
    le1 = s([s([g0, s([iqr, iq2r], 'addge01d', '( 0 <_ %s <-> %s <_ ( %s + %s ) )' % (IQ2, IQQ, IQQ, IQ2))], 'mpbid', '%s <_ ( %s + %s )' % (IQQ, IQQ, IQ2)), spl], 'breqtrrd', '%s <_ %s' % (IQQ, ITT))
    # windows
    HADJ_ = [tsub(h, {'ph': A0, 'B': LL}) for h in ('( ph -> P e. RR )', '( ph -> M e. NN0 )')]
    adj = s([d['pr'], d['mn'], St(w, '( %s /\\ l e. %s )' % (A0, IPT))([llT], 'recnd', '%s e. CC' % LL), ibT], 'ef3adj', 'S. %s %s _d l = sum_ j e. ( 0 ..^ M ) S. %s %s _d l' % (IPT, LL, WIN(), LL))
    Aj = '( %s /\\ j e. ( 0 ..^ M ) )' % A0
    sj = St(w, Aj)
    Lj = lambda x: lift(w, x, Aj)
    jin = sj([], 'simpr', 'j e. ( 0 ..^ M )')
    jn = sj([jin, w.inst('elfzonn0')], 'syl', 'j e. NN0')
    jr = sj([jn], 'nn0red', 'j e. RR')
    j1 = sj([sj([jin, w.inst('fzofzp1')], 'syl', '( j + 1 ) e. ( 0 ... M )'), w.inst('elfzle2')], 'syl', '( j + 1 ) <_ M')
    Wj = WLO()
    wjr = sj([Lj(d['pr']), sj([jr, numst(w, Aj, '2', 'RR+')], 'rerpdivcld', '( j / 2 ) e. RR')], 'readdcld', '%s e. RR' % Wj)
    wjh = sj([wjr, numst(w, Aj, '( 1 / 2 )', 'RR')], 'readdcld', '( %s + ( 1 / 2 ) ) e. RR' % Wj)
    lvj = {'j': jr, 'P': Lj(d['pr']), 'M': Lj(mr), 'T': Lj(d['tr'])}
    # F nonzero on the closed window
    WCj = '( %s [,] ( %s + ( 1 / 2 ) ) )' % (Wj, Wj)
    Ay = '( %s /\\ y e. %s )' % (Aj, WCj)
    sy = St(w, Ay)
    Ly = lambda x: lift(w, x, Ay)
    yin = sy([], 'simpr', 'y e. %s' % WCj)
    e = sy([Ly(wjr), Ly(wjh), w.inst('elicc2')], 'syl2anc', '( y e. %s <-> ( y e. RR /\\ %s <_ y /\\ y <_ ( %s + ( 1 / 2 ) ) ) )' % (WCj, Wj, Wj))
    yy, y0, yb = conj_split(w, Ay, sy([yin, e], 'mpbid', '( y e. RR /\\ %s <_ y /\\ y <_ ( %s + ( 1 / 2 ) ) )' % (Wj, Wj)))
    lvy = {'y': yy, 'j': Ly(jr), 'P': Ly(Lj(d['pr'])), 'M': Ly(Lj(mr))}
    yt = icc_mem(w, Ay, 'y', 'P', TOP, yy, Ly(Lj(d['pr'])), Ly(Lj(topr)), lin8(w, Ay, [y0, Ly(sj([jn], 'nn0ge0d', '0 <_ j'))], 'P <_ y', lvy), lin8(w, Ay, [yb, Ly(j1)], 'y <_ %s' % TOP, lvy))
    eqt, _ = w.wcongr('( F ` ( S + ( _i x. t ) ) ) =/= 0', {'t': 'y'}, 't = y', {'t': w.s([], 'id', '( t = y -> t = y )')})
    fy = sy([eqt, Ly(Lj(hnz)), yt], 'rspcdva', '( F ` ( S + ( _i x. y ) ) ) =/= 0')
    BY = '( F ` ( S + ( _i x. y ) ) ) =/= 0'
    eqx, _ = w.wcongr(BY, {'y': 'x'}, 'y = x', {'y': w.s([], 'id', '( y = x -> y = x )')})
    alx = sj([sj([fy], 'ralrimiva', 'A. y e. %s %s' % (WCj, BY)), w.s([eqx], 'cbvralvw', '( A. y e. %s %s <-> A. x e. %s ( F ` ( S + ( _i x. x ) ) ) =/= 0 )' % (WCj, BY, WCj))], 'sylib', 'A. x e. %s ( F ` ( S + ( _i x. x ) ) ) =/= 0' % WCj)
    # the zeros of the window avoid S
    eqi, _ = w.wcongr('A. o e. %s ( Re ` o ) =/= S' % ZK('i'), {'i': 'j'}, 'i = j', {'i': w.s([], 'id', '( i = j -> i = j )')})
    neo = sj([eqi, Lj(neio), jin], 'rspcdva', 'A. o e. %s ( Re ` o ) =/= S' % ZK())
    eqo = w.s([w.s([], 'fveq2', '( o = p -> ( Re ` o ) = ( Re ` p ) )')], 'neeq1d', '( o = p -> ( ( Re ` o ) =/= S <-> ( Re ` p ) =/= S ) )')
    nep = sj([neo, w.s([eqo], 'cbvralvw', '( A. o e. %s ( Re ` o ) =/= S <-> A. p e. %s ( Re ` p ) =/= S )' % (ZK(), ZK()))], 'sylib', 'A. p e. %s ( Re ` p ) =/= S' % ZK())
    WSUB = {'W': Wj}
    WA = tsub(ante_of(S['ef3win'])[0], WSUB)
    wa1, wa2, wa3 = top_and(WA)
    win = sj([sj([sj([Lj(dd), Lj(yp)], 'jca', wa1), sj([Lj(slh), wjr], 'jca', wa2), sj([alx, nep], 'jca', wa3)], '3jca', WA), w.inst('ef3win')], 'syl', tsub(ante_of(S['ef3win'])[1], WSUB))
    ibW, bW = conj_split(w, Aj, win)
    # log XA ( T0 ( j ) ) <_ LT4
    from ef3_f import AT4
    t0 = T0()
    t0r = sj([wjr, numst(w, Aj, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % t0)
    at0 = sj([sj([t0r], 'recnd', '%s e. CC' % t0)], 'abscld', '( abs ` %s ) e. RR' % t0)
    ab = sj([sj([lin8(w, Aj, [Lj(d['p1']), sj([jn], 'nn0ge0d', '0 <_ j')], '-u ( T + 2 ) <_ %s' % t0, lvj), lin8(w, Aj, [j1, Lj(d['m2'])], '%s <_ ( T + 2 )' % t0, lvj)], 'jca', '( -u ( T + 2 ) <_ %s /\\ %s <_ ( T + 2 ) )' % (t0, t0)),
             sj([t0r, sj([Lj(d['tr']), numst(w, Aj, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')], 'absled', '( ( abs ` %s ) <_ ( T + 2 ) <-> ( -u ( T + 2 ) <_ %s /\\ %s <_ ( T + 2 ) ) )' % (t0, t0, t0))], 'mpbird', '( abs ` %s ) <_ ( T + 2 )' % t0)
    X1 = XA(t0)
    x1le = sj([sj([at0, numst(w, Aj, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % t0), sj([Lj(d['tr']), numst(w, Aj, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), Lj(ar), lin8(w, Aj, [Lj(a1)], '0 <_ A', {'A': Lj(ar)}),
               lin8(w, Aj, [ab], '( ( abs ` %s ) + 2 ) <_ ( T + 4 )' % t0, {'( abs ` %s )' % t0: at0, 'T': Lj(d['tr'])})], 'lemul2ad', '%s <_ %s' % (X1, AT4))
    x1r = sj([Lj(ar), sj([at0, numst(w, Aj, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % t0)], 'remulcld', '%s e. RR' % X1)
    x1p = sj([x1r, lin.linarith(w, Aj, [Lj(a1), sj([sj([t0r], 'recnd', '%s e. CC' % t0)], 'absge0d', '0 <_ ( abs ` %s )' % t0)], '0 < %s' % X1,
                                  closure=Closure(w, Aj, {'A': ('RR', Lj(ar)), '( abs ` %s )' % t0: ('RR', at0)}), products=True)], 'elrpd', '%s e. RR+' % X1)
    lx = sj([x1le, sj([x1p, Lj(f['atp'])], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ %s )' % (X1, AT4, X1, LT4))], 'mpbid', '( log ` %s ) <_ %s' % (X1, LT4))
    lx1r = sj([x1p], 'relogcld', '( log ` %s ) e. RR' % X1)
    # IG_j >_ 0 and real
    IGj = 'S. %s ( 1 / ( 1 + ( abs ` l ) ) ) _d l' % WIN()
    ibgt = sj([wjr, wjh, w.inst('ef1iac')], 'syl2anc', '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) e. L^1' % WIN())
    cbg = w.s([w.s([w.s([w.s([], 'fveq2', '( t = l -> ( abs ` t ) = ( abs ` l ) )')], 'oveq2d', '( t = l -> ( 1 + ( abs ` t ) ) = ( 1 + ( abs ` l ) ) )')], 'oveq2d', '( t = l -> ( 1 / ( 1 + ( abs ` t ) ) ) = ( 1 / ( 1 + ( abs ` l ) ) ) )')], 'cbvmptv',
              '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) = ( l e. %s |-> ( 1 / ( 1 + ( abs ` l ) ) ) )' % (WIN(), WIN()))
    ibg = sj([sj([cbg], 'a1i', '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) = ( l e. %s |-> ( 1 / ( 1 + ( abs ` l ) ) ) )' % (WIN(), WIN())), ibgt], 'eqeltrrd', '( l e. %s |-> ( 1 / ( 1 + ( abs ` l ) ) ) ) e. L^1' % WIN())
    Ajl = '( %s /\\ l e. %s )' % (Aj, WIN())
    sjl = St(w, Ajl)
    llr_ = sjl([sjl([w.s([], 'ioossre', '%s C_ RR' % WIN())], 'a1i', '%s C_ RR' % WIN()), sjl([], 'simpr', 'l e. %s' % WIN())], 'sseldd', 'l e. RR')
    alr = sjl([sjl([llr_], 'recnd', 'l e. CC')], 'abscld', '( abs ` l ) e. RR')
    gp = sjl([sjl([sjl([numst(w, Ajl, '1', 'RR'), alr], 'readdcld', '( 1 + ( abs ` l ) ) e. RR'), lin8(w, Ajl, [sjl([sjl([llr_], 'recnd', 'l e. CC')], 'absge0d', '0 <_ ( abs ` l )')], '0 < ( 1 + ( abs ` l ) )', {'( abs ` l )': alr})], 'elrpd', '( 1 + ( abs ` l ) ) e. RR+')], 'rpreccld', '( 1 / ( 1 + ( abs ` l ) ) ) e. RR+')
    igr = sj([sjl([gp], 'rpred', '( 1 / ( 1 + ( abs ` l ) ) ) e. RR'), ibg], 'itgrecl', '%s e. RR' % IGj)
    ig0 = sj([ibg, sjl([gp], 'rpred', '( 1 / ( 1 + ( abs ` l ) ) ) e. RR'), sjl([gp], 'rpge0d', '0 <_ ( 1 / ( 1 + ( abs ` l ) ) )')], 'itgge0', '0 <_ %s' % IGj)
    from ef3_f import zk_facts_v
    KLX = '( %s x. ( log ` %s ) )' % (KLD, X1)
    KLT = '( %s x. %s )' % (KLD, LT4)
    SWj = 'sum_ q e. %s ( %s x. %s )' % (ZK(), WQ(), RS('S'))
    zfj = conj_split(w, Aj, sj([sj([Lj(dd), zk_t0r(w, Aj, Lj(d['pr']), jr)], 'jca', '( %s /\\ %s e. RR )' % (DD(), T0())), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': T0()})))[0]
    Ajq = '( %s /\\ q e. %s )' % (Aj, ZK())
    sjq = St(w, Ajq)
    zkq = zk_facts_v(w, Ajq, lift(w, dd, Ajq), lift(w, d['pr'], Ajq), lift(w, jr, Ajq), sjq([], 'simpr', 'q e. %s' % ZK()))
    dqa = '( abs ` ( S - ( Re ` q ) ) )'
    dqs = sjq([sjq([lift(w, sr, Ajq), zkq['rer']], 'resubcld', '( S - ( Re ` q ) ) e. RR')], 'recnd', '( S - ( Re ` q ) ) e. CC')
    rsq = sjq([sjq([dqs], 'abscld', '%s e. RR' % dqa), sjq([dqs], 'absge0d', '0 <_ %s' % dqa), sjq([numst(w, Ajq, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR'), w.inst('recxpcl')], 'syl3anc', '%s e. RR' % RS('S'))
    wrr = sjq([zkq['wqr'], rsq], 'remulcld', '( %s x. %s ) e. RR' % (WQ(), RS('S')))
    swr = sj([zfj, wrr], 'fsumrecl', '%s e. RR' % SWj)
    klxr = sj([numst(w, Aj, KLD, 'RR'), lx1r], 'remulcld', '%s e. RR' % KLX)
    kltr = sj([numst(w, Aj, KLD, 'RR'), Lj(f['lr'])], 'remulcld', '%s e. RR' % KLT)
    kle = lin8(w, Aj, [lx], '%s <_ %s' % (KLX, KLT), {'( log ` %s )' % X1: lx1r, LT4: Lj(f['lr'])})
    b1 = sj([klxr, kltr, igr, ig0, kle], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (KLX, IGj, KLT, IGj))
    S135 = '( ; ; 1 3 5 x. %s )' % SWj
    s135 = sj([numst(w, Aj, '; ; 1 3 5', 'RR'), swr], 'remulcld', '%s e. RR' % S135)
    b2 = sj([b1, sj([sj([klxr, igr], 'remulcld', '( %s x. %s ) e. RR' % (KLX, IGj)), sj([kltr, igr], 'remulcld', '( %s x. %s ) e. RR' % (KLT, IGj)), s135], 'leadd1d',
                    '( ( %s x. %s ) <_ ( %s x. %s ) <-> ( ( %s x. %s ) + %s ) <_ ( ( %s x. %s ) + %s ) )' % (KLX, IGj, KLT, IGj, KLX, IGj, S135, KLT, IGj, S135))], 'mpbid',
            '( ( %s x. %s ) + %s ) <_ ( ( %s x. %s ) + %s )' % (KLX, IGj, S135, KLT, IGj, S135))
    YS = '( Y ^c S )'
    ysp = s([yp, sr], 'rpcxpcld', '%s e. RR+' % YS)
    ysr = s([ysp], 'rpred', '%s e. RR' % YS)
    IN1 = '( ( %s x. %s ) + %s )' % (KLX, IGj, S135)
    IN2 = '( ( %s x. %s ) + %s )' % (KLT, IGj, S135)
    in1r = sj([sj([klxr, igr], 'remulcld', '( %s x. %s ) e. RR' % (KLX, IGj)), s135], 'readdcld', '%s e. RR' % IN1)
    in2r = sj([sj([kltr, igr], 'remulcld', '( %s x. %s ) e. RR' % (KLT, IGj)), s135], 'readdcld', '%s e. RR' % IN2)
    b3 = sj([in1r, in2r, Lj(ysr), Lj(s([ysp], 'rpge0d', '0 <_ %s' % YS)), b2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (YS, IN1, YS, IN2))
    IWj = 'S. %s %s _d l' % (WIN(), LL)
    Bj = '( %s x. %s )' % (YS, IN2)
    iwr = sj([ll_facts(Aj, WIN(), sj([sj([sj([sj([Lj(d['pr'])], 'rexrd', 'P e. RR*'), sj([Lj(topr)], 'rexrd', '%s e. RR*' % TOP)], 'jca', '( P e. RR* /\\ %s e. RR* )' % TOP),
                                             sj([lin8(w, Aj, [sj([jn], 'nn0ge0d', '0 <_ j')], 'P <_ %s' % Wj, lvj), lin8(w, Aj, [j1], '( %s + ( 1 / 2 ) ) <_ %s' % (Wj, TOP), lvj)], 'jca', '( P <_ %s /\\ ( %s + ( 1 / 2 ) ) <_ %s )' % (Wj, Wj, TOP))], 'jca',
                                            '( ( P e. RR* /\\ %s e. RR* ) /\\ ( P <_ %s /\\ ( %s + ( 1 / 2 ) ) <_ %s ) )' % (TOP, Wj, Wj, TOP)), w.inst('ioossioo')], 'syl', '%s C_ %s' % (WIN(), IPT)))[0], ibW], 'itgrecl', '%s e. RR' % IWj)
    bj = sj([iwr, sj([Lj(ysr), in1r], 'remulcld', '( %s x. %s ) e. RR' % (YS, IN1)), sj([Lj(ysr), in2r], 'remulcld', '%s e. RR' % Bj), bW, b3], 'letrd', '%s <_ %s' % (IWj, Bj))
    fz = s([w.s([], 'fzofi', '( 0 ..^ M ) e. Fin')], 'a1i', '( 0 ..^ M ) e. Fin')
    SIW = 'sum_ j e. ( 0 ..^ M ) %s' % IWj
    SB = 'sum_ j e. ( 0 ..^ M ) %s' % Bj
    bjr = sj([Lj(ysr), in2r], 'remulcld', '%s e. RR' % Bj)
    t1 = s([fz, iwr, bjr, bj], 'fsumle', '%s <_ %s' % (SIW, SB))
    SIN2 = 'sum_ j e. ( 0 ..^ M ) %s' % IN2
    t2 = s([fz, s([ysr], 'recnd', '%s e. CC' % YS), sj([in2r], 'recnd', '%s e. CC' % IN2)], 'fsummulc2', '( %s x. %s ) = %s' % (YS, SIN2, SB))
    KIG = '( %s x. %s )' % (KLT, IGj)
    SKIG = 'sum_ j e. ( 0 ..^ M ) %s' % KIG
    SS135 = 'sum_ j e. ( 0 ..^ M ) %s' % S135
    t3 = s([fz, sj([sj([kltr, igr], 'remulcld', '%s e. RR' % KIG)], 'recnd', '%s e. CC' % KIG), sj([s135], 'recnd', '%s e. CC' % S135)], 'fsumadd', '%s = ( %s + %s )' % (SIN2, SKIG, SS135))
    SIG = 'sum_ j e. ( 0 ..^ M ) %s' % IGj
    SSW = 'sum_ j e. ( 0 ..^ M ) %s' % SWj
    kltr0 = s([numst(w, A0, KLD, 'RR'), f['lr']], 'remulcld', '%s e. RR' % KLT)
    t4 = s([fz, s([kltr0], 'recnd', '%s e. CC' % KLT), sj([igr], 'recnd', '%s e. CC' % IGj)], 'fsummulc2', '( %s x. %s ) = %s' % (KLT, SIG, SKIG))
    t5 = s([fz, numst(w, A0, '; ; 1 3 5', 'CC'), sj([swr], 'recnd', '%s e. CC' % SWj)], 'fsummulc2', '( ; ; 1 3 5 x. %s ) = %s' % (SSW, SS135))
    RHS1 = '( %s x. ( ( %s x. %s ) + ( ; ; 1 3 5 x. %s ) ) )' % (YS, KLT, SIG, SSW)
    t6 = s([s([t2], 'eqcomd', '%s = ( %s x. %s )' % (SB, YS, SIN2)), s([s([t3, s([s([t4], 'eqcomd', '%s = ( %s x. %s )' % (SKIG, KLT, SIG)), s([t5], 'eqcomd', '%s = ( ; ; 1 3 5 x. %s )' % (SS135, SSW))], 'oveq12d',
                                                                                                         '( %s + %s ) = ( ( %s x. %s ) + ( ; ; 1 3 5 x. %s ) )' % (SKIG, SS135, KLT, SIG, SSW))], 'eqtrd', '%s = ( ( %s x. %s ) + ( ; ; 1 3 5 x. %s ) )' % (SIN2, KLT, SIG, SSW))], 'oveq2d',
                                                                                       '( %s x. %s ) = %s' % (YS, SIN2, RHS1))], 'eqtrd', '%s = %s' % (SB, RHS1))
    # sum of the window integrals of g
    Al = '( %s /\\ l e. %s )' % (A0, IPT)
    sal = St(w, Al)
    lr0 = sal([sal([w.s([], 'ioossre', '%s C_ RR' % IPT)], 'a1i', '%s C_ RR' % IPT), sal([], 'simpr', 'l e. %s' % IPT)], 'sseldd', 'l e. RR')
    alr0 = sal([sal([lr0], 'recnd', 'l e. CC')], 'abscld', '( abs ` l ) e. RR')
    gp0 = sal([sal([sal([numst(w, Al, '1', 'RR'), alr0], 'readdcld', '( 1 + ( abs ` l ) ) e. RR'), lin8(w, Al, [sal([sal([lr0], 'recnd', 'l e. CC')], 'absge0d', '0 <_ ( abs ` l )')], '0 < ( 1 + ( abs ` l ) )', {'( abs ` l )': alr0})], 'elrpd', '( 1 + ( abs ` l ) ) e. RR+')], 'rpreccld', '( 1 / ( 1 + ( abs ` l ) ) ) e. RR+')
    ibgT = s([d['pr'], topr, w.inst('ef1iac')], 'syl2anc', '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) e. L^1' % IPT)
    cbgT = w.s([w.s([w.s([w.s([], 'fveq2', '( t = l -> ( abs ` t ) = ( abs ` l ) )')], 'oveq2d', '( t = l -> ( 1 + ( abs ` t ) ) = ( 1 + ( abs ` l ) ) )')], 'oveq2d', '( t = l -> ( 1 / ( 1 + ( abs ` t ) ) ) = ( 1 / ( 1 + ( abs ` l ) ) ) )')], 'cbvmptv',
               '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) = ( l e. %s |-> ( 1 / ( 1 + ( abs ` l ) ) ) )' % (IPT, IPT))
    ibgl = s([s([cbgT], 'a1i', '( t e. %s |-> ( 1 / ( 1 + ( abs ` t ) ) ) ) = ( l e. %s |-> ( 1 / ( 1 + ( abs ` l ) ) ) )' % (IPT, IPT)), ibgT], 'eqeltrrd', '( l e. %s |-> ( 1 / ( 1 + ( abs ` l ) ) ) ) e. L^1' % IPT)
    adjg = s([d['pr'], d['mn'], sal([sal([gp0], 'rpred', '( 1 / ( 1 + ( abs ` l ) ) ) e. RR')], 'recnd', '( 1 / ( 1 + ( abs ` l ) ) ) e. CC'), ibgl], 'ef3adj',
             'S. %s ( 1 / ( 1 + ( abs ` l ) ) ) _d l = %s' % (IPT, SIG))
    IAt = 'S. %s ( 1 / ( 1 + ( abs ` t ) ) ) _d t' % IPT
    W2 = '( T + 2 )'
    ial = s([s([s([d['pr'], topr, s([d['tr'], numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % W2)], '3jca', '( P e. RR /\\ %s e. RR /\\ %s e. RR )' % (TOP, W2)),
                s([s([d['p0'], d['m0']], 'jca', '( P <_ 0 /\\ 0 <_ %s )' % TOP), s([lin8(w, A0, [d['p1']], '-u %s <_ P' % W2, lv0), d['m2']], 'jca', '( -u %s <_ P /\\ %s <_ %s )' % (W2, TOP, W2))], 'jca',
                  '( ( P <_ 0 /\\ 0 <_ %s ) /\\ ( -u %s <_ P /\\ %s <_ %s ) )' % (TOP, W2, TOP, W2))], 'jca', '( ( P e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ ( ( P <_ 0 /\\ 0 <_ %s ) /\\ ( -u %s <_ P /\\ %s <_ %s ) ) )' % (TOP, W2, TOP, W2, TOP, W2)),
             w.inst('ef1ial')], 'syl', '%s <_ ( 2 x. ( log ` ( 1 + %s ) ) )' % (IAt, W2))
    cbi = w.s([w.s([w.s([w.s([], 'fveq2', '( t = l -> ( abs ` t ) = ( abs ` l ) )')], 'oveq2d', '( t = l -> ( 1 + ( abs ` t ) ) = ( 1 + ( abs ` l ) ) )')], 'oveq2d', '( t = l -> ( 1 / ( 1 + ( abs ` t ) ) ) = ( 1 / ( 1 + ( abs ` l ) ) ) )')], 'cbvitgv',
              '%s = S. %s ( 1 / ( 1 + ( abs ` l ) ) ) _d l' % (IAt, IPT))
    sig1 = s([s([s([cbi], 'a1i', '%s = S. %s ( 1 / ( 1 + ( abs ` l ) ) ) _d l' % (IAt, IPT)), adjg], 'eqtrd', '%s = %s' % (IAt, SIG)), ial], 'eqbrtrrd', '%s <_ ( 2 x. ( log ` ( 1 + %s ) ) )' % (SIG, W2))
    L1W = '( log ` ( 1 + %s ) )' % W2
    w1p = s([s([numst(w, A0, '1', 'RR'), s([d['tr'], numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % W2)], 'readdcld', '( 1 + %s ) e. RR' % W2), lin8(w, A0, [d['t2']], '0 < ( 1 + %s )' % W2, lv0)], 'elrpd', '( 1 + %s ) e. RR+' % W2)
    au = lin.linarith(w, A0, [a1, d['t2']], '( 1 + %s ) <_ %s' % (W2, AT4), closure=f['cl'], products=True)
    lw = s([au, s([w1p, f['atp']], 'logled', '( ( 1 + %s ) <_ %s <-> %s <_ %s )' % (W2, AT4, L1W, LT4))], 'mpbid', '%s <_ %s' % (L1W, LT4))
    sigr = s([fz, igr], 'fsumrecl', '%s e. RR' % SIG)
    l1wr = s([w1p], 'relogcld', '%s e. RR' % L1W)
    lw2 = s([l1wr, f['lr'], numst(w, A0, '2', 'RR'), numst(w, A0, '2', 'ge0'), lw], 'lemul2ad', '( 2 x. %s ) <_ ( 2 x. %s )' % (L1W, LT4))
    sig2 = s([sigr, s([numst(w, A0, '2', 'RR'), l1wr], 'remulcld', '( 2 x. %s ) e. RR' % L1W), s([numst(w, A0, '2', 'RR'), f['lr']], 'remulcld', '( 2 x. %s ) e. RR' % LT4), sig1, lw2], 'letrd', '%s <_ ( 2 x. %s )' % (SIG, LT4))
    # sum of the window weights = the hypothesis functional
    SQj = 'sum_ q e. %s ( %s x. %s )' % (ZK(), WQ(), RS('S'))
    e_ji, _ = w.congr(SQj, {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    r1 = w.s([e_ji], 'cbvsumv', '%s = sum_ i e. ( 0 ..^ M ) sum_ q e. %s ( %s x. %s )' % (SSW, ZK('i'), WQ(), RS('S')))
    e_qo, _ = w.congr('( %s x. %s )' % (WQ(), RS('S')), {'q': 'o'}, 'q = o', {'q': w.s([], 'id', '( q = o -> q = o )')})
    SOi = 'sum_ o e. %s ( %s x. %s )' % (ZK('i'), WQ('o'), RS('S', 'o'))
    r2 = w.s([w.s([w.s([e_qo], 'cbvsumv', 'sum_ q e. %s ( %s x. %s ) = %s' % (ZK('i'), WQ(), RS('S'), SOi))], 'a1i', '( i e. ( 0 ..^ M ) -> sum_ q e. %s ( %s x. %s ) = %s )' % (ZK('i'), WQ(), RS('S'), SOi))], 'sumeq2i',
             'sum_ i e. ( 0 ..^ M ) sum_ q e. %s ( %s x. %s ) = %s' % (ZK('i'), WQ(), RS('S'), PHIio))
    rr = w.s([r1, r2], 'eqtri', '%s = %s' % (SSW, PHIio))
    ssw2 = s([s([rr], 'a1i', '%s = %s' % (SSW, PHIio)), hph], 'eqbrtrd', '%s <_ ( %s x. ( %s ^ 2 ) )' % (SSW, KS, LT4))
    sswr = s([fz, swr], 'fsumrecl', '%s e. RR' % SSW)
    # assemble
    L2_ = '( %s ^ 2 )' % LT4
    l2r = s([f['lr']], 'resqcld', '%s e. RR' % L2_)
    klt0 = lin8(w, A0, [f['l0']], '0 <_ %s' % KLT, {LT4: f['lr']})
    u1 = s([sigr, s([numst(w, A0, '2', 'RR'), f['lr']], 'remulcld', '( 2 x. %s ) e. RR' % LT4), kltr0, klt0, sig2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 2 x. %s ) )' % (KLT, SIG, KLT, LT4))
    u2 = s([sswr, s([numst(w, A0, KS, 'RR'), l2r], 'remulcld', '( %s x. %s ) e. RR' % (KS, L2_)), numst(w, A0, '; ; 1 3 5', 'RR'), numst(w, A0, '; ; 1 3 5', 'ge0'), ssw2], 'lemul2ad', '( ; ; 1 3 5 x. %s ) <_ ( ; ; 1 3 5 x. ( %s x. %s ) )' % (SSW, KS, L2_))
    IN3 = '( ( %s x. %s ) + ( ; ; 1 3 5 x. %s ) )' % (KLT, SIG, SSW)
    IN4 = '( ( %s x. ( 2 x. %s ) ) + ( ; ; 1 3 5 x. ( %s x. %s ) ) )' % (KLT, LT4, KS, L2_)
    u3 = s([u1, u2], 'le2addd', '%s <_ %s' % (IN3, IN4))
    in3r = s([s([kltr0, sigr], 'remulcld', '( %s x. %s ) e. RR' % (KLT, SIG)), s([numst(w, A0, '; ; 1 3 5', 'RR'), sswr], 'remulcld', '( ; ; 1 3 5 x. %s ) e. RR' % SSW)], 'readdcld', '%s e. RR' % IN3)
    in4r = s([s([kltr0, s([numst(w, A0, '2', 'RR'), f['lr']], 'remulcld', '( 2 x. %s ) e. RR' % LT4)], 'remulcld', '( %s x. ( 2 x. %s ) ) e. RR' % (KLT, LT4)), s([numst(w, A0, '; ; 1 3 5', 'RR'), s([numst(w, A0, KS, 'RR'), l2r], 'remulcld', '( %s x. %s ) e. RR' % (KS, L2_))], 'remulcld', '( ; ; 1 3 5 x. ( %s x. %s ) ) e. RR' % (KS, L2_))], 'readdcld', '%s e. RR' % IN4)
    u4 = s([in3r, in4r, ysr, s([ysp], 'rpge0d', '0 <_ %s' % YS), u3], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (YS, IN3, YS, IN4))
    ZY = '( %s x. %s )' % (YS, L2_)
    cl = Closure(w, A0, {YS: ('RR', ysr), LT4: ('RR', f['lr'])}); cl.atom(YS); cl.atom(LT4)
    sqv = s([s([f['lr']], 'recnd', '%s e. CC' % LT4)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (LT4, LT4, LT4))
    e1 = ringeq(w, A0, '( %s x. ( ( %s x. ( 2 x. %s ) ) + ( ; ; 1 3 5 x. ( %s x. ( %s x. %s ) ) ) ) )' % (YS, KLT, LT4, KS, LT4, LT4), '( ; ; ; ; ; ; ; ; 4 5 1 0 4 0 0 0 0 x. ( %s x. ( %s x. %s ) ) )' % (YS, LT4, LT4), cl)
    e2 = ringeq(w, A0, '( ( %s x. %s ) x. ( %s x. %s ) )' % (KL, YS, LT4, LT4), '( %s x. ( %s x. ( %s x. %s ) ) )' % (KL, YS, LT4, LT4), cl)
    LL2 = '( %s x. %s )' % (LT4, LT4)
    IN4b = '( ( %s x. ( 2 x. %s ) ) + ( ; ; 1 3 5 x. ( %s x. %s ) ) )' % (KLT, LT4, KS, LL2)
    q1 = s([s([s([s([sqv], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (KS, L2_, KS, LL2))], 'oveq2d', '( ; ; 1 3 5 x. ( %s x. %s ) ) = ( ; ; 1 3 5 x. ( %s x. %s ) )' % (KS, L2_, KS, LL2))], 'oveq2d', '%s = %s' % (IN4, IN4b))], 'oveq2d',
           '( %s x. %s ) = ( %s x. %s )' % (YS, IN4, YS, IN4b))
    ZZ = '( %s x. %s )' % (YS, LL2)
    zr = s([ysr, s([f['lr'], f['lr']], 'remulcld', '%s e. RR' % LL2)], 'remulcld', '%s e. RR' % ZZ)
    z0 = s([ysr, s([f['lr'], f['lr']], 'remulcld', '%s e. RR' % LL2), s([ysp], 'rpge0d', '0 <_ %s' % YS), s([f['lr'], f['lr'], f['l0'], f['l0']], 'mulge0d', '0 <_ %s' % LL2)], 'mulge0d', '0 <_ %s' % ZZ)
    q2 = lin8(w, A0, [z0], '( ; ; ; ; ; ; ; ; 4 5 1 0 4 0 0 0 0 x. %s ) <_ ( %s x. %s )' % (ZZ, KL, ZZ), {ZZ: zr})
    q3 = s([s([s([q1, e1], 'eqtrd', '( %s x. %s ) = ( ; ; ; ; ; ; ; ; 4 5 1 0 4 0 0 0 0 x. %s )' % (YS, IN4, ZZ)), q2], 'eqbrtrd', '( %s x. %s ) <_ ( %s x. %s )' % (YS, IN4, KL, ZZ)),
            s([s([s([sqv], 'oveq2d', '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (KL, YS, L2_, KL, YS, LL2)), e2], 'eqtrd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (KL, YS, L2_, KL, ZZ))], 'eqcomd',
              '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (KL, ZZ, KL, YS, L2_))], 'breqtrd', '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (YS, IN4, KL, YS, L2_))
    LIN = '( abs ` ( %s lint <. ( S + ( _i x. P ) ) , ( S + ( _i x. Q ) ) >. ) )' % LDI()
    linr = s([s([s([s([], 'id', 'x')], 'id', 'x')], 'id', 'x')], 'id', 'x') if False else None
    siwr = s([fz, iwr], 'fsumrecl', '%s e. RR' % SIW)
    sbr = s([fz, bjr], 'fsumrecl', '%s e. RR' % SB)
    ittr = s([llT, ibT], 'itgrecl', '%s e. RR' % ITT)
    c1 = s([iqr, ittr, s([siwr, sbr, t1], 'id', 'x') if False else siwr, le1, adj], 'id', 'x') if False else None
    c1 = s([le1, adj], 'breqtrd', '%s <_ %s' % (IQQ, SIW))
    c2 = s([iqr, siwr, sbr, c1, t1], 'letrd', '%s <_ %s' % (IQQ, SB))
    c3 = s([c2, t6], 'breqtrd', '%s <_ %s' % (IQQ, RHS1))
    c4 = s([iqr, s([ysr, in3r], 'remulcld', '%s e. RR' % RHS1), s([ysr, in4r], 'remulcld', '( %s x. %s ) e. RR' % (YS, IN4)), c3, u4], 'letrd', '%s <_ ( %s x. %s )' % (IQQ, YS, IN4))
    fin = s([iqr, s([ysr, in4r], 'remulcld', '( %s x. %s ) e. RR' % (YS, IN4)), s([s([numst(w, A0, KL, 'RR'), ysr], 'remulcld', '( %s x. %s ) e. RR' % (KL, YS)), l2r], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (KL, YS, L2_)), c4, q3], 'letrd',
            '%s <_ ( ( %s x. %s ) x. %s )' % (IQQ, KL, YS, L2_))
    linr = s([s([s([s([ldc, w.inst('cncff')], 'syl', 'x')], 'id', 'x')], 'id', 'x')], 'id', 'x') if False else None
    w.qed([s([s([s([s([], 'id', 'x')], 'id', 'x')], 'id', 'x')], 'id', 'x') if False else bQ, fin], 'letrd' if False else 'id', 'x') if False else None
    # the segment integral is a complex number
    from ef3_a import icc_mem as _im
    alQ = seg_in('Q', qr, qtop)
    eqt2, _ = w.wcongr('( S + ( _i x. x ) ) e. %s' % LD0, {'x': 't'}, 'x = t', {'x': w.s([], 'id', '( x = t -> x = t )')})
    alQt = s([alQ, w.s([eqt2], 'cbvralvw', '( A. x e. ( P [,] Q ) ( S + ( _i x. x ) ) e. %s <-> A. t e. ( P [,] Q ) ( S + ( _i x. t ) ) e. %s )' % (LD0, LD0))], 'sylib', 'A. t e. ( P [,] Q ) ( S + ( _i x. t ) ) e. %s' % LD0)
    lvq = {'P': d['pr'], 'Q': qr}
    pin = _im(w, A0, 'P', 'P', 'Q', d['pr'], d['pr'], qr, lin8(w, A0, [], 'P <_ P', lvq), lin8(w, A0, [pq], 'P <_ Q', lvq))
    qin2 = _im(w, A0, 'Q', 'P', 'Q', qr, d['pr'], qr, lin8(w, A0, [pq], 'P <_ Q', lvq), lin8(w, A0, [], 'Q <_ Q', lvq))
    VA = tsub(ante_of(S['ef3vseg'])[0], {'P': 'S', 'L': 'P', 'H': 'Q', 'E': 'P', 'K': 'Q', 'D': LD0})
    va1, va2 = top_and(VA)
    SA_, SB_ = '( S + ( _i x. P ) )', '( S + ( _i x. Q ) )'
    seg = s([s([s([sr, s([d['pr'], qr], 'jca', '( P e. RR /\\ Q e. RR )')], 'jca', va1), s([s([pin, qin2], 'jca', top_and(va2)[0]), alQt], 'jca', va2)], 'jca', VA), w.inst('ef3vseg')], 'syl', '( %s cseg %s ) C_ %s' % (SA_, SB_, LD0))
    ac = crfacts(w, A0, 'S', 'P', sr, d['pr'])[0]; bc = crfacts(w, A0, 'S', 'Q', sr, qr)[0]
    lc = s([s([s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA_, SB_)), s([ldc, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (LDI(), LD0, SA_, SB_, LD0))], 'jca',
               '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (SA_, SB_, LDI(), LD0, SA_, SB_, LD0)), w.inst('lintcl')], 'syl', '( %s lint <. %s , %s >. ) e. CC' % (LDI(), SA_, SB_))
    lr_ = s([lc], 'abscld', '%s e. RR' % LIN)
    w.qed([lr_, iqr, s([s([numst(w, A0, KL, 'RR'), ysr], 'remulcld', '( %s x. %s ) e. RR' % (KL, YS)), l2r], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (KL, YS, L2_)), bQ, fin], 'letrd', S['ef3lcore'])
    return run8(w)


def gen_left():
    w = W('ef3left', 'Lean ` left_edge_le ` : for ` a = P <_ 0 <_ P + M / 2 <_ T + 2 ` , an abscissa ` S e. [ 9 / 16 , 5 / 8 ] ` off the real parts of the window zeros with Lean\'s functional at most ` 2304000 log ^ 2 ( A ( T + 4 ) ) ` ( ~ ef3sig ) and ` F =/= 0 ` on the left edge, ` abs integral_(S+iP)^(S+iQ) ( F \' / F ) Y ^ z / z <_ 500000000 Y ^ S log ^ 2 ( A ( T + 4 ) ) ` ( ~ ef3lcore after renaming the bound letters).')
    A0, G = ante_of(S['ef3left'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1)
    slh, nejq = conj_split(w, A0, s([], 'simp2', H2))
    hnz, hph, qq = conj_split(w, A0, s([], 'simp3', H3))
    I = '( 0 ..^ M )'
    BQo = lambda j: 'A. o e. %s ( Re ` o ) =/= S' % ZK(j)
    eqqo = w.s([w.s([], 'fveq2', '( q = o -> ( Re ` q ) = ( Re ` o ) )')], 'neeq1d', '( q = o -> ( ( Re ` q ) =/= S <-> ( Re ` o ) =/= S ) )')
    inn = w.s([eqqo], 'cbvralvw', '( A. q e. %s ( Re ` q ) =/= S <-> %s )' % (ZK(), BQo('j')))
    rb = w.s([w.s([inn], 'a1i', '( j e. %s -> ( A. q e. %s ( Re ` q ) =/= S <-> %s ) )' % (I, ZK(), BQo('j')))], 'ralbiia', '( A. j e. %s A. q e. %s ( Re ` q ) =/= S <-> A. j e. %s %s )' % (I, ZK(), I, BQo('j')))
    eqji, _ = w.wcongr(BQo('j'), {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    outr = w.s([eqji], 'cbvralvw', '( A. j e. %s %s <-> A. i e. %s %s )' % (I, BQo('j'), I, BQo('i')))
    nio = s([nejq, w.s([rb, outr], 'bitri', '( A. j e. %s A. q e. %s ( Re ` q ) =/= S <-> A. i e. %s %s )' % (I, ZK(), I, BQo('i')))], 'sylib', 'A. i e. %s %s' % (I, BQo('i')))
    SQj = 'sum_ q e. %s ( %s x. %s )' % (ZK(), WQ(), RS('S'))
    e_ji, _ = w.congr(SQj, {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    r1 = w.s([e_ji], 'cbvsumv', '%s = sum_ i e. %s sum_ q e. %s ( %s x. %s )' % (PHI('S'), I, ZK('i'), WQ(), RS('S')))
    e_qo, _ = w.congr('( %s x. %s )' % (WQ(), RS('S')), {'q': 'o'}, 'q = o', {'q': w.s([], 'id', '( q = o -> q = o )')})
    SOi = 'sum_ o e. %s ( %s x. %s )' % (ZK('i'), WQ('o'), RS('S', 'o'))
    r2 = w.s([w.s([w.s([e_qo], 'cbvsumv', 'sum_ q e. %s ( %s x. %s ) = %s' % (ZK('i'), WQ(), RS('S'), SOi))], 'a1i', '( i e. %s -> sum_ q e. %s ( %s x. %s ) = %s )' % (I, ZK('i'), WQ(), RS('S'), SOi))], 'sumeq2i',
             'sum_ i e. %s sum_ q e. %s ( %s x. %s ) = %s' % (I, ZK('i'), WQ(), RS('S'), PHIio))
    rr = w.s([r1, r2], 'eqtri', '%s = %s' % (PHI('S'), PHIio))
    hio = s([s([rr], 'a1i', '%s = %s' % (PHI('S'), PHIio)), hph], 'eqbrtrrd', '%s <_ ( %s x. ( %s ^ 2 ) )' % (PHIio, KS, LT4))
    CA = ante_of(S['ef3lcore'])[0]
    c1, c2, c3 = top_and(CA)
    w.qed([s([h1, s([slh, nio], 'jca', c2), s([hnz, hio, qq], '3jca', c3)], '3jca', CA), w.inst('ef3lcore')], 'syl', S['ef3left'])
    return run8(w)


if __name__ == '__main__':
    gen_win()
    gen_lcore()
    gen_left()
