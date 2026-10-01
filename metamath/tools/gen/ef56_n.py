"""Sortie EF56: the numerics of the zeta contour (ef6nm), after EF4's ef4nm."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef4_f import c1_facts


def gen_nm():
    w = W('ef6nm', 'The numerics of Lean ` contour_zeta ` ( ` zeta_final_numeric ` ): four horizontal edges ( ` eta ` and ` g ` ), two right extras, two left edges and the zero-sum bound add up to at most ` 2 pi 1000000000 ( y log ^ 2 ( N T y ) / T + y ^ ( 5 / 8 ) log ^ 2 ( N ( T + 2 ) ) ) ` .')
    A0, G = ante_of(S['ef6nm'])
    c = Ctx(w, A0)
    g = c.g
    nn = g('N e. NN'); yr = g('Y e. RR'); y100 = g('; ; 1 0 0 <_ Y'); tr = g('T e. RR'); t2 = g('2 <_ T')
    sr = g('S e. RR'); s58 = g('S <_ ( 5 / 8 )')
    ar = g('A e. RR'); br = g('B e. RR'); ale = g('A <_ %s' % EDGE6); ble = g('B <_ %s' % ZB)
    nr = c([nn], 'nnred', 'N e. RR'); n1 = c([nn], 'nnge1d', '1 <_ N')
    f = c1_facts(w, c, yr, y100)
    L_ = '( log ` Y )'
    tp = c([tr, lin8(w, A0, [t2], '0 < T', {'T': tr})], 'elrpd', 'T e. RR+')
    cl = Closure(w, A0, {'N': ('NN', nn), 'T': ('RR+', tp), 'Y': ('RR+', f['yp']), 'S': ('RR', sr), L_: ('RR+', f['lp'])})
    R = lambda e: cl.mem(e, 'RR')
    lv = {'N': nr, 'T': tr, 'Y': yr}
    # logs
    N4, N2 = '( N x. ( T + 4 ) )', '( N x. ( T + 2 ) )'
    NTY = '( ( N x. T ) x. Y )'
    ln4r, lntr, lnyr, lr = R(LN4), R(LNT), R(LNY), R(L_)
    n4g = lin8(w, A0, [n1, t2], '1 <_ %s' % N4, lv, products=True)
    ln40 = c([c([R(N4), n4g], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (N4, N4)), w.inst('logge0')], 'syl', '0 <_ %s' % LN4)
    n2g = lin8(w, A0, [n1, t2], '1 <_ %s' % N2, lv, products=True)
    lnt0 = c([c([R(N2), n2g], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (N2, N2)), w.inst('logge0')], 'syl', '0 <_ %s' % LNT)
    TY = '( T x. Y )'
    ty = lin8(w, A0, [t2, y100], '( T + 4 ) <_ %s' % TY, lv, products=True)
    ntyl = c([R('( T + 4 )'), R(TY), nr, lin8(w, A0, [n1], '0 <_ N', lv), ty], 'lemul2ad', '%s <_ ( N x. %s )' % (N4, TY))
    ma = c([c([nr], 'recnd', 'N e. CC'), c([tr], 'recnd', 'T e. CC'), c([yr], 'recnd', 'Y e. CC')], 'mulassd', '%s = ( N x. %s )' % (NTY, TY))
    le4y = c([ntyl, c([ma], 'eqcomd', '( N x. %s ) = %s' % (TY, NTY))], 'breqtrd', '%s <_ %s' % (N4, NTY))
    l4y = c([le4y, c([cl.mem(N4, 'RR+'), cl.mem(NTY, 'RR+'), w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> %s <_ %s )' % (N4, NTY, LN4, LNY))], 'mpbid', '%s <_ %s' % (LN4, LNY))
    T2S = '( ( T + 2 ) ^ 2 )'
    t42 = lin8(w, A0, [t2], '( T + 4 ) <_ %s' % T2S, lv, products=True)
    a1 = c([R('( T + 4 )'), R(T2S), nr, lin8(w, A0, [n1], '0 <_ N', lv), t42], 'lemul2ad', '%s <_ ( N x. %s )' % (N4, T2S))
    nnn = lin8(w, A0, [n1], 'N <_ ( N x. N )', lv, products=True)
    a2 = c([nr, R('( N x. N )'), R(T2S), c([R('( T + 2 )')], 'sqge0d', '0 <_ %s' % T2S), nnn], 'lemul1ad', '( N x. %s ) <_ ( ( N x. N ) x. %s )' % (T2S, T2S))
    cln = Closure(w, A0, {'N': ('RR', nr), 'T': ('RR', tr)}); cln.atom('N'); cln.atom('T')
    ncc, t2c = c([nr], 'recnd', 'N e. CC'), c([R('( T + 2 )')], 'recnd', '( T + 2 ) e. CC')
    e_1 = c([ncc, t2c], 'sqmuld', '( %s ^ 2 ) = ( ( N ^ 2 ) x. %s )' % (N2, T2S))
    e_2 = c([c([ncc], 'sqvald', '( N ^ 2 ) = ( N x. N )')], 'oveq1d', '( ( N ^ 2 ) x. %s ) = ( ( N x. N ) x. %s )' % (T2S, T2S))
    a3 = c([c([e_1, e_2], 'eqtrd', '( %s ^ 2 ) = ( ( N x. N ) x. %s )' % (N2, T2S))], 'eqcomd', '( ( N x. N ) x. %s ) = ( %s ^ 2 )' % (T2S, N2))
    le42 = le_tr(w, A0, a1, N4, '( N x. %s )' % T2S, c([a2, a3], 'breqtrd', '( N x. %s ) <_ ( %s ^ 2 )' % (T2S, N2)), '( %s ^ 2 )' % N2)
    lg2 = c([le42, c([cl.mem(N4, 'RR+'), cl.mem('( %s ^ 2 )' % N2, 'RR+'), w.inst('logleb')], 'syl2anc', '( %s <_ ( %s ^ 2 ) <-> %s <_ ( log ` ( %s ^ 2 ) ) )' % (N4, N2, LN4, N2))], 'mpbid', '%s <_ ( log ` ( %s ^ 2 ) )' % (LN4, N2))
    rex = c([cl.mem(N2, 'RR+'), c.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ'), w.inst('relogexp')], 'syl2anc', '( log ` ( %s ^ 2 ) ) = ( 2 x. %s )' % (N2, LNT))
    l42 = c([lg2, rex], 'breqtrd', '%s <_ ( 2 x. %s )' % (LN4, LNT))
    nt1 = lin8(w, A0, [n1, t2], '1 <_ ( N x. T )', lv, products=True)
    y1n = c([numst(w, A0, '1', 'RR'), R('( N x. T )'), yr, lin8(w, A0, [y100], '0 <_ Y', lv), nt1], 'lemul1ad', '( 1 x. Y ) <_ %s' % NTY)
    yle = c([c([c([c([yr], 'recnd', 'Y e. CC')], 'mullidd', '( 1 x. Y ) = Y')], 'eqcomd', 'Y = ( 1 x. Y )'), y1n], 'eqbrtrd', 'Y <_ %s' % NTY)
    ly = c([yle, c([f['yp'], cl.mem(NTY, 'RR+'), w.inst('logleb')], 'syl2anc', '( Y <_ %s <-> %s <_ %s )' % (NTY, L_, LNY))], 'mpbid', '%s <_ %s' % (L_, LNY))
    lvl = {LN4: ln4r, LNT: lntr, LNY: lnyr, L_: lr}
    lny1 = lin8(w, A0, [f['l4'], ly], '1 <_ %s' % LNY, lvl)
    # squares
    sq_a = c([c([ln4r, ln40], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (LN4, LN4)), c([lnyr, l4y], 'jca', '( %s e. RR /\\ %s <_ %s )' % (LNY, LN4, LNY)), w.inst('le2sq2')], 'syl2anc', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LN4, LNY))
    sq_b0 = c([c([ln4r, ln40], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (LN4, LN4)), c([R('( 2 x. %s )' % LNT), l42], 'jca', '( ( 2 x. %s ) e. RR /\\ %s <_ ( 2 x. %s ) )' % (LNT, LN4, LNT)), w.inst('le2sq2')], 'syl2anc',
              '( %s ^ 2 ) <_ ( ( 2 x. %s ) ^ 2 )' % (LN4, LNT))
    cll = Closure(w, A0, {LNT: ('RR', lntr)}); cll.atom(LNT)
    s2e = c([c([numst(w, A0, '2', 'CC'), c([lntr], 'recnd', '%s e. CC' % LNT)], 'sqmuld', '( ( 2 x. %s ) ^ 2 ) = ( ( 2 ^ 2 ) x. ( %s ^ 2 ) )' % (LNT, LNT)),
             c([c.a1(w.s([], 'sq2', '( 2 ^ 2 ) = 4'), '( 2 ^ 2 ) = 4')], 'oveq1d', '( ( 2 ^ 2 ) x. ( %s ^ 2 ) ) = ( 4 x. ( %s ^ 2 ) )' % (LNT, LNT))], 'eqtrd', '( ( 2 x. %s ) ^ 2 ) = ( 4 x. ( %s ^ 2 ) )' % (LNT, LNT))
    sq_b = c([sq_b0, s2e], 'breqtrd', '( %s ^ 2 ) <_ ( 4 x. ( %s ^ 2 ) )' % (LN4, LNT))
    lsq = c([lnyr], 'resqcld', '( %s ^ 2 ) e. RR' % LNY)
    lvs = dict(lvl); lvs['( %s ^ 2 )' % LNY] = lsq
    yy = lin8(w, A0, [lny1], '%s <_ ( %s ^ 2 )' % (LNY, LNY), {LNY: lnyr}, products=True)
    sq_c = lin8(w, A0, [ly, yy], '%s <_ ( %s ^ 2 )' % (L_, LNY), lvs)
    sq_d = lin8(w, A0, [l4y, yy], '%s <_ ( %s ^ 2 )' % (LN4, LNY), lvs)
    YS, Y58, YC = '( Y ^c S )', '( Y ^c ( 5 / 8 ) )', '( Y ^c %s )' % C1
    ys = c([s58, c([yr, f['y1'], sr, numst(w, A0, '( 5 / 8 )', 'RR')], 'cxpled', '( S <_ ( 5 / 8 ) <-> %s <_ %s )' % (YS, Y58))], 'mpbid', '%s <_ %s' % (YS, Y58))
    yc3 = c([c([c([yr, f['y1']], 'jca', '( Y e. RR /\\ 1 < Y )'), w.inst('ef1yc')], 'syl', ante_of(stmt('ef1yc'))[1]), w.inst('simpr')], 'syl', '%s <_ ( 3 x. Y )' % YC)
    # the edges
    IT = '( 1 / T )'
    YIT = '( Y x. %s )' % IT
    itp = c([tp], 'rpreccld', '%s e. RR+' % IT)
    yit0 = c([yr, R(IT), lin8(w, A0, [y100], '0 <_ Y', lv), c([itp], 'rpge0d', '0 <_ %s' % IT)], 'mulge0d', '0 <_ %s' % YIT)
    divr = lambda X: c([c([R(X)], 'recnd', '%s e. CC' % X), c([tp], 'rpcnd', 'T e. CC'), c([tp], 'rpne0d', 'T =/= 0')], 'divrecd', '( %s / T ) = ( %s x. %s )' % (X, X, IT))
    catoms = {LN4: ln4r, LNT: lntr, LNY: lnyr, L_: lr, IT: R(IT), 'Y': yr, YS: R(YS), Y58: R(Y58), YC: R(YC)}
    CA = Closure(w, A0, {k: ('RR', v) for k, v in catoms.items()})
    for k in catoms:
        CA.atom(k)
    P1b = '( ( %s ^ 2 ) x. %s )' % (LNY, YIT)
    p1e = c([divr('( Y x. ( %s ^ 2 ) )' % LNY), ringeq(w, A0, '( ( Y x. ( %s ^ 2 ) ) x. %s )' % (LNY, IT), P1b, CA)], 'eqtrd', '%s = %s' % (P1, P1b))
    K2 = '( %s x. ( %s ^ 2 ) )' % (KGH, LN4)
    k2r = R(K2)
    k20 = c([numst(w, A0, KGH, 'RR'), R('( %s ^ 2 )' % LN4), lin8(w, A0, [], '0 <_ %s' % KGH, {}), c([ln4r], 'sqge0d', '0 <_ ( %s ^ 2 )' % LN4)], 'mulge0d', '0 <_ %s' % K2)
    kt0 = c([k2r, tp, k20], 'divge0d', '0 <_ ( %s / T )' % K2)
    ycp = c([f['yp'], f['c1r']], 'rpcxpcld', '%s e. RR+' % YC)
    h1 = c([numst(w, A0, '4', 'RR+'), f['lp'], R(YC), c([ycp], 'rpge0d', '0 <_ %s' % YC), f['l4']], 'lediv2ad', '( %s / %s ) <_ ( %s / 4 )' % (YC, L_, YC))
    h2 = c([R(YC), R('( 3 x. Y )'), numst(w, A0, '4', 'RR+'), yc3], 'lediv1dd', '( %s / 4 ) <_ ( ( 3 x. Y ) / 4 )' % YC)
    h3 = le_tr(w, A0, h1, '( %s / %s )' % (YC, L_), '( %s / 4 )' % YC, h2, '( ( 3 x. Y ) / 4 )')
    h4 = c([R('( %s / %s )' % (YC, L_)), R('( ( 3 x. Y ) / 4 )'), R('( %s / T )' % K2), kt0, h3], 'lemul2ad', '%s <_ ( ( %s / T ) x. ( ( 3 x. Y ) / 4 ) )' % (HB, K2))
    HBb = '( ( %s / T ) x. ( ( 3 x. Y ) / 4 ) )' % K2
    h5 = c([c([divr(K2)], 'oveq1d', '%s = ( ( %s x. %s ) x. ( ( 3 x. Y ) / 4 ) )' % (HBb, K2, IT)), ringeq(w, A0, '( ( %s x. %s ) x. ( ( 3 x. Y ) / 4 ) )' % (K2, IT), '( ; ; ; ; ; ; ; 1 5 7 5 0 0 0 0 x. ( ( %s ^ 2 ) x. %s ) )' % (LN4, YIT), CA)], 'eqtrd',
            '%s = ( ; ; ; ; ; ; ; 1 5 7 5 0 0 0 0 x. ( ( %s ^ 2 ) x. %s ) )' % (HBb, LN4, YIT))
    q4 = c([R('( %s ^ 2 )' % LN4), R('( %s ^ 2 )' % LNY), R(YIT), yit0, sq_a], 'lemul1ad', '( ( %s ^ 2 ) x. %s ) <_ %s' % (LN4, YIT, P1b))
    RBb = '( 8 x. ( %s x. %s ) )' % (L_, YIT)
    r1 = c([c([divr('( Y x. %s )' % L_)], 'oveq2d', '%s = ( 8 x. ( ( Y x. %s ) x. %s ) )' % (RB, L_, IT)), ringeq(w, A0, '( 8 x. ( ( Y x. %s ) x. %s ) )' % (L_, IT), RBb, CA)], 'eqtrd', '%s = %s' % (RB, RBb))
    r2 = c([lr, R('( %s ^ 2 )' % LNY), R(YIT), yit0, sq_c], 'lemul1ad', '( %s x. %s ) <_ %s' % (L_, YIT, P1b))
    lb1 = c([R(YS), R(Y58), R('( %s ^ 2 )' % LN4), R('( 4 x. ( %s ^ 2 ) )' % LNT), c([c([f['yp'], sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpge0d', '0 <_ %s' % YS),
             c([ln4r], 'sqge0d', '0 <_ ( %s ^ 2 )' % LN4), ys, sq_b], 'lemul12ad', '( %s x. ( %s ^ 2 ) ) <_ ( %s x. ( 4 x. ( %s ^ 2 ) ) )' % (YS, LN4, Y58, LNT))
    z2e = c([c([divr(LN4)], 'oveq2d', '( ( %s x. Y ) x. ( %s / T ) ) = ( ( %s x. Y ) x. ( %s x. %s ) )' % (KB, LN4, KB, LN4, IT)), ringeq(w, A0, '( ( %s x. Y ) x. ( %s x. %s ) )' % (KB, LN4, IT), '( %s x. ( %s x. %s ) )' % (KB, LN4, YIT), CA)], 'eqtrd',
            '( ( %s x. Y ) x. ( %s / T ) ) = ( %s x. ( %s x. %s ) )' % (KB, LN4, KB, LN4, YIT))
    z2 = c([ln4r, R('( %s ^ 2 )' % LNY), R(YIT), yit0, sq_d], 'lemul1ad', '( %s x. %s ) <_ %s' % (LN4, YIT, P1b))
    z1 = c([R(YS), R(Y58), R('( %s ^ 2 )' % LNT), c([lntr], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNT), ys], 'lemul1ad', '( %s x. ( %s ^ 2 ) ) <_ ( %s x. ( %s ^ 2 ) )' % (YS, LNT, Y58, LNT))
    # linear combination: A <_ 2040000000 Q, B <_ 73600 Q
    Q = '( %s + %s )' % (P1, P2)
    atoms = {HB: R(HB), RB: R(RB), LB: R(LB), P1: R(P1), P2: R(P2), P1b: R(P1b), 'A': ar, 'B': br, YS: R(YS), Y58: R(Y58), LNT: lntr, LN4: ln4r, YIT: R(YIT), L_: lr,
             '( ( %s ^ 2 ) x. %s )' % (LN4, YIT): R('( ( %s ^ 2 ) x. %s )' % (LN4, YIT)), '( %s x. %s )' % (L_, YIT): R('( %s x. %s )' % (L_, YIT)), '( %s x. %s )' % (LN4, YIT): R('( %s x. %s )' % (LN4, YIT)),
             '( %s x. ( %s ^ 2 ) )' % (YS, LN4): R('( %s x. ( %s ^ 2 ) )' % (YS, LN4)), '( %s x. ( %s ^ 2 ) )' % (YS, LNT): R('( %s x. ( %s ^ 2 ) )' % (YS, LNT)),
             '( %s x. ( %s ^ 2 ) )' % (Y58, LNT): R('( %s x. ( %s ^ 2 ) )' % (Y58, LNT))}
    p10 = c([R('( Y x. ( %s ^ 2 ) )' % LNY), tp, c([yr, R('( %s ^ 2 )' % LNY), lin8(w, A0, [y100], '0 <_ Y', lv), c([lnyr], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNY)], 'mulge0d', '0 <_ ( Y x. ( %s ^ 2 ) )' % LNY)], 'divge0d', '0 <_ %s' % P1)
    p20 = c([R(Y58), R('( %s ^ 2 )' % LNT), c([c([f['yp'], numst(w, A0, '( 5 / 8 )', 'RR')], 'rpcxpcld', '%s e. RR+' % Y58)], 'rpge0d', '0 <_ %s' % Y58), c([lntr], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNT)], 'mulge0d', '0 <_ %s' % P2)
    lb2 = c([numst(w, A0, KL, 'CC'), c([R(YS)], 'recnd', '%s e. CC' % YS), c([R('( %s ^ 2 )' % LN4)], 'recnd', '( %s ^ 2 ) e. CC' % LN4)], 'mulassd', '%s = ( %s x. ( %s x. ( %s ^ 2 ) ) )' % (LB, KL, YS, LN4))
    p2e = ringeq(w, A0, '( %s x. ( 4 x. ( %s ^ 2 ) ) )' % (Y58, LNT), '( 4 x. %s )' % P2, CA)
    z1e = c([numst(w, A0, '; ; ; ; 7 2 0 0 0', 'CC'), c([R(YS)], 'recnd', '%s e. CC' % YS), c([R('( %s ^ 2 )' % LNT)], 'recnd', '( %s ^ 2 ) e. CC' % LNT)], 'mulassd',
             '( ( ; ; ; ; 7 2 0 0 0 x. %s ) x. ( %s ^ 2 ) ) = ( ; ; ; ; 7 2 0 0 0 x. ( %s x. ( %s ^ 2 ) ) )' % (YS, LNT, YS, LNT))
    lvq = dict(atoms)
    lvq['( %s / T )' % LN4] = R('( %s / T )' % LN4)
    lvq['Y'] = yr
    hyps_a = [ale, h4, h5, q4, r1, r2, lb2, lb1, p2e, p1e, p10, p20]
    ea = lin8(w, A0, hyps_a, 'A <_ ( ; ; ; ; ; ; ; ; ; 4 2 0 0 0 0 0 0 0 0 x. %s )' % Q, dict(lvq, **{HBb: R(HBb), '( ( %s ^ 2 ) x. %s )' % (LN4, YIT): R('( ( %s ^ 2 ) x. %s )' % (LN4, YIT))}))
    eb = lin8(w, A0, [ble, z1e, z1, z2e, z2, p1e, p10, p20], 'B <_ ( ; ; ; ; 7 3 6 0 0 x. %s )' % Q, lvq)
    # with pi
    PI2 = '( 2 x. _pi )'
    pi2r = c.a1(w.s([w.s([], '2re', '2 e. RR'), w.s([], 'pire', '_pi e. RR')], 'remulcli', '%s e. RR' % PI2), '%s e. RR' % PI2)
    pi6 = lin8(w, A0, [c.a1(w.s([], 'pigt3', '3 < _pi'), '3 < _pi')], '6 <_ %s' % PI2, {'_pi': c.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR')})
    pi0 = lin8(w, A0, [pi6], '0 <_ %s' % PI2, {PI2: pi2r})
    qr = R(Q)
    q0 = lin8(w, A0, [p10, p20], '0 <_ %s' % Q, {P1: R(P1), P2: R(P2)})
    X1 = '( ; ; ; ; ; ; ; ; 7 0 0 0 0 0 0 0 0 x. %s )' % Q
    x10 = c([numst(w, A0, '; ; ; ; ; ; ; ; 7 0 0 0 0 0 0 0 0', 'RR'), qr, lin8(w, A0, [], '0 <_ ; ; ; ; ; ; ; ; 7 0 0 0 0 0 0 0 0', {}), q0], 'mulge0d', '0 <_ %s' % X1)
    e6 = c([numst(w, A0, '6', 'RR'), pi2r, R(X1), x10, pi6], 'lemul1ad', '( 6 x. %s ) <_ ( %s x. %s )' % (X1, PI2, X1))
    cq = Closure(w, A0, {Q: ('RR', qr)}); cq.atom(Q)
    e6b = c([ringeq(w, A0, '( ; ; ; ; ; ; ; ; ; 4 2 0 0 0 0 0 0 0 0 x. %s )' % Q, '( 6 x. %s )' % X1, cq), e6], 'eqbrtrd', '( ; ; ; ; ; ; ; ; ; 4 2 0 0 0 0 0 0 0 0 x. %s ) <_ ( %s x. %s )' % (Q, PI2, X1))
    fa = le_tr(w, A0, ea, 'A', '( ; ; ; ; ; ; ; ; ; 4 2 0 0 0 0 0 0 0 0 x. %s )' % Q, e6b, '( %s x. %s )' % (PI2, X1))
    X2 = '( ; ; ; ; 7 3 6 0 0 x. %s )' % Q
    fb = c([br, R(X2), pi2r, pi0, eb], 'lemul2ad', '( %s x. B ) <_ ( %s x. %s )' % (PI2, PI2, X2))
    sm = c([fa, fb], 'le2addd', '( A + ( %s x. B ) ) <_ ( ( %s x. %s ) + ( %s x. %s ) )' % (PI2, PI2, X1, PI2, X2))
    ad = c([c([pi2r], 'recnd', '%s e. CC' % PI2), c([R(X1)], 'recnd', '%s e. CC' % X1), c([R(X2)], 'recnd', '%s e. CC' % X2)], 'adddid', '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (PI2, X1, X2, PI2, X1, PI2, X2))
    X12 = '( %s + %s )' % (X1, X2)
    KQ = '( %s x. %s )' % (KZ, Q)
    kq = lin8(w, A0, [q0], '%s <_ %s' % (X12, KQ), {Q: qr})
    fk = c([R(X12), R(KQ), pi2r, pi0, kq], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (PI2, X12, PI2, KQ))
    fin = le_tr(w, A0, c([sm, c([ad], 'eqcomd', '( ( %s x. %s ) + ( %s x. %s ) ) = ( %s x. %s )' % (PI2, X1, PI2, X2, PI2, X12))], 'breqtrd', '( A + ( %s x. B ) ) <_ ( %s x. %s )' % (PI2, PI2, X12)),
                '( A + ( %s x. B ) )' % PI2, '( %s x. %s )' % (PI2, X12), fk, '( %s x. %s )' % (PI2, KQ))
    w.qed([fin], 'idi', S['ef6nm'])
    return run8(w)





GENS = {'ef6nm': gen_nm}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
