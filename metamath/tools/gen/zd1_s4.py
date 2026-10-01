"""Sortie ZD1: extensions: the algebra of cDet_sq_div_bMaj_le_term, Theorem A arithmetic."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import Closure, lift
import lin
lin.MAXDEG = 7


def zdcdet():
    w = W('zdcdet', "The algebra of Lean cDet_sq_div_bMaj_le_term: for c = a P E N ^c -T, b = ( 1 / N ) P ^ 2 W with P =/= 0, W > 0, "
                    "E <_ 3 W: c ^ 2 / b <_ 3 N ^c ( 1 - 2 T ) a ^ 2 E (N ^c ( 1 - 2 T ) / N = ( N ^c -T ) ^ 2).")
    ante = STATEMENTS['zdcdet'].split(' ) -> ( ( ( ( ( A x. P )')[0][2:] + ' )'
    st = mkst(w, ante)
    P1 = '( N e. NN /\\ T e. RR )'
    P2 = '( ( A e. RR /\\ ( P e. RR /\\ P =/= 0 ) ) /\\ ( E e. RR+ /\\ ( W e. RR+ /\\ E <_ ( 3 x. W ) ) ) )'
    p1 = st([], 'simpl', P1); p2 = st([], 'simpr', P2)
    nn = st([p1], 'simpld', 'N e. NN'); tr = st([p1], 'simprd', 'T e. RR')
    ap = st([p2], 'simpld', '( A e. RR /\\ ( P e. RR /\\ P =/= 0 ) )'); ew = st([p2], 'simprd', '( E e. RR+ /\\ ( W e. RR+ /\\ E <_ ( 3 x. W ) ) )')
    ar = st([ap], 'simpld', 'A e. RR'); pr = st([st([ap], 'simprd', '( P e. RR /\\ P =/= 0 )')], 'simpld', 'P e. RR')
    pne = st([st([ap], 'simprd', '( P e. RR /\\ P =/= 0 )')], 'simprd', 'P =/= 0')
    erp = st([ew], 'simpld', 'E e. RR+'); wrp = st([st([ew], 'simprd', '( W e. RR+ /\\ E <_ ( 3 x. W ) )')], 'simpld', 'W e. RR+')
    e3w = st([st([ew], 'simprd', '( W e. RR+ /\\ E <_ ( 3 x. W ) )')], 'simprd', 'E <_ ( 3 x. W )')
    nrp = st([nn], 'nnrpd', 'N e. RR+'); nc = st([nrp], 'rpcnd', 'N e. CC'); nne = st([nrp], 'rpne0d', 'N =/= 0')
    Q = '( N ^c -u T )'; NC = '( N ^c ( 1 - ( 2 x. T ) ) )'
    qrp = st([nrp, st([tr], 'renegcld', '-u T e. RR')], 'rpcxpcld', '%s e. RR+' % Q); qr = st([qrp], 'rpred', '%s e. RR' % Q)
    b1 = st([st([], '1red', '1 e. RR'), st([a1c(w, ante, '2re', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '( 1 - ( 2 x. T ) ) e. RR')
    ncrp = st([nrp, b1], 'rpcxpcld', '%s e. RR+' % NC); ncr = st([ncrp], 'rpred', '%s e. RR' % NC)
    RN = '( 1 / N )'
    rnrp = st([nrp], 'rpreccld', '%s e. RR+' % RN); rnr = st([rnrp], 'rpred', '%s e. RR' % RN)
    # Q ^ 2 = NC x. ( 1 / N )
    q2a = st([st([qrp], 'rpcnd', '%s e. CC' % Q)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (Q, Q, Q))
    tc = st([tr], 'recnd', 'T e. CC'); ntc = st([st([tr], 'renegcld', '-u T e. RR')], 'recnd', '-u T e. CC')
    q2b = st([nc, nne, ntc, ntc], 'cxpaddd', '( N ^c ( -u T + -u T ) ) = ( %s x. %s )' % (Q, Q))
    m1 = st([nc, nne, a1c(w, ante, 'ax-1cn', '1 e. CC')], 'cxpnegd', '( N ^c -u 1 ) = ( 1 / ( N ^c 1 ) )')
    m1b = st([m1, st([st([nc], 'cxp1d', '( N ^c 1 ) = N')], 'oveq2d', '( 1 / ( N ^c 1 ) ) = %s' % RN)], 'eqtrd', '( N ^c -u 1 ) = %s' % RN)
    c3 = st([nc, nne, st([b1], 'recnd', '( 1 - ( 2 x. T ) ) e. CC'), st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR')], 'recnd', '-u 1 e. CC')], 'cxpaddd',
            '( N ^c ( ( 1 - ( 2 x. T ) ) + -u 1 ) ) = ( %s x. ( N ^c -u 1 ) )' % NC)
    ex = lineq(w, ante, '( ( 1 - ( 2 x. T ) ) + -u 1 )', '( -u T + -u T )', leaves={'T': tr})
    c4 = st([st([ex], 'oveq2d', '( N ^c ( ( 1 - ( 2 x. T ) ) + -u 1 ) ) = ( N ^c ( -u T + -u T ) )'), c3], 'eqtr3d', '( N ^c ( -u T + -u T ) ) = ( %s x. ( N ^c -u 1 ) )' % NC)
    c5 = st([c4, st([m1b], 'oveq2d', '( %s x. ( N ^c -u 1 ) ) = ( %s x. %s )' % (NC, NC, RN))], 'eqtrd', '( N ^c ( -u T + -u T ) ) = ( %s x. %s )' % (NC, RN))
    Q2 = '( %s ^ 2 )' % Q
    qq = eqtr(w, ante, [q2a, st([q2b], 'eqcomd', '( %s x. %s ) = ( N ^c ( -u T + -u T ) )' % (Q, Q)), c5], None)
    # c ^ 2
    APE = '( ( A x. P ) x. E )'
    C = '( %s x. %s )' % (APE, Q)
    ac = st([ar], 'recnd', 'A e. CC'); pc = st([pr], 'recnd', 'P e. CC'); ec = st([erp], 'rpcnd', 'E e. CC'); qc = st([qrp], 'rpcnd', '%s e. CC' % Q)
    s1 = st([st([st([ac, pc], 'mulcld', '( A x. P ) e. CC'), ec], 'mulcld', '%s e. CC' % APE), qc], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. %s )' % (C, APE, Q2))
    s2 = st([st([ac, pc], 'mulcld', '( A x. P ) e. CC'), ec], 'sqmuld', '( %s ^ 2 ) = ( ( ( A x. P ) ^ 2 ) x. ( E ^ 2 ) )' % APE)
    s3 = st([ac, pc], 'sqmuld', '( ( A x. P ) ^ 2 ) = ( ( A ^ 2 ) x. ( P ^ 2 ) )')
    X4 = '( ( ( ( A ^ 2 ) x. ( P ^ 2 ) ) x. ( E ^ 2 ) ) x. %s )' % Q2
    s4 = st([st([s2, st([s3], 'oveq1d', '( ( ( A x. P ) ^ 2 ) x. ( E ^ 2 ) ) = ( ( ( A ^ 2 ) x. ( P ^ 2 ) ) x. ( E ^ 2 ) )')], 'eqtrd',
                '( %s ^ 2 ) = ( ( ( A ^ 2 ) x. ( P ^ 2 ) ) x. ( E ^ 2 ) )' % APE)], 'oveq1d', '( ( %s ^ 2 ) x. %s ) = %s' % (APE, Q2, X4))
    cc2 = st([s1, s4], 'eqtrd', '( %s ^ 2 ) = %s' % (C, X4))
    A2 = '( A ^ 2 )'; P2 = '( P ^ 2 )'; E2 = '( E ^ 2 )'
    a2r = st([ar], 'resqcld', '%s e. RR' % A2); p2r = st([pr], 'resqcld', '%s e. RR' % P2); er = st([erp], 'rpred', 'E e. RR')
    e2r = st([er], 'resqcld', '%s e. RR' % E2); q2r = st([qr], 'resqcld', '%s e. RR' % Q2)
    e2 = st([ec], 'sqvald', '%s = ( E x. E )' % E2)
    X = '( ( %s x. %s ) x. ( E x. %s ) )' % (A2, P2, Q2)
    xr = st([st([a2r, p2r], 'remulcld', '( %s x. %s ) e. RR' % (A2, P2)), st([er, q2r], 'remulcld', '( E x. %s ) e. RR' % Q2)], 'remulcld', '%s e. RR' % X)
    x0 = st([st([a2r, p2r], 'remulcld', '( %s x. %s ) e. RR' % (A2, P2)), st([er, q2r], 'remulcld', '( E x. %s ) e. RR' % Q2),
             st([a2r, p2r, st([ar], 'sqge0d', '0 <_ %s' % A2), st([pr], 'sqge0d', '0 <_ %s' % P2)], 'mulge0d', '0 <_ ( %s x. %s )' % (A2, P2)),
             st([er, q2r, st([erp], 'rpge0d', '0 <_ E'), st([qr], 'sqge0d', '0 <_ %s' % Q2)], 'mulge0d', '0 <_ ( E x. %s )' % Q2)], 'mulge0d', '0 <_ %s' % X)
    TW = '( 3 x. W )'
    m = st([er, st([litr(w, ante, '3'), st([wrp], 'rpred', 'W e. RR')], 'remulcld', '%s e. RR' % TW), xr, x0, e3w], 'lemul2ad', '( %s x. E ) <_ ( %s x. %s )' % (X, X, TW))
    lv = {A2: a2r, P2: p2r, E2: e2r, 'E': er, Q2: q2r, 'W': st([wrp], 'rpred', 'W e. RR'), NC: ncr, RN: rnr}
    at = [A2, P2, E2, Q2, NC, RN]
    X4b = '( ( ( %s x. %s ) x. ( E x. E ) ) x. %s )' % (A2, P2, Q2)
    ea = st([st([e2], 'oveq2d', '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. ( E x. E ) )' % (A2, P2, E2, A2, P2))], 'oveq1d', '%s = %s' % (X4, X4b))
    eqL = st([ea, lineq(w, ante, X4b, '( %s x. E )' % X, products=True, leaves=lv, atoms=at)], 'eqtrd', '%s = ( %s x. E )' % (X4, X))
    B = '( ( %s x. %s ) x. W )' % (RN, P2)
    R = '( 3 x. ( ( %s x. %s ) x. E ) )' % (NC, A2)
    bR = '( %s x. %s )' % (B, R)
    X6 = '( ( ( %s x. %s ) x. ( E x. ( %s x. %s ) ) ) x. %s )' % (A2, P2, NC, RN, TW)
    eqR = lineq(w, ante, bR, X6, products=True, leaves=lv, atoms=at)
    sub = st([st([st([qq], 'eqcomd', '( %s x. %s ) = %s' % (NC, RN, Q2))], 'oveq2d', '( E x. ( %s x. %s ) ) = ( E x. %s )' % (NC, RN, Q2))], 'oveq2d',
             '( ( %s x. %s ) x. ( E x. ( %s x. %s ) ) ) = %s' % (A2, P2, NC, RN, X))
    eqR2 = st([eqR, st([sub], 'oveq1d', '%s = ( %s x. %s )' % (X6, X, TW))], 'eqtrd', '%s = ( %s x. %s )' % (bR, X, TW))
    le = st([st([cc2, eqL], 'eqtrd', '( %s ^ 2 ) = ( %s x. E )' % (C, X)), st([m, st([eqR2], 'eqcomd', '( %s x. %s ) = %s' % (X, TW, bR))], 'breqtrd',
             '( %s x. E ) <_ %s' % (X, bR))], 'eqbrtrd', '( %s ^ 2 ) <_ %s' % (C, bR))
    brp = st([st([rnrp, st([p2r, st([pr, pne], 'sqgt0d', '0 < %s' % P2)], 'elrpd', '%s e. RR+' % P2)], 'rpmulcld',
                 '( %s x. %s ) e. RR+' % (RN, P2)), wrp], 'rpmulcld', '%s e. RR+' % B)
    cr = st([st([st([st([ar, pr], 'remulcld', '( A x. P ) e. RR'), er], 'remulcld', '%s e. RR' % APE), qr], 'remulcld', '%s e. RR' % C)], 'resqcld', '( %s ^ 2 ) e. RR' % C)
    rr = st([litr(w, ante, '3'), st([st([ncr, a2r], 'remulcld', '( %s x. %s ) e. RR' % (NC, A2)), er], 'remulcld', '( ( %s x. %s ) x. E ) e. RR' % (NC, A2))], 'remulcld',
            '%s e. RR' % R)
    bi = st([cr, rr, brp], 'ledivmuld', '( ( ( %s ^ 2 ) / %s ) <_ %s <-> ( %s ^ 2 ) <_ ( %s x. %s ) )' % (C, B, R, C, B, R))
    w.qed([le, bi], 'mpbird', STATEMENTS['zdcdet'])
    return w


def zdd2e():
    w = W('zdd2e', "D ^c ( ( 5 / 2 ) ( 1 - S ) ) <_ 2 E ^c ( ( 9 / 2 ) ( 1 - S ) ) for D <_ 2 E, E >_ 1, 99 / 100 <_ S <_ 1 "
                   "(Lean logfree_of_logged_of_mertens, hD2E).")
    ante = STATEMENTS['zdd2e'].split(' ) -> ( D ^c')[0][2:] + ' )'
    st = mkst(w, ante)
    P1 = '( D e. RR+ /\\ E e. RR )'
    P2 = '( ( 1 <_ E /\\ D <_ ( 2 x. E ) ) /\\ ( S e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 ) ) )'
    p1 = st([], 'simpl', P1); p2 = st([], 'simpr', P2)
    drp = st([p1], 'simpld', 'D e. RR+'); er = st([p1], 'simprd', 'E e. RR')
    q = st([p2], 'simpld', '( 1 <_ E /\\ D <_ ( 2 x. E ) )'); e1 = st([q], 'simpld', '1 <_ E'); d2e = st([q], 'simprd', 'D <_ ( 2 x. E )')
    ss_ = st([p2], 'simprd', '( S e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 ) )')
    sr = st([ss_], 'simpld', 'S e. RR'); s99 = st([st([ss_], 'simprd', '( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 )')], 'simpld', '( ; 9 9 / ; ; 1 0 0 ) <_ S')
    s1 = st([st([ss_], 'simprd', '( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 )')], 'simprd', 'S <_ 1')
    X5 = '( ( 5 / 2 ) x. ( 1 - S ) )'; X9 = '( ( 9 / 2 ) x. ( 1 - S ) )'
    oms = st([st([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR')
    x5r = st([litr(w, ante, '( 5 / 2 )'), oms], 'remulcld', '%s e. RR' % X5); x9r = st([litr(w, ante, '( 9 / 2 )'), oms], 'remulcld', '%s e. RR' % X9)
    x50 = linarith(w, ante, [s1], '0 <_ %s' % X5, leaves={'S': sr})
    erp = st([er, linarith(w, ante, [e1], '0 < E', leaves={'E': er})], 'elrpd', 'E e. RR+')
    TE = '( 2 x. E )'
    ter = st([a1c(w, ante, '2re', '2 e. RR'), er], 'remulcld', '%s e. RR' % TE)
    a = st([st([drp], 'rpred', 'D e. RR'), st([drp], 'rpge0d', '0 <_ D'), ter, x5r, x50, d2e], 'cxple2ad', '( D ^c %s ) <_ ( %s ^c %s )' % (X5, TE, X5))
    b = st([a1c(w, ante, '2re', '2 e. RR'), litle(w, ante, '0', '2'), er, st([erp], 'rpge0d', '0 <_ E'), st([x5r], 'recnd', '%s e. CC' % X5)], 'mulcxpd',
           '( %s ^c %s ) = ( ( 2 ^c %s ) x. ( E ^c %s ) )' % (TE, X5, X5, X5))
    c2 = st([a1c(w, ante, '2re', '2 e. RR'), a1c(w, ante, '1le2', '1 <_ 2'), x5r, st([], '1red', '1 e. RR'), linarith(w, ante, [s99], '%s <_ 1' % X5, leaves={'S': sr})],
            'cxplead', '( 2 ^c %s ) <_ ( 2 ^c 1 )' % X5)
    c3 = st([c2, st([a1c(w, ante, '2cn', '2 e. CC')], 'cxp1d', '( 2 ^c 1 ) = 2')], 'breqtrd', '( 2 ^c %s ) <_ 2' % X5)
    ce = st([er, e1, x5r, x9r, linarith(w, ante, [s1], '%s <_ %s' % (X5, X9), leaves={'S': sr})], 'cxplead', '( E ^c %s ) <_ ( E ^c %s )' % (X5, X9))
    t2 = st([st([a1c(w, ante, '2rp', '2 e. RR+'), x5r], 'rpcxpcld', '( 2 ^c %s ) e. RR+' % X5)], 'rpred', '( 2 ^c %s ) e. RR' % X5)
    t20 = st([st([a1c(w, ante, '2rp', '2 e. RR+'), x5r], 'rpcxpcld', '( 2 ^c %s ) e. RR+' % X5)], 'rpge0d', '0 <_ ( 2 ^c %s )' % X5)
    ex5 = st([st([erp, x5r], 'rpcxpcld', '( E ^c %s ) e. RR+' % X5)], 'rpred', '( E ^c %s ) e. RR' % X5)
    ex50 = st([st([erp, x5r], 'rpcxpcld', '( E ^c %s ) e. RR+' % X5)], 'rpge0d', '0 <_ ( E ^c %s )' % X5)
    ex9 = st([st([erp, x9r], 'rpcxpcld', '( E ^c %s ) e. RR+' % X9)], 'rpred', '( E ^c %s ) e. RR' % X9)
    m = st([t2, a1c(w, ante, '2re', '2 e. RR'), ex5, ex9, t20, ex50, c3, ce], 'lemul12ad', '( ( 2 ^c %s ) x. ( E ^c %s ) ) <_ ( 2 x. ( E ^c %s ) )' % (X5, X5, X9))
    c_1 = st([st([drp, x5r], 'rpcxpcld', '( D ^c %s ) e. RR+' % X5)], 'rpred', '( D ^c %s ) e. RR' % X5)
    c_2 = st([st([st([a1c(w, ante, '2rp', '2 e. RR+'), erp], 'rpmulcld', '%s e. RR+' % TE), x5r], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (TE, X5))], 'rpred', '( %s ^c %s ) e. RR' % (TE, X5))
    c_3 = st([a1c(w, ante, '2re', '2 e. RR'), ex9], 'remulcld', '( 2 x. ( E ^c %s ) ) e. RR' % X9)
    w.qed([c_1, c_2, c_3, a, st([b, m], 'eqbrtrd', '( %s ^c %s ) <_ ( 2 x. ( E ^c %s ) )' % (TE, X5, X9))], 'letrd', STATEMENTS['zdd2e'])
    return w


def zdsqabs():
    w = W('zdsqabs', "1120 t d log ( d ( t + 2 ) ) <_ 1120 ( d ( t + 2 ) ) ^ 2 for d >_ 1, t >_ 1 (the arithmetic of Lean sum_zeroCountBox_le_sq).")
    ante = '( N e. NN /\\ ( T e. RR /\\ 1 <_ T ) )'
    st = mkst(w, ante)
    nn = st([], 'simpl', 'N e. NN'); tr = st([st([], 'simpr', '( T e. RR /\\ 1 <_ T )')], 'simpld', 'T e. RR'); t1 = st([st([], 'simpr', '( T e. RR /\\ 1 <_ T )')], 'simprd', '1 <_ T')
    nr = st([nn], 'nnred', 'N e. RR'); n1 = sy(w, ante, nn, 'nnge1', '1 <_ N')
    D = '( N x. ( T + 2 ) )'
    t2r = st([tr, a1c(w, ante, '2re', '2 e. RR')], 'readdcld', '( T + 2 ) e. RR')
    dr = st([nr, t2r], 'remulcld', '%s e. RR' % D)
    m = st([st([], '1red', '1 e. RR'), t2r, nr, linarith(w, ante, [n1], '0 <_ N', leaves={'N': nr}), linarith(w, ante, [t1], '1 <_ ( T + 2 )', leaves={'T': tr})],
           'lemul2ad', '( N x. 1 ) <_ %s' % D)
    d1 = linarith(w, ante, [m, n1], '1 <_ %s' % D, leaves={'N': nr, D: dr})
    L = '( log ` %s )' % D
    lr = st([st([dr, linarith(w, ante, [d1], '0 < %s' % D, leaves={D: dr})], 'elrpd', '%s e. RR+' % D)], 'relogcld', '%s e. RR' % L)
    l0 = st([dr, d1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % L)
    ll = st([dr, d1, w.inst('extrwlogle')], 'syl2anc', '%s <_ ( %s - 1 )' % (L, D))
    le = linarith(w, ante, [ll], '%s <_ %s' % (L, D), leaves={L: lr, D: dr})
    td = linarith(w, ante, [linarith(w, ante, [n1], '0 <_ N', leaves={'N': nr})], '( T x. N ) <_ %s' % D, leaves={'N': nr, 'T': tr}, products=True)
    tn0 = st([tr, nr, linarith(w, ante, [t1], '0 <_ T', leaves={'T': tr}), linarith(w, ante, [n1], '0 <_ N', leaves={'N': nr})], 'mulge0d', '0 <_ ( T x. N )')
    p = st([st([tr, nr], 'remulcld', '( T x. N ) e. RR'), dr, lr, dr, tn0, l0, td, le], 'lemul12ad', '( ( T x. N ) x. %s ) <_ ( %s x. %s )' % (L, D, D))
    linarith(w, ante, [p], STATEMENTS['zdsqabs'].split(' -> ', 1)[1][:-2], leaves={'T': tr, 'N': nr, L: lr}, products=True, name='qed')
    return w


def lsfacts(w, ante, h):
    """from h: ( ante -> HLS ): L, 200 <_ L, S, 99/100 <_ S, S <_ 1, lambda = ( 1 - S ) L real, 0 <_ lambda, lambda <_ L / 100, L e. RR+"""
    st = mkst(w, ante)
    hl = st([h], 'simpld', '( L e. RR /\\ ; ; 2 0 0 <_ L )'); hs = st([h], 'simprd', '( S e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 ) )')
    lr = st([hl], 'simpld', 'L e. RR'); l200 = st([hl], 'simprd', '; ; 2 0 0 <_ L')
    sr = st([hs], 'simpld', 'S e. RR'); s99 = st([st([hs], 'simprd', '( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 )')], 'simpld', '( ; 9 9 / ; ; 1 0 0 ) <_ S')
    s1 = st([st([hs], 'simprd', '( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 )')], 'simprd', 'S <_ 1')
    oms = st([st([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR')
    lamr = st([oms, lr], 'remulcld', '%s e. RR' % LAMZ)
    l0 = linarith(w, ante, [l200], '0 <_ L', leaves={'L': lr})
    om0 = linarith(w, ante, [s1], '0 <_ ( 1 - S )', leaves={'S': sr})
    lam0 = st([oms, lr, om0, l0], 'mulge0d', '0 <_ %s' % LAMZ)
    m = st([oms, litr(w, ante, '( 1 / ; ; 1 0 0 )'), lr, l0, linarith(w, ante, [s99], '( 1 - S ) <_ ( 1 / ; ; 1 0 0 )', leaves={'S': sr})], 'lemul1ad',
           '%s <_ ( ( 1 / ; ; 1 0 0 ) x. L )' % LAMZ)
    lrp = st([lr, linarith(w, ante, [l200], '0 < L', leaves={'L': lr})], 'elrpd', 'L e. RR+')
    return dict(lr=lr, l200=l200, sr=sr, s99=s99, s1=s1, oms=oms, lamr=lamr, lam0=lam0, lam100=m, l0=l0, lrp=lrp)


def zdzc1():
    w = W('zdzc1', "Theorem Z, band (b), first case (Lean zeroCountBox_one_le_density_of_mertens, hcase): with lambda = ( 1 - S ) L, "
                   "lambda ^ 2 <_ L and the band thresholds: Lambda0 + 3 <_ L and ( 1 - S ) log L <_ c.")
    from cl import split_imp
    ante = split_imp(STATEMENTS['zdzc1'])[0]
    st = mkst(w, ante)
    TH = '( ( ( log ` L ) <_ ( L / 4 ) /\\ ( ( log ` L ) ^ 2 ) <_ ( ( A ^ 2 ) x. L ) /\\ ( C + 3 ) <_ ( L / 2 ) ) /\\ ( %s ^ 2 ) <_ L )' % LAMZ
    R2 = '( ( A e. RR+ /\\ C e. RR ) /\\ %s )' % TH
    h = st([], 'simpl', HLS); r2 = st([], 'simpr', R2)
    f = lsfacts(w, ante, h)
    ac = st([r2], 'simpld', '( A e. RR+ /\\ C e. RR )'); th = st([r2], 'simprd', TH)
    arp = st([ac], 'simpld', 'A e. RR+'); cr = st([ac], 'simprd', 'C e. RR'); ar = st([arp], 'rpred', 'A e. RR')
    t3 = st([th], 'simpld', '( ( log ` L ) <_ ( L / 4 ) /\\ ( ( log ` L ) ^ 2 ) <_ ( ( A ^ 2 ) x. L ) /\\ ( C + 3 ) <_ ( L / 2 ) )')
    ha = st([t3], 'simp1d', '( log ` L ) <_ ( L / 4 )'); hb = st([t3], 'simp2d', '( ( log ` L ) ^ 2 ) <_ ( ( A ^ 2 ) x. L )'); hc = st([t3], 'simp3d', '( C + 3 ) <_ ( L / 2 )')
    hd = st([th], 'simprd', '( %s ^ 2 ) <_ L' % LAMZ)
    LG = '( log ` L )'; lgr = st([f['lrp']], 'relogcld', '%s e. RR' % LG)
    # lambda <_ 5 L / 24
    Q = '( ( 5 / ; 2 4 ) x. L )'
    qr = st([litr(w, ante, '( 5 / ; 2 4 )'), f['lr']], 'remulcld', '%s e. RR' % Q)
    q0 = linarith(w, ante, [f['l200']], '0 <_ %s' % Q, leaves={'L': f['lr']})
    ll = st([litr(w, ante, '; ; 2 0 0'), f['lr'], f['lr'], f['l0'], f['l200']], 'lemul1ad', '( ; ; 2 0 0 x. L ) <_ ( L x. L )')
    lq = linarith(w, ante, [hd, ll, f['l0']], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LAMZ, Q), leaves={'L': f['lr'], LAMZ: f['lamr']}, products=True, atoms=[LAMZ])
    bi = st([bind(w, ante, f['lamr'], f['lam0'], '%s e. RR' % LAMZ, '0 <_ %s' % LAMZ), bind(w, ante, qr, q0, '%s e. RR' % Q, '0 <_ %s' % Q), w.inst('le2sq')], 'syl2anc',
            '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (LAMZ, Q, LAMZ, Q))
    l524 = st([lq, bi], 'mpbird', '%s <_ %s' % (LAMZ, Q))
    g1 = linarith(w, ante, [ha, hc, l524], '( %s + 3 ) <_ L' % LAM0, leaves={LG: lgr, 'L': f['lr'], 'C': cr, 'S': f['sr']}, products=True)
    # ( lambda log L ) ^ 2 <_ ( A L ) ^ 2
    lg0 = st([f['lr'], linarith(w, ante, [f['l200']], '1 <_ L', leaves={'L': f['lr']}), w.inst('logge0')], 'syl2anc', '0 <_ %s' % LG)
    m = st([st([f['lamr']], 'resqcld', '( %s ^ 2 ) e. RR' % LAMZ), f['lr'], st([lgr], 'resqcld', '( %s ^ 2 ) e. RR' % LG),
            st([st([ar], 'resqcld', '( A ^ 2 ) e. RR'), f['lr']], 'remulcld', '( ( A ^ 2 ) x. L ) e. RR'),
            st([f['lamr']], 'sqge0d', '0 <_ ( %s ^ 2 )' % LAMZ), st([lgr], 'sqge0d', '0 <_ ( %s ^ 2 )' % LG), hd, hb], 'lemul12ad',
           '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) <_ ( L x. ( ( A ^ 2 ) x. L ) )' % (LAMZ, LG))
    LL = '( %s x. %s )' % (LAMZ, LG); AL = '( A x. L )'
    llr = st([f['lamr'], lgr], 'remulcld', '%s e. RR' % LL); alr = st([ar, f['lr']], 'remulcld', '%s e. RR' % AL)
    e1 = st([st([f['lamr']], 'recnd', '%s e. CC' % LAMZ), st([lgr], 'recnd', '%s e. CC' % LG)], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (LL, LAMZ, LG))
    e2a = st([st([st([st([ar], 'recnd', 'A e. CC')], 'sqvald', '( A ^ 2 ) = ( A x. A )')], 'oveq1d', '( ( A ^ 2 ) x. L ) = ( ( A x. A ) x. L )')], 'oveq2d',
             '( L x. ( ( A ^ 2 ) x. L ) ) = ( L x. ( ( A x. A ) x. L ) )')
    e2b = lineq(w, ante, '( L x. ( ( A x. A ) x. L ) )', '( %s x. %s )' % (AL, AL), products=True, leaves={'A': ar, 'L': f['lr']})
    e2c = st([st([st([alr], 'recnd', '%s e. CC' % AL)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (AL, AL, AL))], 'eqcomd', '( %s x. %s ) = ( %s ^ 2 )' % (AL, AL, AL))
    e2 = eqtr(w, ante, [e2a, e2b, e2c], None)
    sq = st([st([e1, m], 'eqbrtrd', '( %s ^ 2 ) <_ ( L x. ( ( A ^ 2 ) x. L ) )' % LL), e2], 'breqtrd', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LL, AL))
    bi2 = st([bind(w, ante, llr, st([f['lamr'], lgr, f['lam0'], lg0], 'mulge0d', '0 <_ %s' % LL), '%s e. RR' % LL, '0 <_ %s' % LL),
              bind(w, ante, alr, st([ar, f['lr'], st([arp], 'rpge0d', '0 <_ A'), f['l0']], 'mulge0d', '0 <_ %s' % AL), '%s e. RR' % AL, '0 <_ %s' % AL), w.inst('le2sq')],
             'syl2anc', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (LL, AL, LL, AL))
    la = st([sq, bi2], 'mpbird', '%s <_ %s' % (LL, AL))
    OL = '( ( 1 - S ) x. %s )' % LG
    la2 = st([lineq(w, ante, '( %s x. L )' % OL, LL, products=True, leaves={'S': f['sr'], 'L': f['lr'], LG: lgr}), la], 'eqbrtrd', '( %s x. L ) <_ %s' % (OL, AL))
    bi3 = st([st([f['oms'], lgr], 'remulcld', '%s e. RR' % OL), ar, f['lrp']], 'lemul1d', '( %s <_ A <-> ( %s x. L ) <_ %s )' % (OL, OL, AL))
    g2 = st([la2, bi3], 'mpbird', '%s <_ A' % OL)
    w.qed([g1, g2], 'jca', STATEMENTS['zdzc1'])
    return w


def zdzc2():
    w = W('zdzc2', "Theorem Z, band (b), second case (Lean zeroCountBox_one_le_density_of_mertens, the crude count): with lambda = ( 1 - S ) L, "
                   "L < lambda ^ 2 and the band thresholds: 1 <_ Lambda0 and 1120 Lambda0 log ( Lambda0 + 2 ) <_ 1120 e ^ ( ( 5 / 2 ) lambda ) "
                   "(L ^ 2 <_ lambda ^ 4 <_ e ^ ( ( 5 / 2 ) lambda ), zdpow4).")
    from cl import split_imp
    ante = split_imp(STATEMENTS['zdzc2'])[0]
    st = mkst(w, ante)
    TH = '( ( ( log ` L ) <_ ( L / 4 ) /\\ ( C + 3 ) <_ ( L / 2 ) ) /\\ ( 1 <_ ( log ` L ) /\\ L < ( %s ^ 2 ) ) )' % LAMZ
    R2 = '( ( C e. RR /\\ 0 <_ C ) /\\ %s )' % TH
    h = st([], 'simpl', HLS); r2 = st([], 'simpr', R2)
    f = lsfacts(w, ante, h)
    cc_ = st([r2], 'simpld', '( C e. RR /\\ 0 <_ C )'); th = st([r2], 'simprd', TH)
    cr = st([cc_], 'simpld', 'C e. RR'); c0 = st([cc_], 'simprd', '0 <_ C')
    ta = st([th], 'simpld', '( ( log ` L ) <_ ( L / 4 ) /\\ ( C + 3 ) <_ ( L / 2 ) )'); tb = st([th], 'simprd', '( 1 <_ ( log ` L ) /\\ L < ( %s ^ 2 ) )' % LAMZ)
    ha = st([ta], 'simpld', '( log ` L ) <_ ( L / 4 )'); hc = st([ta], 'simprd', '( C + 3 ) <_ ( L / 2 )')
    hl1 = st([tb], 'simpld', '1 <_ ( log ` L )'); hq = st([tb], 'simprd', 'L < ( %s ^ 2 )' % LAMZ)
    LG = '( log ` L )'; lgr = st([f['lrp']], 'relogcld', '%s e. RR' % LG)
    lv = {LG: lgr, 'L': f['lr'], 'C': cr, 'S': f['sr']}
    lam0r = st([st([lgr, st([litr(w, ante, '( 6 / 5 )'), f['lamr']], 'remulcld', '( ( 6 / 5 ) x. %s ) e. RR' % LAMZ)], 'readdcld',
                   '( %s + ( ( 6 / 5 ) x. %s ) ) e. RR' % (LG, LAMZ)), cr], 'readdcld', '%s e. RR' % LAM0)
    g1 = linarith(w, ante, [hl1, f['lam0'], c0], '1 <_ %s' % LAM0, leaves=lv, products=True)
    l2 = linarith(w, ante, [ha, hc, f['lam100'], f['l200']], '( %s + 2 ) <_ L' % LAM0, leaves=lv, products=True)
    L2 = '( %s + 2 )' % LAM0
    l2r = st([lam0r, a1c(w, ante, '2re', '2 e. RR')], 'readdcld', '%s e. RR' % L2)
    l21 = linarith(w, ante, [g1], '1 <_ %s' % L2, leaves=lv, products=True)
    lg2 = st([l2r, l21, w.inst('extrwlogle')], 'syl2anc', '( log ` %s ) <_ ( %s - 1 )' % (L2, L2))
    LG2 = '( log ` %s )' % L2
    lg2r = st([st([l2r, linarith(w, ante, [l21], '0 < %s' % L2, leaves={L2: l2r})], 'elrpd', '%s e. RR+' % L2)], 'relogcld', '%s e. RR' % LG2)
    lg2l = linarith(w, ante, [lg2, l2], '%s <_ L' % LG2, leaves=dict(lv, **{LG2: lg2r}), products=True)
    lg20 = st([l2r, l21, w.inst('logge0')], 'syl2anc', '0 <_ %s' % LG2)
    ll = linarith(w, ante, [l2], '%s <_ L' % LAM0, leaves=lv, products=True)
    m = st([lam0r, f['lr'], lg2r, f['lr'], linarith(w, ante, [g1], '0 <_ %s' % LAM0, leaves=lv, products=True), lg20, ll, lg2l], 'lemul12ad',
           '( %s x. %s ) <_ ( L x. L )' % (LAM0, LG2))
    # L ^ 2 <_ lambda ^ 4 <_ e ^ ( ( 5 / 2 ) lambda )
    lsq = w.s([bind(w, ante, f['lr'], f['l0'], 'L e. RR', '0 <_ L'), bind(w, ante, st([f['lamr']], 'resqcld', '( %s ^ 2 ) e. RR' % LAMZ), st([hq], 'ltled', 'L <_ ( %s ^ 2 )' % LAMZ),
                                                                     '( %s ^ 2 ) e. RR' % LAMZ, 'L <_ ( %s ^ 2 )' % LAMZ), w.inst('le2sq2')], 'syl2anc',
              '( %s -> ( L ^ 2 ) <_ ( ( %s ^ 2 ) ^ 2 ) )' % (ante, LAMZ))
    p4 = st([f['lamr'], f['lam0'], w.inst('zdpow4')], 'syl2anc', '( %s ^ 4 ) <_ ( exp ` ( ( 5 / 2 ) x. %s ) )' % (LAMZ, LAMZ))
    ex = '( exp ` ( ( 5 / 2 ) x. %s ) )' % LAMZ
    exr = st([st([litr(w, ante, '( 5 / 2 )'), f['lamr']], 'remulcld', '( ( 5 / 2 ) x. %s ) e. RR' % LAMZ)], 'reefcld', '%s e. RR' % ex)
    c2 = st([st([st([f['lr']], 'recnd', 'L e. CC')], 'sqvald', '( L ^ 2 ) = ( L x. L )')], 'eqcomd', '( L x. L ) = ( L ^ 2 )')
    l4 = '( %s ^ 4 )' % LAMZ
    c4 = st([st([f['lamr']], 'recnd', '%s e. CC' % LAMZ), a1c(w, ante, '2nn0', '2 e. NN0'), a1c(w, ante, '2nn0', '2 e. NN0')], 'expmuld',
            '( %s ^ ( 2 x. 2 ) ) = ( ( %s ^ 2 ) ^ 2 )' % (LAMZ, LAMZ))
    c4b = st([st([a1c(w, ante, '2t2e4', '( 2 x. 2 ) = 4')], 'oveq2d', '( %s ^ ( 2 x. 2 ) ) = %s' % (LAMZ, l4)), c4], 'eqtr3d', '%s = ( ( %s ^ 2 ) ^ 2 )' % (l4, LAMZ))
    k1 = st([m, c2], 'breqtrd', '( %s x. %s ) <_ ( L ^ 2 )' % (LAM0, LG2))
    lsqr = st([f['lr']], 'resqcld', '( L ^ 2 ) e. RR')
    l22 = st([st([f['lamr']], 'resqcld', '( %s ^ 2 ) e. RR' % LAMZ)], 'resqcld', '( ( %s ^ 2 ) ^ 2 ) e. RR' % LAMZ)
    pr_ = st([lam0r, lg2r], 'remulcld', '( %s x. %s ) e. RR' % (LAM0, LG2))
    k2 = st([pr_, lsqr, l22, k1, lsq], 'letrd', '( %s x. %s ) <_ ( ( %s ^ 2 ) ^ 2 )' % (LAM0, LG2, LAMZ))
    k3 = st([k2, st([c4b], 'eqcomd', '( ( %s ^ 2 ) ^ 2 ) = %s' % (LAMZ, l4))], 'breqtrd', '( %s x. %s ) <_ %s' % (LAM0, LG2, l4))
    k4 = st([pr_, st([f['lamr'], a1c(w, ante, '4nn0', '4 e. NN0')], 'reexpcld', '%s e. RR' % l4), exr, k3, p4], 'letrd', '( %s x. %s ) <_ %s' % (LAM0, LG2, ex))
    k5 = st([pr_, exr, litr(w, ante, '; ; ; 1 1 2 0'), litle(w, ante, '0', '; ; ; 1 1 2 0'), k4], 'lemul2ad',
            '( ; ; ; 1 1 2 0 x. ( %s x. %s ) ) <_ ( ; ; ; 1 1 2 0 x. %s )' % (LAM0, LG2, ex))
    k6 = st([st([litr(w, ante, '; ; ; 1 1 2 0')], 'recnd', '; ; ; 1 1 2 0 e. CC'), st([lam0r], 'recnd', '%s e. CC' % LAM0), st([lg2r], 'recnd', '%s e. CC' % LG2)], 'mulassd',
            '( ( ; ; ; 1 1 2 0 x. %s ) x. %s ) = ( ; ; ; 1 1 2 0 x. ( %s x. %s ) )' % (LAM0, LG2, LAM0, LG2))
    g2 = st([k6, k5], 'eqbrtrd', '( ( ; ; ; 1 1 2 0 x. %s ) x. %s ) <_ ( ; ; ; 1 1 2 0 x. %s )' % (LAM0, LG2, ex))
    w.qed([g1, g2], 'jca', STATEMENTS['zdzc2'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
