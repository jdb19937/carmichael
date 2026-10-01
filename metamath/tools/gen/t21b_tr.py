"""Sortie T21b: t21efe (efErr_le), t21sm (small_terms_le)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from t21a_z1 import x_basics
from mvlib import ringeq as ringeq_d
import cl as _cl

L = LX


def basics(w, A0, u):
    """common facts at the level: N, X, Y, the logs"""
    s = S_(w, A0)
    nn = u['N e. NN']; xr = u['X e. RR']; xe = u['( exp ` 1 ) <_ X']; yr = u['Y e. RR']
    nx = u['N <_ ( X ^c %s )' % F191]; ny = u['( N x. ( X ^c %s ) ) <_ Y' % F709]; yx = u['Y <_ X']
    b = x_basics(w, A0, xr, xe)
    nr = s([nn], 'nnred', 'N e. RR'); n1 = s([nn], 'nnge1d', '1 <_ N'); np_ = s([nn], 'nnrpd', 'N e. RR+')
    f191 = s([num.real(w, F191)], 'a1i', '%s e. RR' % F191); f709 = s([num.real(w, F709)], 'a1i', '%s e. RR' % F709)
    one = b['one']
    x191 = s([b['xp'], f191], 'rpcxpcld', '( X ^c %s ) e. RR+' % F191)
    x191l = s([xr, b['x1'], f191, one, s([num.le_lit(w, F191, '1')], 'a1i', '%s <_ 1' % F191)], 'cxplead', '( X ^c %s ) <_ ( X ^c 1 )' % F191)
    xc1 = s([s([xr], 'recnd', 'X e. CC')], 'cxp1d', '( X ^c 1 ) = X')
    nX = lin.linarith(w, A0, [nx, s([x191l, xc1], 'breqtrd', '( X ^c %s ) <_ X' % F191)], 'N <_ X', leaves={'N': nr, 'X': xr, '( X ^c %s )' % F191: s([x191], 'rpred', '( X ^c %s ) e. RR' % F191)})
    zero = s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR')
    x709a = s([xr, b['x1'], zero, f709, s([num.le_lit(w, '0', F709)], 'a1i', '0 <_ %s' % F709)], 'cxplead', '( X ^c 0 ) <_ ( X ^c %s )' % F709)
    x709 = s([s([s([s([xr], 'recnd', 'X e. CC')], 'cxp0d', '( X ^c 0 ) = 1')], 'eqcomd', '1 = ( X ^c 0 )'), x709a], 'eqbrtrd', '1 <_ ( X ^c %s )' % F709)
    X709 = '( X ^c %s )' % F709
    x709r = s([b['xp'], f709], 'rpcxpcld', '%s e. RR+' % X709)
    y1 = lin.nlinarith(w, A0, [n1, x709, ny], '1 <_ Y', leaves={'N': nr, X709: s([x709r], 'rpred', '%s e. RR' % X709), 'Y': yr})
    yp = rp_of(w, A0, yr, y1, 'Y')
    return dict(s=s, nn=nn, xr=xr, xe=xe, yr=yr, nx=nx, ny=ny, yx=yx, b=b, nr=nr, n1=n1, np=np_, f191=f191, f709=f709, nX=nX, y1=y1, yp=yp, one=one)


def level(w, A0, c, a, bb, lit):
    """( A0 -> ( N ^c a ) <_ ( ( X ^c lit ) x. ( Y ^c bb ) ) ) (t21dpow), lit the simplified exponent"""
    s = c['s']
    ar = s([num.real(w, a)], 'a1i', '%s e. RR' % a); br = s([num.real(w, bb)], 'a1i', '%s e. RR' % bb)
    EXP = '( ( %s x. ( %s - %s ) ) - ( %s x. %s ) )' % (F191, a, bb, F709, bb)
    dp = ap(w, A0, [c['xr'], c['b']['x1'], c['nr'], c['n1'], c['nx'], c['f191'], c['f709'], c['yr'], c['ny'], ar, br, s([num.le_lit(w, '0', bb)], 'a1i', '0 <_ %s' % bb),
                    s([num.le_lit(w, bb, a)], 'a1i', '%s <_ %s' % (bb, a))], 't21dpow', '( N ^c %s ) <_ ( ( X ^c %s ) x. ( Y ^c %s ) )' % (a, EXP, bb))
    eq = lin.lineq(w, A0, EXP, lit)
    return s([dp, s([s([eq], 'oveq2d', '( X ^c %s ) = ( X ^c %s )' % (EXP, lit))], 'oveq1d', '( ( X ^c %s ) x. ( Y ^c %s ) ) = ( ( X ^c %s ) x. ( Y ^c %s ) )' % (EXP, bb, lit, bb))], 'breqtrd',
             '( N ^c %s ) <_ ( ( X ^c %s ) x. ( Y ^c %s ) )' % (a, lit, bb))


def gen_efe():
    w = W('t21efe', 'Truncation at ` T = X ^ 3 ` : the three explicit-formula error terms total at most ` 75 . 10 ^ 12 log ^ 2 X Y ^ ( 5 / 8 ) <_ ( E / 9 ) Y / N ` once ` 675 . 10 ^ 12 log ^ 2 X <_ E X ^ ( 293 / 1800 ) ` (Lean ` efErr_le ` ; ~ t21dpow , ~ t21ld ).')
    A0, concl = split_imp(SB['t21efe'])
    u = unpackA(w, A0)
    c = basics(w, A0, u)
    s = c['s']; b = c['b']
    er = u['E e. RR']; e0 = u['0 < E']; h = u['( %s x. ( %s ^ 2 ) ) <_ ( E x. ( X ^c %s ) )' % (C675, L, F2931800)]
    lr = b['lr']
    xp, yp, np_ = b['xp'], c['yp'], c['np']
    x3p = s([xp, s([w.s([], '3z', '3 e. ZZ')], 'a1i', '3 e. ZZ')], 'rpexpcld', '%s e. RR+' % X3)
    NT = '( N x. %s )' % X3; NTY = '( %s x. Y )' % NT
    L1 = '( log ` %s )' % NTY
    ln = s([np_], 'relogcld', '( log ` N )'.join(['', ' e. RR'])) if False else s([np_], 'relogcld', '( log ` N ) e. RR')
    lyr = s([yp], 'relogcld', '( log ` Y ) e. RR')
    l3 = s([x3p], 'relogcld', '( log ` %s ) e. RR' % X3)
    m1 = s([s([np_, x3p], 'rpmulcld', '%s e. RR+' % NT), yp], 'relogmuld', '%s = ( ( log ` %s ) + ( log ` Y ) )' % (L1, NT))
    m2 = s([np_, x3p], 'relogmuld', '( log ` %s ) = ( ( log ` N ) + ( log ` %s ) )' % (NT, X3))
    m3 = ap(w, A0, [xp, s([w.s([], '3z', '3 e. ZZ')], 'a1i', '3 e. ZZ')], 'relogexp', '( log ` %s ) = ( 3 x. %s )' % (X3, L))
    lnx = s([c['nX'], s([np_, xp], 'logled', '( N <_ X <-> ( log ` N ) <_ %s )' % L)], 'mpbid', '( log ` N ) <_ %s' % L)
    lyx = s([c['yx'], s([yp, xp], 'logled', '( Y <_ X <-> ( log ` Y ) <_ %s )' % L)], 'mpbid', '( log ` Y ) <_ %s' % L)
    ln0 = s([c['nr'], c['n1']], 'logge0d', '0 <_ ( log ` N )'); ly0 = s([c['yr'], c['y1']], 'logge0d', '0 <_ ( log ` Y )')
    L1e = s([m1, s([m2], 'oveq1d', '( ( log ` %s ) + ( log ` Y ) ) = ( ( ( log ` N ) + ( log ` %s ) ) + ( log ` Y ) )' % (NT, X3))], 'eqtrd', '%s = ( ( ( log ` N ) + ( log ` %s ) ) + ( log ` Y ) )' % (L1, X3))
    l1r = s([s([s([np_, x3p], 'rpmulcld', '%s e. RR+' % NT), yp], 'rpmulcld', '%s e. RR+' % NTY)], 'relogcld', '%s e. RR' % L1)
    lv = {L1: l1r, '( log ` N )': ln, '( log ` Y )': lyr, '( log ` %s )' % X3: l3, L: lr}
    l1u = lin.linarith(w, A0, [L1e, m3, lnx, lyx], '%s <_ ( 5 x. %s )' % (L1, L), leaves=lv)
    l10 = lin.linarith(w, A0, [L1e, m3, ln0, ly0, b['l1']], '0 <_ %s' % L1, leaves=lv)
    L2 = '( log ` ( N x. ( %s + 2 ) ) )' % X3
    l2u = ap(w, A0, [c['xr'], b['x2'], c['nr'], c['n1'], c['nx']], 't21ld', '%s <_ ( 5 x. %s )' % (L2, L))
    T2 = '( %s + 2 )' % X3
    t2r = s([b['x3r'], s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % T2)
    NT2 = '( N x. %s )' % T2
    nt2r = s([c['nr'], t2r], 'remulcld', '%s e. RR' % NT2)
    nt21 = lin.nlinarith(w, A0, [c['n1'], b['x8']], '1 <_ %s' % NT2, leaves={'N': c['nr'], X3: b['x3r']})
    l20 = s([nt2r, nt21], 'logge0d', '0 <_ %s' % L2)
    l2r = s([s([nt2r, lin.linarith(w, A0, [nt21], '0 < %s' % NT2, leaves={NT2: nt2r})], 'elrpd', '%s e. RR+' % NT2)], 'relogcld', '%s e. RR' % L2)
    LL = '( %s ^ 2 )' % L
    llr = s([lr], 'resqcld', '%s e. RR' % LL)
    L5 = '( 5 x. %s )' % L
    l5r = s([s([w.s([], '5re', '5 e. RR')], 'a1i', '5 e. RR'), lr], 'remulcld', '%s e. RR' % L5)
    l50 = lin.linarith(w, A0, [b['l1']], '0 <_ %s' % L5, leaves={L: lr})
    s5 = s([s([s([w.s([], '5cn', '5 e. CC')], 'a1i', '5 e. CC'), s([lr], 'recnd', '%s e. CC' % L)], 'sqmuld', '( %s ^ 2 ) = ( ( 5 ^ 2 ) x. ( %s ^ 2 ) )' % (L5, L)),
            s([s([w.s([w.s([w.s([], '5cn', '5 e. CC'), w.inst('sqval')], 'ax-mp', '( 5 ^ 2 ) = ( 5 x. 5 )'), w.s([], '5t5e25', '( 5 x. 5 ) = ; 2 5')], 'eqtri', '( 5 ^ 2 ) = ; 2 5')], 'a1i', '( 5 ^ 2 ) = ; 2 5')], 'oveq1d', '( ( 5 ^ 2 ) x. ( %s ^ 2 ) ) = ( ; 2 5 x. ( %s ^ 2 ) )' % (L, L))], 'eqtrd', '( %s ^ 2 ) = ( ; 2 5 x. ( %s ^ 2 ) )' % (L5, L))
    def sqb(a, ar_, a0_, au):
        t = s([au, s([ar_, l5r, a0_, l50], 'le2sqd', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (a, L5, a, L5))], 'mpbid', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (a, L5))
        return s([t, s5], 'breqtrd', '( %s ^ 2 ) <_ ( ; 2 5 x. ( %s ^ 2 ) )' % (a, L))
    sq1 = sqb(L1, l1r, l10, l1u)
    sq2 = sqb(L2, l2r, l20, l2u)
    P = '( Y ^c ( 5 / 8 ) )'; Q = '( Y ^c ( 3 / 8 ) )'
    pp = s([yp, s([num.real(w, '( 5 / 8 )')], 'a1i', '( 5 / 8 ) e. RR')], 'rpcxpcld', '%s e. RR+' % P)
    qp = s([yp, s([num.real(w, '( 3 / 8 )')], 'a1i', '( 3 / 8 ) e. RR')], 'rpcxpcld', '%s e. RR+' % Q)
    pr = s([pp], 'rpred', '%s e. RR' % P); qr = s([qp], 'rpred', '%s e. RR' % Q)
    p1a = s([c['yr'], c['y1'], s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([num.real(w, '( 5 / 8 )')], 'a1i', '( 5 / 8 ) e. RR'), s([num.le_lit(w, '0', '( 5 / 8 )')], 'a1i', '0 <_ ( 5 / 8 )')], 'cxplead', '( Y ^c 0 ) <_ %s' % P)
    p1 = s([s([s([s([c['yr']], 'recnd', 'Y e. CC')], 'cxp0d', '( Y ^c 0 ) = 1')], 'eqcomd', '1 = ( Y ^c 0 )'), p1a], 'eqbrtrd', '1 <_ %s' % P)
    M = '( %s x. %s )' % (LL, P)
    ll0 = s([lr], 'sqge0d', '0 <_ %s' % LL)
    lm = s([llr, pr, ll0, p1], 'lemulge11d', '%s <_ %s' % (LL, M))
    mr = s([llr, pr], 'remulcld', '%s e. RR' % M)
    # Y <_ X ^ 3
    x13 = s([c['xr'], b['x1'], s([w.s([w.s([], '3nn', '3 e. NN'), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtri', '3 e. ( ZZ>= ` 1 )')], 'a1i', '3 e. ( ZZ>= ` 1 )')], 'leexp2ad', '( X ^ 1 ) <_ %s' % X3)
    xx3 = s([s([s([c['xr']], 'recnd', 'X e. CC')], 'exp1d', '( X ^ 1 ) = X'), x13], 'eqbrtrrd', 'X <_ %s' % X3)
    yT = lin.linarith(w, A0, [c['yx'], xx3], 'Y <_ %s' % X3, leaves={'Y': c['yr'], 'X': c['xr'], X3: b['x3r']})
    L1S = '( %s ^ 2 )' % L1
    l1s = s([l1r], 'resqcld', '%s e. RR' % L1S); l1s0 = s([l1r], 'sqge0d', '0 <_ %s' % L1S)
    T1 = '( ( Y x. %s ) / %s )' % (L1S, X3)
    a = s([c['yr'], b['x3r'], l1s, l1s0, yT], 'lemul1ad', '( Y x. %s ) <_ ( %s x. %s )' % (L1S, X3, L1S))
    a2 = s([s([c['yr'], l1s], 'remulcld', '( Y x. %s ) e. RR' % L1S), s([b['x3r'], l1s], 'remulcld', '( %s x. %s ) e. RR' % (X3, L1S)), x3p, a], 'lediv1dd', '%s <_ ( ( %s x. %s ) / %s )' % (T1, X3, L1S, X3))
    a3 = s([s([l1s], 'recnd', '%s e. CC' % L1S), s([x3p], 'rpcnd', '%s e. CC' % X3), s([x3p], 'rpne0d', '%s =/= 0' % X3)], 'divcan3d', '( ( %s x. %s ) / %s ) = %s' % (X3, L1S, X3, L1S))
    t1b = s([a2, a3], 'breqtrd', '%s <_ %s' % (T1, L1S))
    L2S = '( %s ^ 2 )' % L2
    l2s = s([l2r], 'resqcld', '%s e. RR' % L2S)
    T2t = '( %s x. %s )' % (P, L2S)
    t2b = s([l2s, s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR') if False else s([num.real(w, '; 2 5')], 'a1i', '; 2 5 e. RR'), llr], 'remulcld', '( ; 2 5 x. %s ) e. RR' % LL), pr, s([pp], 'rpge0d', '0 <_ %s' % P), sq2], 'lemul2ad',
            '%s <_ ( %s x. ( ; 2 5 x. %s ) )' % (T2t, P, LL))
    t1r = s([s([c['yr'], l1s], 'remulcld', '( Y x. %s ) e. RR' % L1S), x3p], 'rerpdivcld', '%s e. RR' % T1)
    t2r_ = s([pr, l2s], 'remulcld', '%s e. RR' % T2t)
    SS = '( ( %s + %s ) + %s )' % (T1, T2t, L1S)
    cl = _cl.Closure(w, A0, {})
    for k_, st_ in ((T1, t1r), (T2t, t2r_), (L1S, l1s), (LL, llr), (P, pr), (M, mr)):
        cl.leaf(k_, 'RR', st_); cl.atom(k_)
    pm = ringeq_d(w, A0, '( %s x. ( ; 2 5 x. %s ) )' % (P, LL), '( ; 2 5 x. %s )' % M, cl)
    t2c = s([t2b, pm], 'breqtrd', '%s <_ ( ; 2 5 x. %s )' % (T2t, M))
    sb = lin.linarith(w, A0, [t1b, sq1, lm, t2c], '%s <_ ( ; 7 5 x. %s )' % (SS, M), closure=cl)
    ssr = s([s([t1r, t2r_], 'readdcld', '( %s + %s ) e. RR' % (T1, T2t)), l1s], 'readdcld', '%s e. RR' % SS)
    c12 = s([num.real(w, C12)], 'a1i', '%s e. RR' % C12)
    efb = s([ssr, s([s([num.real(w, '; 7 5')], 'a1i', '; 7 5 e. RR'), mr], 'remulcld', '( ; 7 5 x. %s ) e. RR' % M), c12, s([num.ge0_nat(w, 10 ** 12)], 'a1i', '0 <_ %s' % C12), sb], 'lemul2ad',
            '%s <_ ( %s x. ( ; 7 5 x. %s ) )' % (EFERR('N', X3, 'Y'), C12, M))
    # level: N <_ X^-r Y^(3/8)
    R = '( X ^c %s )' % F2931800
    rp_ = s([xp, s([num.real(w, F2931800)], 'a1i', '%s e. RR' % F2931800)], 'rpcxpcld', '%s e. RR+' % R)
    lv1 = level(w, A0, c, '1', '( 3 / 8 )', '-u %s' % F2931800)
    n1c = s([s([c['nr']], 'recnd', 'N e. CC')], 'cxp1d', '( N ^c 1 ) = N')
    xn = s([s([xp], 'rpcnd', 'X e. CC'), s([xp], 'rpne0d', 'X =/= 0'), s([num.cc(w, F2931800)], 'a1i', '%s e. CC' % F2931800)], 'cxpnegd', '( X ^c -u %s ) = ( 1 / %s )' % (F2931800, R))
    dq = s([s([qr], 'recnd', '%s e. CC' % Q), s([rp_], 'rpcnd', '%s e. CC' % R), s([rp_], 'rpne0d', '%s =/= 0' % R)], 'divrec2d', '( %s / %s ) = ( ( 1 / %s ) x. %s )' % (Q, R, R, Q))
    lv2 = s([s([n1c], 'eqcomd', 'N = ( N ^c 1 )'), s([lv1, s([s([xn], 'oveq1d', '( ( X ^c -u %s ) x. %s ) = ( ( 1 / %s ) x. %s )' % (F2931800, Q, R, Q)), s([dq], 'eqcomd', '( ( 1 / %s ) x. %s ) = ( %s / %s )' % (R, Q, Q, R))], 'eqtrd',
                                                          '( ( X ^c -u %s ) x. %s ) = ( %s / %s )' % (F2931800, Q, Q, R))], 'breqtrd', '( N ^c 1 ) <_ ( %s / %s )' % (Q, R))], 'eqbrtrd', 'N <_ ( %s / %s )' % (Q, R))
    nrq = s([lv2, s([c['nr'], qr, rp_], 'lemuldivd', '( ( N x. %s ) <_ %s <-> N <_ ( %s / %s ) )' % (R, Q, Q, R))], 'mpbird', '( N x. %s ) <_ %s' % (R, Q))
    rr = s([rp_], 'rpred', '%s e. RR' % R)
    e0l = lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er})
    n0 = lin.linarith(w, A0, [c['n1']], '0 <_ N', leaves={'N': c['nr']})
    hk = lin.nlinarith(w, A0, [h, nrq, e0l, n0], '( ( %s x. %s ) x. N ) <_ ( E x. %s )' % (C675, LL, Q), leaves={LL: llr, 'E': er, R: rr, 'N': c['nr'], Q: qr})
    # final
    ca = s([s([c['yr']], 'recnd', 'Y e. CC'), s([yp], 'rpne0d', 'Y =/= 0'), s([num.cc(w, '( 5 / 8 )')], 'a1i', '( 5 / 8 ) e. CC'), s([num.cc(w, '( 3 / 8 )')], 'a1i', '( 3 / 8 ) e. CC')], 'cxpaddd',
           '( Y ^c ( ( 5 / 8 ) + ( 3 / 8 ) ) ) = ( %s x. %s )' % (P, Q))
    s58 = lin.lineq(w, A0, '( ( 5 / 8 ) + ( 3 / 8 ) )', '1')
    ye = s([s([s([s58], 'oveq2d', '( Y ^c ( ( 5 / 8 ) + ( 3 / 8 ) ) ) = ( Y ^c 1 )'), s([s([c['yr']], 'recnd', 'Y e. CC')], 'cxp1d', '( Y ^c 1 ) = Y')], 'eqtrd', '( Y ^c ( ( 5 / 8 ) + ( 3 / 8 ) ) ) = Y'), ca], 'eqtr3d', 'Y = ( %s x. %s )' % (P, Q))
    LHS = '( %s x. ( ; 7 5 x. %s ) )' % (C12, M)
    fin1 = lin.nlinarith(w, A0, [hk, s([pp], 'rpge0d', '0 <_ %s' % P)], '( %s x. N ) <_ ( ( E / 9 ) x. ( %s x. %s ) )' % (LHS, P, Q), leaves={LL: llr, 'E': er, 'N': c['nr'], Q: qr, P: pr})
    lhsr = s([c12, s([s([num.real(w, '; 7 5')], 'a1i', '; 7 5 e. RR'), mr], 'remulcld', '( ; 7 5 x. %s ) e. RR' % M)], 'remulcld', '%s e. RR' % LHS)
    e9r = s([er, s([num.rp_nat(w, 9)], 'a1i', '9 e. RR+')], 'rerpdivcld', '( E / 9 ) e. RR')
    pq = s([pr, qr], 'remulcld', '( %s x. %s ) e. RR' % (P, Q))
    fin2 = s([fin1, s([lhsr, s([e9r, pq], 'remulcld', '( ( E / 9 ) x. ( %s x. %s ) ) e. RR' % (P, Q)), np_], 'lemuldivd', '( ( %s x. N ) <_ ( ( E / 9 ) x. ( %s x. %s ) ) <-> %s <_ ( ( ( E / 9 ) x. ( %s x. %s ) ) / N ) )' % (LHS, P, Q, LHS, P, Q))], 'mpbid',
             '%s <_ ( ( ( E / 9 ) x. ( %s x. %s ) ) / N )' % (LHS, P, Q))
    fin3 = s([fin2, s([s([s([ye], 'eqcomd', '( %s x. %s ) = Y' % (P, Q))], 'oveq2d', '( ( E / 9 ) x. ( %s x. %s ) ) = ( ( E / 9 ) x. Y )' % (P, Q))], 'oveq1d', '( ( ( E / 9 ) x. ( %s x. %s ) ) / N ) = ( ( ( E / 9 ) x. Y ) / N )' % (P, Q))], 'breqtrd',
             '%s <_ ( ( ( E / 9 ) x. Y ) / N )' % LHS)
    efr = s([c12, ssr], 'remulcld', '%s e. RR' % EFERR('N', X3, 'Y'))
    rhr = s([s([e9r, c['yr']], 'remulcld', '( ( E / 9 ) x. Y ) e. RR'), np_], 'rerpdivcld', '( ( ( E / 9 ) x. Y ) / N ) e. RR')
    w.qed([efr, lhsr, rhr, efb, fin3], 'letrd', SB['t21efe'])
    return go(w)


def gen_sm():
    w = W('t21sm', 'Prime powers and the imprimitive cushion: ` omega ( N ) log Y + 2 sqrt Y log Y <_ ( 2 E / 27 ) Y / N ` once ` 81 log X <_ E X ^ ( 259 / 900 ) ` (Lean ` small_terms_le ` ; ~ t21dpow , ~ t21om , ~ psiapsubsqrt ).')
    A0, concl = split_imp(SB['t21sm'])
    u = unpackA(w, A0)
    c = basics(w, A0, u)
    s = c['s']; b = c['b']
    er = u['E e. RR']; e0 = u['0 < E']; h = u['( ; 8 1 x. %s ) <_ ( E x. ( X ^c %s ) )' % (L, F259900)]
    lr = b['lr']; xp, yp, np_ = b['xp'], c['yp'], c['np']
    nr = c['nr']; yr = c['yr']
    e0l = lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er})
    n0 = lin.linarith(w, A0, [c['n1']], '0 <_ N', leaves={'N': nr})
    l0 = lin.linarith(w, A0, [b['l1']], '0 <_ %s' % L, leaves={L: lr})
    LY = '( log ` Y )'
    lyr = s([yp], 'relogcld', '%s e. RR' % LY)
    ly0 = s([yr, c['y1']], 'logge0d', '0 <_ %s' % LY)
    lyx = s([c['yx'], s([yp, xp], 'logled', '( Y <_ X <-> %s <_ %s )' % (LY, L))], 'mpbid', '%s <_ %s' % (LY, L))
    OMN = OM('N')
    omr = s([s([s([c['nn'], w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OMN)], 'nn0red', '%s e. RR' % OMN)
    om0 = s([s([s([c['nn'], w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OMN)], 'nn0ge0d', '0 <_ %s' % OMN)
    omn = s([c['nn'], w.inst('t21om')], 'syl', '%s <_ N' % OMN)
    Rp = '( X ^c %s )' % F259900; S5 = '( X ^c ( ; ; 2 5 9 / ; ; 4 5 0 ) )'
    rpp = s([xp, s([num.real(w, F259900)], 'a1i', '%s e. RR' % F259900)], 'rpcxpcld', '%s e. RR+' % Rp)
    s5p = s([xp, s([num.real(w, '( ; ; 2 5 9 / ; ; 4 5 0 )')], 'a1i', '( ; ; 2 5 9 / ; ; 4 5 0 ) e. RR')], 'rpcxpcld', '%s e. RR+' % S5)
    rs = s([c['xr'], b['x1'], s([num.real(w, F259900)], 'a1i', '%s e. RR' % F259900), s([num.real(w, '( ; ; 2 5 9 / ; ; 4 5 0 )')], 'a1i', '( ; ; 2 5 9 / ; ; 4 5 0 ) e. RR'),
            lin.linarith(w, A0, [], '%s <_ ( ; ; 2 5 9 / ; ; 4 5 0 )' % F259900, leaves={})], 'cxplead', '%s <_ %s' % (Rp, S5))
    rpr = s([rpp], 'rpred', '%s e. RR' % Rp); s5r = s([s5p], 'rpred', '%s e. RR' % S5)
    # term A
    lvA = level(w, A0, c, '2', '1', '-u ( ; ; 2 5 9 / ; ; 4 5 0 )')
    n2 = ap(w, A0, [s([nr], 'recnd', 'N e. CC'), s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'cxpexp', '( N ^c 2 ) = ( N ^ 2 )')
    y1c = s([s([yr], 'recnd', 'Y e. CC')], 'cxp1d', '( Y ^c 1 ) = Y')
    xn = s([s([xp], 'rpcnd', 'X e. CC'), s([xp], 'rpne0d', 'X =/= 0'), s([num.cc(w, '( ; ; 2 5 9 / ; ; 4 5 0 )')], 'a1i', '( ; ; 2 5 9 / ; ; 4 5 0 ) e. CC')], 'cxpnegd',
           '( X ^c -u ( ; ; 2 5 9 / ; ; 4 5 0 ) ) = ( 1 / %s )' % S5)
    dq = s([s([yr], 'recnd', 'Y e. CC'), s([s5p], 'rpcnd', '%s e. CC' % S5), s([s5p], 'rpne0d', '%s =/= 0' % S5)], 'divrec2d', '( Y / %s ) = ( ( 1 / %s ) x. Y )' % (S5, S5))
    NN2 = '( N ^ 2 )'
    rhsA = s([s([xn, y1c], 'oveq12d', '( ( X ^c -u ( ; ; 2 5 9 / ; ; 4 5 0 ) ) x. ( Y ^c 1 ) ) = ( ( 1 / %s ) x. Y )' % S5), s([dq], 'eqcomd', '( ( 1 / %s ) x. Y ) = ( Y / %s )' % (S5, S5))], 'eqtrd',
             '( ( X ^c -u ( ; ; 2 5 9 / ; ; 4 5 0 ) ) x. ( Y ^c 1 ) ) = ( Y / %s )' % S5)
    lA = s([s([s([n2], 'eqcomd', '%s = ( N ^c 2 )' % NN2), lvA], 'eqbrtrd', '%s <_ ( ( X ^c -u ( ; ; 2 5 9 / ; ; 4 5 0 ) ) x. ( Y ^c 1 ) )' % NN2), rhsA], 'breqtrd', '%s <_ ( Y / %s )' % (NN2, S5))
    n2r = s([nr], 'resqcld', '%s e. RR' % NN2)
    lA2 = s([lA, s([n2r, yr, s5p], 'lemuldivd', '( ( %s x. %s ) <_ Y <-> %s <_ ( Y / %s ) )' % (NN2, S5, NN2, S5))], 'mpbird', '( %s x. %s ) <_ Y' % (NN2, S5))
    h27 = lin.nlinarith(w, A0, [h, rs, e0l, l0], '( ; 2 7 x. %s ) <_ ( E x. %s )' % (L, S5), leaves={L: lr, 'E': er, Rp: rpr, S5: s5r})
    hA = lin.nlinarith(w, A0, [h27, lA2, e0l, s([nr], 'sqge0d', '0 <_ %s' % NN2)], '( ; 2 7 x. ( %s x. %s ) ) <_ ( E x. Y )' % (NN2, L), leaves={L: lr, 'E': er, S5: s5r, NN2: n2r, 'Y': yr})
    TA = '( %s x. %s )' % (OMN, LY)
    a1 = s([omr, nr, lyr, lr, om0, ly0, omn, lyx], 'lemul12ad', '%s <_ ( N x. %s )' % (TA, L))
    # term B
    SY = '( sqrt ` Y )'
    syr = s([yr], 'resqrtcld', '%s e. RR' % SY); sy0 = s([yr], 'sqrtge0d', '0 <_ %s' % SY)
    y0 = lin.linarith(w, A0, [c['y1']], '0 <_ Y', leaves={'Y': yr})
    ss = ap(w, A0, [yr, y0], 'remsqsqrt', '( %s x. %s ) = Y' % (SY, SY))
    lvB = level(w, A0, c, '1', '( 1 / 2 )', '-u %s' % F259900)
    n1c = s([s([nr], 'recnd', 'N e. CC')], 'cxp1d', '( N ^c 1 ) = N')
    ysq = s([s([yr], 'recnd', 'Y e. CC'), w.inst('cxpsqrt')], 'syl', '( Y ^c ( 1 / 2 ) ) = %s' % SY)
    xnB = s([s([xp], 'rpcnd', 'X e. CC'), s([xp], 'rpne0d', 'X =/= 0'), s([num.cc(w, F259900)], 'a1i', '%s e. CC' % F259900)], 'cxpnegd', '( X ^c -u %s ) = ( 1 / %s )' % (F259900, Rp))
    dqB = s([s([syr], 'recnd', '%s e. CC' % SY), s([rpp], 'rpcnd', '%s e. CC' % Rp), s([rpp], 'rpne0d', '%s =/= 0' % Rp)], 'divrec2d', '( %s / %s ) = ( ( 1 / %s ) x. %s )' % (SY, Rp, Rp, SY))
    rhsB = s([s([xnB, ysq], 'oveq12d', '( ( X ^c -u %s ) x. ( Y ^c ( 1 / 2 ) ) ) = ( ( 1 / %s ) x. %s )' % (F259900, Rp, SY)), s([dqB], 'eqcomd', '( ( 1 / %s ) x. %s ) = ( %s / %s )' % (Rp, SY, SY, Rp))], 'eqtrd',
             '( ( X ^c -u %s ) x. ( Y ^c ( 1 / 2 ) ) ) = ( %s / %s )' % (F259900, SY, Rp))
    lB = s([s([s([n1c], 'eqcomd', 'N = ( N ^c 1 )'), lvB], 'eqbrtrd', 'N <_ ( ( X ^c -u %s ) x. ( Y ^c ( 1 / 2 ) ) )' % F259900), rhsB], 'breqtrd', 'N <_ ( %s / %s )' % (SY, Rp))
    lB2 = s([lB, s([nr, syr, rpp], 'lemuldivd', '( ( N x. %s ) <_ %s <-> N <_ ( %s / %s ) )' % (Rp, SY, SY, Rp))], 'mpbird', '( N x. %s ) <_ %s' % (Rp, SY))
    h54 = lin.nlinarith(w, A0, [h, lB2, e0l, n0, l0], '( ; 5 4 x. ( N x. %s ) ) <_ ( E x. %s )' % (L, SY), leaves={L: lr, 'E': er, Rp: rpr, 'N': nr, SY: syr})
    NL = '( N x. %s )' % L
    nlr = s([nr, lr], 'remulcld', '%s e. RR' % NL)
    f54 = s([num.real(w, '; 5 4')], 'a1i', '; 5 4 e. RR')
    l54 = s([f54, nlr], 'remulcld', '( ; 5 4 x. %s ) e. RR' % NL)
    esy = s([er, syr], 'remulcld', '( E x. %s ) e. RR' % SY)
    q1 = s([l54, esy, syr, sy0, h54], 'lemul1ad', '( ( ; 5 4 x. %s ) x. %s ) <_ ( ( E x. %s ) x. %s )' % (NL, SY, SY, SY))
    q2 = s([s([f54], 'recnd', '; 5 4 e. CC'), s([nlr], 'recnd', '%s e. CC' % NL), s([syr], 'recnd', '%s e. CC' % SY)], 'mulassd', '( ( ; 5 4 x. %s ) x. %s ) = ( ; 5 4 x. ( %s x. %s ) )' % (NL, SY, NL, SY))
    q3 = s([s([s([er], 'recnd', 'E e. CC'), s([syr], 'recnd', '%s e. CC' % SY), s([syr], 'recnd', '%s e. CC' % SY)], 'mulassd', '( ( E x. %s ) x. %s ) = ( E x. ( %s x. %s ) )' % (SY, SY, SY, SY)),
            s([ss], 'oveq2d', '( E x. ( %s x. %s ) ) = ( E x. Y )' % (SY, SY))], 'eqtrd', '( ( E x. %s ) x. %s ) = ( E x. Y )' % (SY, SY))
    hB = s([s([s([q2], 'eqcomd', '( ; 5 4 x. ( %s x. %s ) ) = ( ( ; 5 4 x. %s ) x. %s )' % (NL, SY, NL, SY)), q1], 'eqbrtrd', '( ; 5 4 x. ( %s x. %s ) ) <_ ( ( E x. %s ) x. %s )' % (NL, SY, SY, SY)), q3], 'breqtrd',
           '( ; 5 4 x. ( %s x. %s ) ) <_ ( E x. Y )' % (NL, SY))
    TB = SQL('Y')
    b1 = s([s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), syr], 'remulcld', '( 2 x. %s ) e. RR' % SY)], 'x', 'x')], 'x', 'x') if False else None
    t2s = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), syr], 'remulcld', '( 2 x. %s ) e. RR' % SY)
    t2s0 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), syr, s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), sy0], 'mulge0d', '0 <_ ( 2 x. %s )' % SY)
    b1 = s([lyr, lr, t2s, t2s0, lyx], 'lemul2ad', '%s <_ ( ( 2 x. %s ) x. %s )' % (TB, SY, L))
    # combine: ( ( TA + TB ) x. N ) <_ ( ( ( 2 x. E ) / 27 ) x. Y )
    tar = s([omr, lyr], 'remulcld', '%s e. RR' % TA)
    tbr = s([t2s, lyr], 'remulcld', '%s e. RR' % TB)
    B2 = '( ( 2 x. %s ) x. %s )' % (SY, L)
    b2r = s([t2s, lr], 'remulcld', '%s e. RR' % B2)
    a1n = s([tar, s([nr, lr], 'remulcld', '( N x. %s ) e. RR' % L), nr, n0, a1], 'lemul1ad', '( %s x. N ) <_ ( ( N x. %s ) x. N )' % (TA, L))
    b1n = s([tbr, b2r, nr, n0, b1], 'lemul1ad', '( %s x. N ) <_ ( %s x. N )' % (TB, B2))
    cl = _cl.Closure(w, A0, {})
    for k_, st_ in (('N', nr), (L, lr), (SY, syr), ('E', er), ('Y', yr), (TA, tar), (TB, tbr)):
        cl.leaf(k_, 'RR', st_); cl.atom(k_)
    iA = ringeq_d(w, A0, '( ( N x. %s ) x. N )' % L, '( %s x. %s )' % (NN2, L), cl) if False else None
    # identities: ( ( N x. L ) x. N ) = ( ( N ^ 2 ) x. L ) ; ( B2 x. N ) = ( 2 x. ( NL x. SY ) )
    from mvlib import ringeqp
    iA = ringeqp(w, A0, '( ( N x. %s ) x. N )' % L, '( %s x. %s )' % (NN2, L), cl)
    iB = ringeq_d(w, A0, '( %s x. N )' % B2, '( 2 x. ( %s x. %s ) )' % (NL, SY), cl)
    fin1 = lin8_(w, A0, [a1n, b1n, iA, iB, hA, hB], '( ( %s x. N ) + ( %s x. N ) ) <_ ( ( 2 / ; 2 7 ) x. ( E x. Y ) )' % (TA, TB),
                 {('%s x. N' % TA).join(['( ', ' )']): s([tar, nr], 'remulcld', '( %s x. N ) e. RR' % TA), ('%s x. N' % TB).join(['( ', ' )']): s([tbr, nr], 'remulcld', '( %s x. N ) e. RR' % TB),
                  '( ( N x. %s ) x. N )' % L: s([s([nr, lr], 'remulcld', '( N x. %s ) e. RR' % L), nr], 'remulcld', '( ( N x. %s ) x. N ) e. RR' % L), '( %s x. %s )' % (NN2, L): s([n2r, lr], 'remulcld', '( %s x. %s ) e. RR' % (NN2, L)),
                  '( %s x. N )' % B2: s([b2r, nr], 'remulcld', '( %s x. N ) e. RR' % B2), '( %s x. %s )' % (NL, SY): s([nlr, syr], 'remulcld', '( %s x. %s ) e. RR' % (NL, SY)),
                  '( E x. Y )': s([er, yr], 'remulcld', '( E x. Y ) e. RR')})
    rr27 = ringeq_d(w, A0, '( ( 2 / ; 2 7 ) x. ( E x. Y ) )', '( ( ( 2 x. E ) / ; 2 7 ) x. Y )', cl)
    fin1 = s([fin1, rr27], 'breqtrd', '( ( %s x. N ) + ( %s x. N ) ) <_ ( ( ( 2 x. E ) / ; 2 7 ) x. Y )' % (TA, TB))
    dd = s([s([tar], 'recnd', '%s e. CC' % TA), s([tbr], 'recnd', '%s e. CC' % TB), s([nr], 'recnd', 'N e. CC')], 'adddird', '( ( %s + %s ) x. N ) = ( ( %s x. N ) + ( %s x. N ) )' % (TA, TB, TA, TB))
    fin2 = s([dd, fin1], 'eqbrtrd', '( ( %s + %s ) x. N ) <_ ( ( ( 2 x. E ) / ; 2 7 ) x. Y )' % (TA, TB))
    e27 = s([s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er], 'remulcld', '( 2 x. E ) e. RR'), s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '( ( 2 x. E ) / ; 2 7 ) e. RR'), yr], 'remulcld',
            '( ( ( 2 x. E ) / ; 2 7 ) x. Y ) e. RR')
    fin3 = s([fin2, s([s([tar, tbr], 'readdcld', '( %s + %s ) e. RR' % (TA, TB)), e27, np_], 'lemuldivd',
                      '( ( ( %s + %s ) x. N ) <_ ( ( ( 2 x. E ) / ; 2 7 ) x. Y ) <-> ( %s + %s ) <_ ( ( ( ( 2 x. E ) / ; 2 7 ) x. Y ) / N ) )' % (TA, TB, TA, TB))], 'mpbid', concl)
    w.lines.append('qed:%s:idi |- %s' % (fin3, SB['t21sm']))
    return go(w)


def lin8_(w, ante, hyps, goal, leaves):
    from c8lib import lin8
    return lin8(w, ante, hyps, goal, leaves)


if __name__ == '__main__':
    if not only or 't21efe' in only:
        gen_efe()
    if not only or 't21sm' in only:
        gen_sm()
