"""Sortie T21a: levels (t21ld = log_d_T_le, t21dpow = dpow_le, t21d92 = d_ninehalf_le) and the
harmonic sum (t21harm = sum_inv_succ_le_log)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_
import num, lin
import cl as _cl
lin.FASTPATH = True
from tm import W


def clos(w, A, leaves):
    c = _cl.Closure(w, A, {})
    for k, (kind, s_) in leaves.items():
        c.leaf(k, kind, s_)
    return c


def gen_ld():
    w = W('t21ld', 'At ` T = X ^ 3 ` and ` D <_ X ^ ( 191 / 900 ) ` , ` log ( D ( T + 2 ) ) <_ 5 log X ` (Lean ` log_d_T_le ` ).')
    A0 = ante_of(S['t21ld'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    xs = st([], 'simpl', '( X e. RR /\\ 2 <_ X )'); ds = st([], 'simpr', '( D e. RR /\\ 1 <_ D /\\ D <_ ( X ^c %s ) )' % F191)
    xr = st([xs], 'simpld', 'X e. RR'); x2 = st([xs], 'simprd', '2 <_ X')
    dr = st([ds], 'simp1d', 'D e. RR'); d1 = st([ds], 'simp2d', '1 <_ D'); du = st([ds], 'simp3d', 'D <_ ( X ^c %s )' % F191)
    x1 = lin.linarith(w, A0, [x2], '1 <_ X', leaves={'X': xr})
    x0 = lin.linarith(w, A0, [x2], '0 < X', leaves={'X': xr})
    xp = st([xr, x0], 'elrpd', 'X e. RR+')
    c = clos(w, A0, {'X': ('RR+', xp), 'D': ('RR', dr)})
    c.have('D', 'ge1', d1); c.have('X', 'ge1', x1)
    fr = c.mem(F191, 'RR')
    xc = st([xr, x1, fr, st([num.real(w, '1')], 'a1i', '1 e. RR'), st([num.le_lit(w, F191, '1')], 'a1i', '%s <_ 1' % F191)], 'cxplead', '( X ^c %s ) <_ ( X ^c 1 )' % F191)
    x1e = st([st([xr], 'recnd', 'X e. CC')], 'cxp1d', '( X ^c 1 ) = X')
    xur = c.mem('( X ^c %s )' % F191, 'RR')
    dx = st([dr, xur, xr, du, st([xc, x1e], 'breqtrd', '( X ^c %s ) <_ X' % F191)], 'letrd', 'D <_ X')
    X3, X4 = '( X ^ 3 )', '( X ^ 4 )'
    x3r = c.mem(X3, 'RR')
    x4e = st([st([xr], 'recnd', 'X e. CC'), st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'expp1d', '( X ^ ( 3 + 1 ) ) = ( %s x. X )' % X3)
    x4e2 = st([st([st([w.s([], '3p1e4', '( 3 + 1 ) = 4')], 'a1i', '( 3 + 1 ) = 4')], 'oveq2d', '( X ^ ( 3 + 1 ) ) = %s' % X4), x4e], 'eqtr3d', '%s = ( %s x. X )' % (X4, X3))
    two = st([num.real(w, '2')], 'a1i', '2 e. RR')
    e8 = st([two, xr, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0'), st([num.ge0_nat(w, 2)], 'a1i', '0 <_ 2'), x2], 'leexp1ad', '( 2 ^ 3 ) <_ %s' % X3)
    c8 = st([w.s([], 'cu2', '( 2 ^ 3 ) = 8')], 'a1i', '( 2 ^ 3 ) = 8')
    e8b = st([c8, e8], 'eqbrtrrd', '8 <_ %s' % X3)
    c.leaf(X3, 'RR', x3r); c.atom(X4)
    c.leaf(X4, 'RR', c.mem(X4, 'RR'))
    x43 = lin.nlinarith(w, A0, [x2, e8b, x4e2], '( %s + 2 ) <_ %s' % (X3, X4), closure=c)
    T2 = '( %s + 2 )' % X3
    t2r = c.mem(T2, 'RR'); x4r = c.mem(X4, 'RR')
    d0 = lin.linarith(w, A0, [d1], '0 <_ D', leaves={'D': dr})
    t20 = lin.linarith(w, A0, [e8b], '0 <_ %s' % T2, closure=c)
    pr = st([dr, xr, t2r, x4r, d0, t20, dx, x43], 'lemul12ad', '( D x. %s ) <_ ( X x. %s )' % (T2, X4))
    x5 = st([st([xr], 'recnd', 'X e. CC'), st([w.s([], '4nn0', '4 e. NN0')], 'a1i', '4 e. NN0')], 'expp1d', '( X ^ ( 4 + 1 ) ) = ( %s x. X )' % X4)
    x5b = st([st([st([w.s([], '4p1e5', '( 4 + 1 ) = 5')], 'a1i', '( 4 + 1 ) = 5')], 'oveq2d', '( X ^ ( 4 + 1 ) ) = ( X ^ 5 )'), x5], 'eqtr3d', '( X ^ 5 ) = ( %s x. X )' % X4)
    x5c = st([x5b, st([st([xr], 'recnd', 'X e. CC'), st([x4r], 'recnd', '%s e. CC' % X4)], 'mulcomd', '( %s x. X ) = ( X x. %s )' % (X4, X4))], 'eqtrd', '( X ^ 5 ) = ( X x. %s )' % X4)
    pr2 = st([pr, x5c], 'breqtrrd', '( D x. %s ) <_ ( X ^ 5 )' % T2)
    dp = lin.linarith(w, A0, [d1], '0 < D', leaves={'D': dr})
    drp = st([dr, dp], 'elrpd', 'D e. RR+')
    c.have('D', 'RR+', drp)
    lhp = c.mem('( D x. %s )' % T2, 'RR+') if False else st([drp, st([t2r, lin.linarith(w, A0, [e8b], '0 < %s' % T2, closure=c)], 'elrpd', '%s e. RR+' % T2)], 'rpmulcld', '( D x. %s ) e. RR+' % T2)
    x5p = st([xp, st([w.s([], '5nn0', '5 e. NN0')], 'a1i', '5 e. NN0') and st([num.z_nat(w, 5)], 'a1i', '5 e. ZZ')], 'rpexpcld', '( X ^ 5 ) e. RR+')
    lg = st([pr2, st([lhp, x5p], 'logled', '( ( D x. %s ) <_ ( X ^ 5 ) <-> ( log ` ( D x. %s ) ) <_ ( log ` ( X ^ 5 ) ) )' % (T2, T2))], 'mpbid', '( log ` ( D x. %s ) ) <_ ( log ` ( X ^ 5 ) )' % T2)
    le = ap_(w, A0, [xp, st([num.z_nat(w, 5)], 'a1i', '5 e. ZZ')], 'relogexp', '( log ` ( X ^ 5 ) ) = ( 5 x. ( log ` X ) )')
    w.qed([lg, le], 'breqtrd', S['t21ld'])
    return w.run()

def gen_dpow():
    w = W('t21dpow', 'The level lemma: from ` 1 <_ D <_ X ^ U ` and ` D X ^ V <_ Y ` , ` D ^ A <_ X ^ ( U ( A - B ) - V B ) Y ^ B ` for ` 0 <_ B <_ A ` (Lean ` dpow_le ` ).')
    A0 = ante_of(S['t21dpow'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    xr, x1, dr, d1, du = u['X e. RR'], u['1 <_ X'], u['D e. RR'], u['1 <_ D'], u['D <_ ( X ^c U )']
    ur, vr, yr, dy = u['U e. RR'], u['V e. RR'], u['Y e. RR'], u['( D x. ( X ^c V ) ) <_ Y']
    ar, br, b0, ba = u['A e. RR'], u['B e. RR'], u['0 <_ B'], u['B <_ A']
    xp = st([xr, lin.linarith(w, A0, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    dp = st([dr, lin.linarith(w, A0, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    d0 = st([dp], 'rpge0d', '0 <_ D'); dc = st([dr], 'recnd', 'D e. CC'); dn = st([dp], 'rpne0d', 'D =/= 0')
    XU, XV = '( X ^c U )', '( X ^c V )'
    xu = st([xp, ur], 'rpcxpcld', '%s e. RR+' % XU); xv = st([xp, vr], 'rpcxpcld', '%s e. RR+' % XV)
    AB = '( A - B )'
    abr = st([ar, br], 'resubcld', '%s e. RR' % AB)
    ab0 = st([ar, br], 'subge0d', '( 0 <_ %s <-> B <_ A )' % AB)
    ab0 = st([ba, ab0], 'mpbird', '0 <_ %s' % AB)
    h1 = st([dr, d0, st([xu], 'rpred', '%s e. RR' % XU), abr, ab0, du], 'cxple2ad', '( D ^c %s ) <_ ( %s ^c %s )' % (AB, XU, AB))
    e1 = st([xp, ur, st([abr], 'recnd', '%s e. CC' % AB)], 'cxpmuld', '( X ^c ( U x. %s ) ) = ( %s ^c %s )' % (AB, XU, AB))
    h1b = st([h1, e1], 'breqtrrd', '( D ^c %s ) <_ ( X ^c ( U x. %s ) )' % (AB, AB))
    YQ = '( Y / %s )' % XV
    dq = st([dy, st([dr, yr, xv], 'lemuldivd', '( ( D x. %s ) <_ Y <-> D <_ %s )' % (XV, YQ))], 'mpbid', 'D <_ %s' % YQ)
    y0 = st([st([dr, st([xv], 'rpred', '%s e. RR' % XV)], 'remulcld', '( D x. %s ) e. RR' % XV), yr,
             st([dr, st([xv], 'rpred', '%s e. RR' % XV), d0, st([xv], 'rpge0d', '0 <_ %s' % XV)], 'mulge0d', '0 <_ ( D x. %s )' % XV) , dy], 'x', 'x') if False else None
    dxv0 = st([dr, st([xv], 'rpred', '%s e. RR' % XV), d0, st([xv], 'rpge0d', '0 <_ %s' % XV)], 'mulge0d', '0 <_ ( D x. %s )' % XV)
    dxvr = st([dr, st([xv], 'rpred', '%s e. RR' % XV)], 'remulcld', '( D x. %s ) e. RR' % XV)
    y0 = st([st([], '0red', '0 e. RR') if False else st([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), dxvr, yr, dxv0, dy], 'letrd', '0 <_ Y')
    yqr = st([yr, xv], 'rerpdivcld', '%s e. RR' % YQ)
    h2 = st([dr, d0, yqr, br, b0, dq], 'cxple2ad', '( D ^c B ) <_ ( %s ^c B )' % YQ)
    bc = st([br], 'recnd', 'B e. CC')
    e2 = st([yr, y0, xv, bc], 'divcxpd', '( %s ^c B ) = ( ( Y ^c B ) / ( %s ^c B ) )' % (YQ, XV))
    e3 = st([xp, vr, bc], 'cxpmuld', '( X ^c ( V x. B ) ) = ( %s ^c B )' % XV)
    e23 = st([e2, st([e3], 'oveq2d', '( ( Y ^c B ) / ( X ^c ( V x. B ) ) ) = ( ( Y ^c B ) / ( %s ^c B ) )' % XV)], 'eqtr4d', '( %s ^c B ) = ( ( Y ^c B ) / ( X ^c ( V x. B ) ) )' % YQ)
    h2b = st([h2, e23], 'breqtrd', '( D ^c B ) <_ ( ( Y ^c B ) / ( X ^c ( V x. B ) ) )')
    ea = st([st([ar], 'recnd', 'A e. CC'), bc], 'npcand', '( %s + B ) = A' % AB)
    da = st([dc, dn, st([abr], 'recnd', '%s e. CC' % AB), bc], 'cxpaddd', '( D ^c ( %s + B ) ) = ( ( D ^c %s ) x. ( D ^c B ) )' % (AB, AB))
    da2 = st([st([ea], 'oveq2d', '( D ^c ( %s + B ) ) = ( D ^c A )' % AB), da], 'eqtr3d', '( D ^c A ) = ( ( D ^c %s ) x. ( D ^c B ) )' % AB)
    XUA, XVB, YB = '( X ^c ( U x. %s ) )' % AB, '( X ^c ( V x. B ) )', '( Y ^c B )'
    xuar = st([xp, st([ur, abr], 'remulcld', '( U x. %s ) e. RR' % AB)], 'rpcxpcld', '%s e. RR+' % XUA)
    xvbr = st([xp, st([vr, br], 'remulcld', '( V x. B ) e. RR')], 'rpcxpcld', '%s e. RR+' % XVB)
    ybr = st([yr, y0, br], 'recxpcld', '%s e. RR' % YB)
    q = st([ybr, xvbr], 'rerpdivcld', '( %s / %s ) e. RR' % (YB, XVB))
    pr = st([st([dr, d0, abr], 'recxpcld', '( D ^c %s ) e. RR' % AB), st([xuar], 'rpred', '%s e. RR' % XUA),
             st([dr, d0, br], 'recxpcld', '( D ^c B ) e. RR'), q, st([dr, d0, abr], 'cxpge0d', '0 <_ ( D ^c %s )' % AB),
             st([dr, d0, br], 'cxpge0d', '0 <_ ( D ^c B )'), h1b, h2b], 'lemul12ad', '( ( D ^c %s ) x. ( D ^c B ) ) <_ ( %s x. ( %s / %s ) )' % (AB, XUA, YB, XVB))
    xc = st([xuar], 'rpcnd', '%s e. CC' % XUA); yc = st([ybr], 'recnd', '%s e. CC' % YB); vc = st([xvbr], 'rpcnd', '%s e. CC' % XVB); vn = st([xvbr], 'rpne0d', '%s =/= 0' % XVB)
    r1 = st([xc, yc, vc, vn], 'divassd', '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (XUA, YB, XVB, XUA, YB, XVB))
    r2 = st([xc, yc, vc, vn], 'div23d', '( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s )' % (XUA, YB, XVB, XUA, XVB, YB))
    EX = '( ( U x. %s ) - ( V x. B ) )' % AB
    r3 = st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([st([ur, abr], 'remulcld', '( U x. %s ) e. RR' % AB)], 'recnd', '( U x. %s ) e. CC' % AB),
             st([st([vr, br], 'remulcld', '( V x. B ) e. RR')], 'recnd', '( V x. B ) e. CC')], 'cxpsubd', '( X ^c %s ) = ( %s / %s )' % (EX, XUA, XVB))
    r4 = st([r3], 'oveq1d', '( ( X ^c %s ) x. %s ) = ( ( %s / %s ) x. %s )' % (EX, YB, XUA, XVB, YB))
    rr = st([st([r1, r2], 'eqtr3d', '( %s x. ( %s / %s ) ) = ( ( %s / %s ) x. %s )' % (XUA, YB, XVB, XUA, XVB, YB)), r4], 'eqtr4d',
            '( %s x. ( %s / %s ) ) = ( ( X ^c %s ) x. %s )' % (XUA, YB, XVB, EX, YB))
    fin = st([st([da2, pr], 'eqbrtrd', '( D ^c A ) <_ ( %s x. ( %s / %s ) )' % (XUA, YB, XVB)), rr], 'breqtrd', '( D ^c A ) <_ ( ( X ^c %s ) x. %s )' % (EX, YB))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21dpow']))
    return w.run()

def gen_d92():
    w = W('t21d92', 'At the level ` N <_ X ^ ( 191 / 900 ) ` , ` N X ^ ( 709 / 900 ) <_ Y ` : ` N ^ ( 9 / 2 ) <_ X ^ ( - 9 / 200 ) Y ` (Lean ` d_ninehalf_le ` ; ~ t21dpow ).')
    A0 = ante_of(S['t21d92'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    lr = lambda t_: st([num.real(w, t_)], 'a1i', '%s e. RR' % t_)
    m = {'U': F191, 'V': F709, 'A': F92, 'B': '1'}
    body = S['t21dpow'].split(' -> ', 1)[1][:-2]
    EX = '( ( %s x. ( %s - 1 ) ) - ( %s x. 1 ) )' % (F191, F92, F709)
    f = '( D ^c %s ) <_ ( ( X ^c %s ) x. ( Y ^c 1 ) )' % (F92, EX)
    l1 = st([lin.linarith(w, A0, [], '0 <_ 1', leaves={})] if False else [], 'x', 'x') if False else None
    b0 = st([num.le_lit(w, '0', '1')], 'a1i', '0 <_ 1')
    b1 = st([num.le_lit(w, '1', F92)], 'a1i', '1 <_ %s' % F92)
    hyp = [u['X e. RR'], u['1 <_ X'], u['D e. RR'], u['1 <_ D'], u['D <_ ( X ^c %s )' % F191], lr(F191), lr(F709), u['Y e. RR'],
           u['( D x. ( X ^c %s ) ) <_ Y' % F709], lr(F92), lr('1'), b0, b1]
    d = ap_(w, A0, hyp, 't21dpow', f)
    ee = lin.lineq(w, A0, EX, '-u %s' % F9200, leaves={})
    y1 = st([st([u['Y e. RR']], 'recnd', 'Y e. CC')], 'cxp1d', '( Y ^c 1 ) = Y')
    rhs = st([st([ee], 'oveq2d', '( X ^c %s ) = ( X ^c -u %s )' % (EX, F9200)), y1], 'oveq12d', '( ( X ^c %s ) x. ( Y ^c 1 ) ) = ( ( X ^c -u %s ) x. Y )' % (EX, F9200))
    w.qed([d, rhs], 'breqtrd', S['t21d92'])
    return w.run()


def gen_harm():
    w = W('t21harm', '` sum_ ( 1 <_ n <_ floor T ) 1 / ( n + 1 ) <_ log ( floor T + 1 ) ` (Lean ` sum_inv_succ_le_log ` ; ~ harmonicubnd ).')
    A0 = ante_of(S['t21harm'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    one_z = lambda A_: w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A_)
    u = unpack(w, A0)
    tr, t1 = u['T e. RR'], u['1 <_ T']
    FT = '( |_ ` T )'; M1 = '( %s + 1 )' % FT
    fz = st([tr], 'flcld', '%s e. ZZ' % FT)
    m1z = st([fz], 'peano2zd', '%s e. ZZ' % M1)
    m1r = st([m1z], 'zred', '%s e. RR' % M1)
    fr = st([fz], 'zred', '%s e. RR' % FT)
    f1 = st([t1, ap_(w, A0, [tr, one_z(A0)], 'flge', '( 1 <_ T <-> 1 <_ %s )' % FT)], 'mpbid', '1 <_ %s' % FT)
    m11 = lin.linarith(w, A0, [f1], '1 <_ %s' % M1, leaves={FT: fr})
    hb = ap_(w, A0, [m1r, m11], 'harmonicubnd', 'sum_ m e. ( 1 ... ( |_ ` %s ) ) ( 1 / m ) <_ ( ( log ` %s ) + 1 )' % (M1, M1))
    fid = ap_(w, A0, [m1z], 'flid', '( |_ ` %s ) = %s' % (M1, M1))
    H = 'sum_ m e. ( 1 ... %s ) ( 1 / m )' % M1
    hb2 = st([st([st([fid], 'oveq2d', '( 1 ... ( |_ ` %s ) ) = ( 1 ... %s )' % (M1, M1))], 'sumeq1d', 'sum_ m e. ( 1 ... ( |_ ` %s ) ) ( 1 / m ) = %s' % (M1, H)), hb],
             'eqbrtrrd', '%s <_ ( ( log ` %s ) + 1 )' % (H, M1))
    c3 = st([one_z(A0), m1z, m11], '3jca', '( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s )' % (M1, M1))
    uz = w.s([c3, w.s([], 'eluz2', '( %s e. ( ZZ>= ` 1 ) <-> ( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s ) )' % (M1, M1, M1))], 'sylibr', '( %s -> %s e. ( ZZ>= ` 1 ) )' % (A0, M1))
    # m in ( 1 ... M1 )
    A1 = '( %s /\\ m e. ( 1 ... %s ) )' % (A0, M1)
    mnn = ap_(w, A1, [w.s([], 'simpr', '( %s -> m e. ( 1 ... %s ) )' % (A1, M1))], 'elfznn', 'm e. NN')
    mr1 = w.s([mnn], 'nnrecred', '( %s -> ( 1 / m ) e. RR )' % A1)
    mc = w.s([mr1], 'recnd', '( %s -> ( 1 / m ) e. CC )' % A1)
    e1 = w.s([], 'oveq2', '( m = 1 -> ( 1 / m ) = ( 1 / 1 ) )')
    S2 = 'sum_ m e. ( ( 1 + 1 ) ... %s ) ( 1 / m )' % M1
    sp = st([uz, mc, e1], 'fsum1p', '%s = ( ( 1 / 1 ) + %s )' % (H, S2))
    # n in ( 1 ... FT )
    A2 = '( %s /\\ n e. ( 1 ... %s ) )' % (A0, FT)
    nnn = ap_(w, A2, [w.s([], 'simpr', '( %s -> n e. ( 1 ... %s ) )' % (A2, FT))], 'elfznn', 'n e. NN')
    nr1 = w.s([w.s([nnn], 'peano2nnd', '( %s -> ( n + 1 ) e. NN )' % A2)], 'nnrecred', '( %s -> ( 1 / ( n + 1 ) ) e. RR )' % A2)
    nc = w.s([nr1], 'recnd', '( %s -> ( 1 / ( n + 1 ) ) e. CC )' % A2)
    sub = w.s([w.s([], 'oveq1', '( n = ( m - 1 ) -> ( n + 1 ) = ( ( m - 1 ) + 1 ) )')], 'oveq2d', '( n = ( m - 1 ) -> ( 1 / ( n + 1 ) ) = ( 1 / ( ( m - 1 ) + 1 ) ) )')
    S1 = 'sum_ n e. ( 1 ... %s ) ( 1 / ( n + 1 ) )' % FT
    sh = st([one_z(A0), one_z(A0), fz, nc, sub], 'fsumshft', '%s = sum_ m e. ( ( 1 + 1 ) ... ( %s + 1 ) ) ( 1 / ( ( m - 1 ) + 1 ) )' % (S1, FT))
    # m in ( ( 1 + 1 ) ... M1 )
    A3 = '( %s /\\ m e. ( ( 1 + 1 ) ... %s ) )' % (A0, M1)
    m3in = w.s([], 'simpr', '( %s -> m e. ( ( 1 + 1 ) ... %s ) )' % (A3, M1))
    m3 = ap_(w, A3, [m3in], 'elfzelz', 'm e. ZZ')
    m3r = w.s([m3], 'zred', '( %s -> m e. RR )' % A3)
    m3le = ap_(w, A3, [m3in], 'elfzle1', '( 1 + 1 ) <_ m')
    m3p = lin.linarith(w, A3, [m3le], '0 < m', leaves={'m': m3r})
    m3rec = w.s([m3r, w.s([m3p], 'gt0ne0d', '( %s -> m =/= 0 )' % A3)], 'rereccld', '( %s -> ( 1 / m ) e. RR )' % A3)
    np = w.s([w.s([w.s([m3], 'zcnd', '( %s -> m e. CC )' % A3), w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A3)], 'npcand', '( %s -> ( ( m - 1 ) + 1 ) = m )' % A3)],
             'oveq2d', '( %s -> ( 1 / ( ( m - 1 ) + 1 ) ) = ( 1 / m ) )' % A3)
    sh2 = st([np], 'sumeq2dv', 'sum_ m e. ( ( 1 + 1 ) ... %s ) ( 1 / ( ( m - 1 ) + 1 ) ) = %s' % (M1, S2))
    eq = st([sh, sh2], 'eqtrd', '%s = %s' % (S1, S2))
    o1 = st([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')
    lg = st([st([m1r, lin.linarith(w, A0, [m11], '0 < %s' % M1, leaves={M1: m1r})], 'elrpd', '%s e. RR+' % M1)], 'relogcld', '( log ` %s ) e. RR' % M1)
    s1r = st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % FT), nr1], 'fsumrecl', '%s e. RR' % S1)
    hr = st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % M1), mr1], 'fsumrecl', '%s e. RR' % H)
    s2r = st([st([], 'fzfid', '( ( 1 + 1 ) ... %s ) e. Fin' % M1), m3rec], 'fsumrecl', '%s e. RR' % S2)
    c = _cl.Closure(w, A0, {})
    c.leaf(S1, 'RR', s1r); c.leaf(S2, 'RR', s2r); c.leaf(H, 'RR', hr); c.leaf('( log ` %s )' % M1, 'RR', lg)
    sp2 = st([sp, st([o1], 'oveq1d', '( ( 1 / 1 ) + %s ) = ( 1 + %s )' % (S2, S2))], 'eqtrd', '%s = ( 1 + %s )' % (H, S2))
    fin = lin.linarith(w, A0, [hb2, sp2, eq], '%s <_ ( log ` %s )' % (S1, M1), closure=c)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21harm']))
    return w.run()

if __name__ == '__main__':
    only = sys.argv[1:]
    for lab, f in [('t21ld', gen_ld), ('t21dpow', gen_dpow), ('t21d92', gen_d92), ('t21harm', gen_harm)]:
        if not only or lab in only:
            f()
