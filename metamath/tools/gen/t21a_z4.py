"""Sortie T21a: zone IV (t21z4 = zoneIV_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21a_zz import *
import cl as _cl
from t21a_z1 import x_basics
lin.FASTPATH = True
lin.MAXDEG = 6


def gen_z4():
    w = W('t21z4', 'Zone IV(b) ( ` tau <_ beta ` , ` tau = 1 - R / log X ` ): when no zero of any ` chi mod N ` lies in ` [ tau , 1 ] x. [ - V , V ] ` , each remaining zero weighs at most ` ord Y / V ` and the log-free density at ` sigma = tau ` , ` t = X ^ 3 ` counts them by ` G e ^ ( 28 R ) ` (Lean ` zoneIV_le ` ; ~ t21zfel , ~ nco_eq ).')
    A0 = ante_of(S['t21z4'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L_ = lambda s_, A_: _cl.lift(w, s_, A_)
    u = unpack(w, A0)
    body = LFD_BODY('G', 'C')
    HE = 'A. y e. %s A. p e. %s ( %s <_ ( Re ` p ) -> V < ( abs ` ( Im ` p ) ) )' % (DB, ZFo(HALF, X3), TAU)
    nn, xr, xe, nx, yr, y1, gr, g1, cr, c2, bst, rp, vp, r10, he = [u[k] for k in ['N e. NN', 'X e. RR', '( exp ` 1 ) <_ X', 'N <_ ( X ^c %s )' % F191, 'Y e. RR', '1 <_ Y',
        'G e. RR', '1 <_ G', 'C e. RR', 'C <_ 2', body, 'R e. RR+', 'V e. RR+', '( ; 1 0 x. R ) <_ %s' % LX, HE]]
    L = LX
    b = x_basics(w, A0, xr, xe)
    lr = b['lr']
    lp = st([lr, lin.linarith(w, A0, [b['l1']], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    one = b['one']
    rr = st([rp], 'rpred', 'R e. RR')
    RL = '( R / %s )' % L
    rlr = st([rr, lp], 'rerpdivcld', '%s e. RR' % RL)
    rl0 = st([rr, lp, st([rp], 'rpge0d', '0 <_ R')], 'divge0d', '0 <_ %s' % RL)
    # R / L <_ 1 / 10
    rle = st([lin.linarith(w, A0, [r10], 'R <_ ( %s x. ( 1 / ; 1 0 ) )' % L, leaves={'R': rr, L: lr}), st([rr, st([num.real(w, '( 1 / ; 1 0 )')], 'a1i', '( 1 / ; 1 0 ) e. RR'), lp], 'ledivmuld', '( %s <_ ( 1 / ; 1 0 ) <-> R <_ ( %s x. ( 1 / ; 1 0 ) ) )' % (RL, L))], 'mpbird', '%s <_ ( 1 / ; 1 0 )' % RL)
    taur = st([one, rlr], 'resubcld', '%s e. RR' % TAU)
    ct = clos(w, A0, {RL: rlr})
    t9 = lin.linarith(w, A0, [rle], '%s <_ %s' % (F910, TAU), closure=ct)
    t1 = lin.linarith(w, A0, [rl0], '%s <_ 1' % TAU, closure=ct)
    th = lin.linarith(w, A0, [rle], '%s <_ %s' % (HALF, TAU), closure=ct)
    t0 = lin.linarith(w, A0, [rle], '0 < %s' % TAU, closure=ct)
    # ---- per character / per zero
    C1 = '( %s /\\ x e. %s )' % (A0, DB)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (C1, DB))
    phi = lambda pv: '( %s <_ ( Re ` %s ) -> V < ( abs ` ( Im ` %s ) ) )' % (TAU, pv, pv)
    PSY = 'A. p e. %s %s' % (ZFo(HALF, X3), phi('p'))
    idy = w.s([], 'id', '( y = x -> y = x )')
    cy, PSX = w.wcongr(PSY, {'y': 'x'}, 'y = x', {'y': idy})
    rs1 = w.s([cy], 'rspcv', '( x e. %s -> ( %s -> %s ) )' % (DB, HE, PSX))
    psx = w.s([xin, L_(he, C1), rs1], 'sylc', '( %s -> %s )' % (C1, PSX))
    ZT_ = ZFX(TAU, X3); Z0 = ZFX(HALF, X3)
    ZOx = PSX[len('A. p e. '):len(PSX) - len(phi('p')) - 1]
    C2 = '( %s /\\ q e. %s )' % (C1, ZT_)
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, ZT_))
    xr3 = L_(b['x3r'], C2)
    ss = ap_(w, C2, [L_(st([num.real(w, HALF)], 'a1i', '%s e. RR' % HALF), C2), L_(taur, C2), L_(th, C2), xr3, xr3, w.s([xr3], 'leidd', '( %s -> %s <_ %s )' % (C2, X3, X3))], 't21zfss', '%s C_ %s' % (ZT_, Z0))
    q0 = w.s([ss, qin], 'sseldd', '( %s -> q e. %s )' % (C2, Z0))
    Ex = EX
    phr = lambda b_: '( %s =/= 1 /\\ ( %s ` %s ) = 0 )' % (b_, Ex, b_)
    idro = w.s([], 'id', '( r = o -> r = o )')
    cro, _ = w.wcongr(phr('r'), {'r': 'o'}, 'r = o', {'r': idro})
    zeq = w.s([cro], 'cbvrabv', '%s = %s' % (Z0, ZOx))
    qo = w.s([q0, w.s([w.s([zeq], 'eleq2i', '( q e. %s <-> q e. %s )' % (Z0, ZOx))], 'a1i', '( %s -> ( q e. %s <-> q e. %s ) )' % (C2, Z0, ZOx))], 'mpbid', '( %s -> q e. %s )' % (C2, ZOx))
    idp = w.s([], 'id', '( p = q -> p = q )')
    cp, phq = w.wcongr(phi('p'), {'p': 'q'}, 'p = q', {'p': idp})
    rs2 = w.s([cp], 'rspcv', '( q e. %s -> ( %s -> %s ) )' % (ZOx, PSX, phq))
    phiq = w.s([qo, L_(psx, C2), rs2], 'sylc', '( %s -> %s )' % (C2, phq))
    qf = q_facts(w, C2, qin, L_(taur, C2), xr3, TAU, X3)
    vim = w.s([qf['lo'], phiq], 'mpd', '( %s -> V < ( abs ` ( Im ` q ) ) )' % C2)
    ez = ap_(w, C1, [L_(nn, C1), xin, L_(taur, C1), L_(t0, C1), L_(t1, C1), L_(b['x3r'], C1)], 'ezf', '( %s e. Fin /\\ A. q e. %s %s e. NN )' % (ZT_, ZT_, ORD()))
    zfin = w.s([ez], 'simpld', '( %s -> %s e. Fin )' % (C1, ZT_))
    ordn = w.s([L_(w.s([ez], 'simprd', '( %s -> A. q e. %s %s e. NN )' % (C1, ZT_, ORD())), C2), qin, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (ZT_, ORD(), ZT_, ORD()))], 'sylc', '( %s -> %s e. NN )' % (C2, ORD()))
    orr = w.s([ordn], 'nnred', '( %s -> %s e. RR )' % (C2, ORD())); or0 = w.s([w.s([ordn], 'nnnn0d', '( %s -> %s e. NN0 )' % (C2, ORD()))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (C2, ORD()))
    wr, w0, g1p = wt_facts(w, C2, orr, or0, qf)
    G_ = '( abs ` ( Im ` q ) )'
    vle = lin.linarith(w, C2, [vim], 'V <_ ( 1 + %s )' % G_, leaves={'V': L_(st([vp], 'rpred', 'V e. RR'), C2), G_: qf['imr']})
    wv = w.s([L_(vp, C2), g1p, orr, or0, vle], 'lediv2ad', '( %s -> %s <_ ( %s / V ) )' % (C2, WT(), ORD()))
    yre = w.s([L_(yr, C2), L_(lin.linarith(w, A0, [y1], '0 <_ Y', leaves={'Y': yr}), C2), qf['re']], 'recxpcld', '( %s -> ( Y ^c ( Re ` q ) ) e. RR )' % C2)
    yre0 = w.s([L_(yr, C2), L_(lin.linarith(w, A0, [y1], '0 <_ Y', leaves={'Y': yr}), C2), qf['re']], 'cxpge0d', '( %s -> 0 <_ ( Y ^c ( Re ` q ) ) )' % C2)
    yle = w.s([w.s([L_(yr, C2), L_(y1, C2), qf['re'], L_(one, C2), qf['hi']], 'cxplead', '( %s -> ( Y ^c ( Re ` q ) ) <_ ( Y ^c 1 ) )' % C2), w.s([L_(st([yr], 'recnd', 'Y e. CC'), C2)], 'cxp1d', '( %s -> ( Y ^c 1 ) = Y )' % C2)], 'breqtrd', '( %s -> ( Y ^c ( Re ` q ) ) <_ Y )' % C2)
    OV = '( %s / V )' % ORD()
    ovr = w.s([orr, L_(vp, C2)], 'rerpdivcld', '( %s -> %s e. RR )' % (C2, OV))
    pr = w.s([wr, ovr, yre, L_(yr, C2), w0, yre0, wv, yle], 'lemul12ad', '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) <_ ( %s x. Y ) )' % (C2, WT(), OV))
    oc = w.s([orr], 'recnd', '( %s -> %s e. CC )' % (C2, ORD())); yc = L_(st([yr], 'recnd', 'Y e. CC'), C2)
    vc = L_(st([vp], 'rpcnd', 'V e. CC'), C2); vn = L_(st([vp], 'rpne0d', 'V =/= 0'), C2)
    d1 = w.s([oc, yc, vc, vn], 'div23d', '( %s -> ( ( %s x. Y ) / V ) = ( %s x. Y ) )' % (C2, ORD(), OV))
    d2 = w.s([yc, oc, vc, vn], 'div23d', '( %s -> ( ( Y x. %s ) / V ) = ( ( Y / V ) x. %s ) )' % (C2, ORD(), ORD()))
    d3 = w.s([w.s([oc, yc], 'mulcomd', '( %s -> ( %s x. Y ) = ( Y x. %s ) )' % (C2, ORD(), ORD()))], 'oveq1d', '( %s -> ( ( %s x. Y ) / V ) = ( ( Y x. %s ) / V ) )' % (C2, ORD(), ORD()))
    YVO = '( ( Y / V ) x. %s )' % ORD()
    deq = w.s([w.s([d1, d3], 'eqtr3d', '( %s -> ( %s x. Y ) = ( ( Y x. %s ) / V ) )' % (C2, OV, ORD())), d2], 'eqtrd', '( %s -> ( %s x. Y ) = %s )' % (C2, OV, YVO))
    pt = w.s([pr, deq], 'breqtrd', '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) <_ %s )' % (C2, WT(), YVO))
    # sums
    YV = '( Y / V )'
    yvr = st([yr, vp], 'rerpdivcld', '%s e. RR' % YV)
    BW = '( %s x. ( Y ^c ( Re ` q ) ) )' % WT()
    bwr = w.s([wr, yre], 'remulcld', '( %s -> %s e. RR )' % (C2, BW))
    yvor = w.s([L_(yvr, C2), orr], 'remulcld', '( %s -> %s e. RR )' % (C2, YVO))
    i1 = w.s([zfin, bwr, yvor, pt], 'fsumle', '( %s -> sum_ q e. %s %s <_ sum_ q e. %s %s )' % (C1, ZT_, BW, ZT_, YVO))
    SO = 'sum_ q e. %s %s' % (ZT_, ORD())
    i2 = w.s([zfin, L_(st([yvr], 'recnd', '%s e. CC' % YV), C1), oc], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ q e. %s %s )' % (C1, YV, SO, ZT_, YVO))
    per = w.s([i1, i2], 'breqtrrd', '( %s -> sum_ q e. %s %s <_ ( %s x. %s ) )' % (C1, ZT_, BW, YV, SO))
    DBfin = w.s([nn, w.s([w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'), w.s([], 'eqid', '%s = %s' % (DB, DB))], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB)], 'syl', '( %s -> %s e. Fin )' % (A0, DB))
    sor = w.s([zfin, orr], 'fsumrecl', '( %s -> %s e. RR )' % (C1, SO))
    o1 = st([DBfin, w.s([zfin, bwr], 'fsumrecl', '( %s -> sum_ q e. %s %s e. RR )' % (C1, ZT_, BW)), w.s([L_(yvr, C1), sor], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (C1, YV, SO)), per], 'fsumle',
            '%s <_ sum_ x e. %s ( %s x. %s )' % (ZT(X3, 'Y', TAU), DB, YV, SO))
    o2 = st([DBfin, st([yvr], 'recnd', '%s e. CC' % YV), w.s([sor], 'recnd', '( %s -> %s e. CC )' % (C1, SO))], 'fsummulc2', '( %s x. %s ) = sum_ x e. %s ( %s x. %s )' % (YV, NC(TAU, X3), DB, YV, SO))
    zb = st([o1, o2], 'breqtrrd', '%s <_ ( %s x. %s )' % (ZT(X3, 'Y', TAU), YV, NC(TAU, X3)))
    # ---- the count at sigma = tau, t = X^3
    inner = body.split(' ', 8)[8]
    idv = w.s([], 'id', '( v = %s -> v = %s )' % (X3, X3))
    c1_, b_t = w.wcongr(inner, {'v': X3}, 'v = %s' % X3, {'v': idv})
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (TAU, TAU))
    c2_, b_ta = w.wcongr(b_t, {'u': TAU}, 'u = %s' % TAU, {'u': idu})
    rs = w.s([c1_, c2_], 'rspc2v', '( ( %s e. RR /\\ %s e. RR ) -> ( %s -> %s ) )' % (X3, TAU, body, b_ta))
    inst = st([st([b['x3r'], taur], 'jca', '( %s e. RR /\\ %s e. RR )' % (X3, TAU)), bst, rs], 'sylc', b_ta)
    pre, post = b_ta[2:-2].split(' -> ', 1)
    x32 = lin.linarith(w, A0, [b['x8']], '2 <_ %s' % X3, leaves={X3: b['x3r']})
    got = st([st([x32, t9, t1], '3jca', pre), inst], 'mpd', post)
    rhs_b = post[len(NCo(TAU, X3)) + 4:]
    got2 = st([st([nco_eq(w, TAU, X3)], 'a1i', '%s = %s' % (NCo(TAU, X3), NC(TAU, X3))), got], 'eqbrtrrd', '%s <_ %s' % (NC(TAU, X3), rhs_b))
    X3c = '( %s ^c C )' % X3
    xp = b['xp']
    three = st([num.real(w, '3')], 'a1i', '3 e. RR')
    c3 = st([three, cr], 'remulcld', '( 3 x. C ) e. RR')
    m1 = st([xp, three, st([cr], 'recnd', 'C e. CC')], 'cxpmuld', '( X ^c ( 3 x. C ) ) = ( ( X ^c 3 ) ^c C )')
    m2 = ap_(w, A0, [st([xp], 'rpcnd', 'X e. CC'), st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'cxpexp', '( X ^c 3 ) = %s' % X3)
    m3 = st([m1, st([m2], 'oveq1d', '( ( X ^c 3 ) ^c C ) = %s' % X3c)], 'eqtrd', '( X ^c ( 3 x. C ) ) = %s' % X3c)
    six = st([num.real(w, '6')], 'a1i', '6 e. RR')
    le6 = st([xr, b['x1'], c3, six, lin.linarith(w, A0, [c2], '( 3 x. C ) <_ 6', leaves={'C': cr})], 'cxplead', '( X ^c ( 3 x. C ) ) <_ ( X ^c 6 )')
    xcle = st([m3, le6], 'eqbrtrrd', '%s <_ ( X ^c 6 )' % X3c)
    X191 = '( X ^c %s )' % F191
    x191r = st([st([xp, st([num.real(w, F191)], 'a1i', '%s e. RR' % F191)], 'rpcxpcld', '%s e. RR+' % X191)], 'rpred', '%s e. RR' % X191)
    x3cp = st([st([xp, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0') and st([num.z_nat(w, 3)], 'a1i', '3 e. ZZ')], 'rpexpcld', '%s e. RR+' % X3), cr], 'rpcxpcld', '%s e. RR+' % X3c)
    x6r = st([st([xp, six], 'rpcxpcld', '( X ^c 6 ) e. RR+')], 'rpred', '( X ^c 6 ) e. RR')
    nr = st([nn], 'nnred', 'N e. RR'); n0 = st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')
    NX = '( N x. %s )' % X3c
    nxle = st([nr, x191r, st([x3cp], 'rpred', '%s e. RR' % X3c), x6r, n0, st([x3cp], 'rpge0d', '0 <_ %s' % X3c), nx, xcle], 'lemul12ad', '%s <_ ( %s x. ( X ^c 6 ) )' % (NX, X191))
    A_ = '( %s + 6 )' % F191
    ad = st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([num.cc(w, F191)], 'a1i', '%s e. CC' % F191), st([num.cc(w, '6')], 'a1i', '6 e. CC')], 'cxpaddd', '( X ^c %s ) = ( %s x. ( X ^c 6 ) )' % (A_, X191))
    nxle2 = st([nxle, ad], 'breqtrrd', '%s <_ ( X ^c %s )' % (NX, A_))
    E_ = '( %s x. ( 1 - %s ) )' % (F92, TAU)
    er_ = st([st([num.real(w, F92)], 'a1i', '%s e. RR' % F92), st([one, taur], 'resubcld', '( 1 - %s ) e. RR' % TAU)], 'remulcld', '%s e. RR' % E_)
    e0 = lin.linarith(w, A0, [t1], '0 <_ %s' % E_, closure=ct)
    nxr = st([nr, st([x3cp], 'rpred', '%s e. RR' % X3c)], 'remulcld', '%s e. RR' % NX)
    nx0 = st([nr, st([x3cp], 'rpred', '%s e. RR' % X3c), n0, st([x3cp], 'rpge0d', '0 <_ %s' % X3c)], 'mulge0d', '0 <_ %s' % NX)
    XA = '( X ^c %s )' % A_
    xar = st([st([xp, st([num.real(w, A_)], 'a1i', '%s e. RR' % A_) if num.is_lit(A_) else st([st([num.real(w, F191)], 'a1i', '%s e. RR' % F191), six], 'readdcld', '%s e. RR' % A_)], 'rpcxpcld', '%s e. RR+' % XA)], 'rpred', '%s e. RR' % XA)
    pw = st([nxr, nx0, xar, er_, e0, nxle2], 'cxple2ad', '( %s ^c %s ) <_ ( %s ^c %s )' % (NX, E_, XA, E_))
    ar_ = st([st([num.real(w, F191)], 'a1i', '%s e. RR' % F191), six], 'readdcld', '%s e. RR' % A_)
    pm = st([xp, ar_, st([er_], 'recnd', '%s e. CC' % E_)], 'cxpmuld', '( X ^c ( %s x. %s ) ) = ( %s ^c %s )' % (A_, E_, XA, E_))
    AE = '( %s x. %s )' % (A_, E_)
    pe = st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([st([ar_, er_], 'remulcld', '%s e. RR' % AE)], 'recnd', '%s e. CC' % AE)], 'cxpefd', '( X ^c %s ) = ( exp ` ( %s x. %s ) )' % (AE, AE, L))
    OT = '( 1 - %s )' % TAU
    otr = st([one, taur], 'resubcld', '%s e. RR' % OT)
    ot = lin.lineq(w, A0, OT, RL, leaves={RL: rlr})
    dc = st([st([rr], 'recnd', 'R e. CC'), st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L)], 'divcan1d', '( %s x. %s ) = R' % (RL, L))
    ol = st([st([ot], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (OT, L, RL, L)), dc], 'eqtrd', '( %s x. %s ) = R' % (OT, L))
    el = st([st([st([num.cc(w, F92)], 'a1i', '%s e. CC' % F92), st([otr], 'recnd', '%s e. CC' % OT), st([lr], 'recnd', '%s e. CC' % L)], 'mulassd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (E_, L, F92, OT, L)),
              st([ol], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. R )' % (F92, OT, L, F92))], 'eqtrd', '( %s x. %s ) = ( %s x. R )' % (E_, L, F92))
    ael = st([st([st([ar_], 'recnd', '%s e. CC' % A_), st([er_], 'recnd', '%s e. CC' % E_), st([lr], 'recnd', '%s e. CC' % L)], 'mulassd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (AE, L, A_, E_, L)),
               st([el], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. R ) )' % (A_, E_, L, A_, F92))], 'eqtrd', '( %s x. %s ) = ( %s x. ( %s x. R ) )' % (AE, L, A_, F92))
    aer = st([st([ar_, er_], 'remulcld', '%s e. RR' % AE), lr], 'remulcld', '( %s x. %s ) e. RR' % (AE, L))
    A5 = num.lit_text(__import__('fractions').Fraction(191, 900) + 6)
    a5 = lin.lineq(w, A0, A_, A5, leaves={})
    ael2 = st([ael, st([a5], 'oveq1d', '( %s x. ( %s x. R ) ) = ( %s x. ( %s x. R ) )' % (A_, F92, A5, F92))], 'eqtrd', '( %s x. %s ) = ( %s x. ( %s x. R ) )' % (AE, L, A5, F92))
    b28 = lin.linarith(w, A0, [ael2, st([rp], 'rpge0d', '0 <_ R')], '( %s x. %s ) <_ ( ; 2 8 x. R )' % (AE, L), closure=clos(w, A0, {'R': rr, '( %s x. %s )' % (AE, L): aer}))
    efm = st([b28, ap_(w, A0, [aer, st([st([num.real(w, '; 2 8')], 'a1i', '; 2 8 e. RR'), rr], 'remulcld', '( ; 2 8 x. R ) e. RR')], 'efle', '( ( %s x. %s ) <_ ( ; 2 8 x. R ) <-> ( exp ` ( %s x. %s ) ) <_ ( exp ` ( ; 2 8 x. R ) ) )' % (AE, L, AE, L))], 'mpbid',
             '( exp ` ( %s x. %s ) ) <_ ( exp ` ( ; 2 8 x. R ) )' % (AE, L))
    PW = '( %s ^c %s )' % (NX, E_)
    pwe = st([st([pw, st([pm, pe], 'eqtr3d', '( %s ^c %s ) = ( exp ` ( %s x. %s ) )' % (XA, E_, AE, L))], 'breqtrd', '%s <_ ( exp ` ( %s x. %s ) )' % (PW, AE, L)), efm], 'x', 'x') if False else None
    pw1 = st([pw, st([pm, pe], 'eqtr3d', '( %s ^c %s ) = ( exp ` ( %s x. %s ) )' % (XA, E_, AE, L))], 'breqtrd', '%s <_ ( exp ` ( %s x. %s ) )' % (PW, AE, L))
    EXP28 = '( exp ` ( ; 2 8 x. R ) )'
    pwr = st([nxr, nx0, er_], 'recxpcld', '%s e. RR' % PW)
    e28r = st([st([st([num.real(w, '; 2 8')], 'a1i', '; 2 8 e. RR'), rr], 'remulcld', '( ; 2 8 x. R ) e. RR')], 'reefcld', '%s e. RR' % EXP28)
    pwe = st([pwr, st([aer], 'reefcld', '( exp ` ( %s x. %s ) ) e. RR' % (AE, L)), e28r, pw1, efm], 'letrd', '%s <_ %s' % (PW, EXP28))
    g0 = lin.linarith(w, A0, [g1], '0 <_ G', leaves={'G': gr})
    gp = st([pwr, e28r, gr, g0, pwe], 'lemul2ad', '( G x. %s ) <_ ( G x. %s )' % (PW, EXP28))
    ncb = st([got2, gp], 'x', 'x') if False else None
    ncr, _ = nc_real(w, A0, nn, taur, t0, t1, b['x3r'], TAU, X3)
    ncb = st([ncr, st([gr, pwr], 'remulcld', '( G x. %s ) e. RR' % PW), st([gr, e28r], 'remulcld', '( G x. %s ) e. RR' % EXP28), got2, gp], 'letrd', '%s <_ ( G x. %s )' % (NC(TAU, X3), EXP28))
    yv0 = st([yr, vp, lin.linarith(w, A0, [y1], '0 <_ Y', leaves={'Y': yr})], 'divge0d', '0 <_ %s' % YV)
    fb = st([ncr, st([gr, e28r], 'remulcld', '( G x. %s ) e. RR' % EXP28), yvr, yv0, ncb], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( G x. %s ) )' % (YV, NC(TAU, X3), YV, EXP28))
    GE = '( G x. %s )' % EXP28
    gec = st([st([gr, e28r], 'remulcld', '%s e. RR' % GE)], 'recnd', '%s e. CC' % GE)
    fe = st([st([gec, st([yr], 'recnd', 'Y e. CC'), st([vp], 'rpcnd', 'V e. CC'), st([vp], 'rpne0d', 'V =/= 0')], 'divassd', '( ( %s x. Y ) / V ) = ( %s x. %s )' % (GE, GE, YV)),
             st([gec, st([yvr], 'recnd', '%s e. CC' % YV)], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (GE, YV, YV, GE))], 'eqtrd', '( ( %s x. Y ) / V ) = ( %s x. %s )' % (GE, YV, GE))
    ztr = st([DBfin, w.s([zfin, bwr], 'fsumrecl', '( %s -> sum_ q e. %s %s e. RR )' % (C1, ZT_, BW))], 'fsumrecl', '%s e. RR' % ZT(X3, 'Y', TAU))
    fin0 = st([ztr, st([yvr, ncr], 'remulcld', '( %s x. %s ) e. RR' % (YV, NC(TAU, X3))), st([yvr, st([gr, e28r], 'remulcld', '%s e. RR' % GE)], 'remulcld', '( %s x. %s ) e. RR' % (YV, GE)), zb, fb], 'letrd', '%s <_ ( %s x. %s )' % (ZT(X3, 'Y', TAU), YV, GE))
    fin = st([fin0, fe], 'breqtrrd', '%s <_ ( ( %s x. Y ) / V )' % (ZT(X3, 'Y', TAU), GE))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21z4']))
    return run(w)


if __name__ == '__main__':
    gen_z4()
