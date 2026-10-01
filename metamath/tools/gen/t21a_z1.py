"""Sortie T21a: zone I (t21wsi = Lean's h2/h3 of zoneI_le, t21z1 = zoneI_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_, run
import num, lin
import cl as _cl
lin.FASTPATH = True
lin.MAXDEG = 6
from tm import W

C64 = '; ; ; 6 4 0 0'
LAM = '( log ` ( N x. ( %s + 2 ) ) )' % X3


def x_basics(w, A0, xr, xe):
    """steps: 1 < e, 2 <_ X, 1 <_ X, X e. RR+, L e. RR, 1 <_ L, X^3 facts"""
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    one = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    e1r = st([one], 'reefcld', '( exp ` 1 ) e. RR')
    e2 = st([ap_(w, A0, [st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')], 'efgt1p', '( 1 + 1 ) < ( exp ` 1 )'), st([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2')], 'x', 'x') if False else None
    e2 = st([st([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2'), ap_(w, A0, [st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')], 'efgt1p', '( 1 + 1 ) < ( exp ` 1 )')], 'eqbrtrrd', '2 < ( exp ` 1 )')
    x2 = lin.linarith(w, A0, [e2, xe], '2 <_ X', leaves={'X': xr, '( exp ` 1 )': e1r})
    x1 = lin.linarith(w, A0, [x2], '1 <_ X', leaves={'X': xr})
    xp = st([xr, lin.linarith(w, A0, [x2], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    e1p = st([one], 'rpefcld', '( exp ` 1 ) e. RR+')
    lge = st([xe, st([e1p, xp], 'logled', '( ( exp ` 1 ) <_ X <-> ( log ` ( exp ` 1 ) ) <_ %s )' % LX)], 'mpbid', '( log ` ( exp ` 1 ) ) <_ %s' % LX)
    l1 = st([st([ap_(w, A0, [one], 'relogef', '( log ` ( exp ` 1 ) ) = 1')], 'eqcomd', '1 = ( log ` ( exp ` 1 ) )'), lge], 'eqbrtrd', '1 <_ %s' % LX)
    lr = st([xp], 'relogcld', '%s e. RR' % LX)
    x3r = st([xr, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'reexpcld', '%s e. RR' % X3)
    e8 = st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), xr, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0'), st([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), x2], 'leexp1ad', '( 2 ^ 3 ) <_ %s' % X3)
    x8 = st([st([w.s([], 'cu2', '( 2 ^ 3 ) = 8')], 'a1i', '( 2 ^ 3 ) = 8'), e8], 'eqbrtrrd', '8 <_ %s' % X3)
    t1 = lin.linarith(w, A0, [x8], '1 <_ %s' % X3, leaves={X3: x3r})
    return dict(one=one, x2=x2, x1=x1, xp=xp, l1=l1, lr=lr, x3r=x3r, x8=x8, t1=t1)


def gen_wsI():
    w = W('t21wsi', 'Zone I weight at ` T = X ^ 3 ` : ` sum_chi sum_rho ord / ( 1 + abs gamma ) <_ 160000 N log ^ 2 X ` , from (L-gamma), the crude count ` 6400 t N log ( N ( t + 2 ) ) ` and ` sum 1 / ( n + 1 ) <_ log ( floor T + 1 ) ` (Lean ` zoneI_le ` , steps ` h2 ` , ` h3 ` ; ~ t21lgs , ~ zc1sum , ~ t21harm , ~ t21ld ).')
    A0 = ante_of(S['t21wsi'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L_ = lambda s_, A_: _cl.lift(w, s_, A_)
    u = unpack(w, A0)
    nn, xr, xe, nx = u['N e. NN'], u['X e. RR'], u['( exp ` 1 ) <_ X'], u['N <_ ( X ^c %s )' % F191]
    b = x_basics(w, A0, xr, xe)
    x3r, lr = b['x3r'], b['lr']
    two = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    nr = st([nn], 'nnred', 'N e. RR'); n1 = st([nn], 'nnge1d', '1 <_ N'); n0 = st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')
    lam = ap_(w, A0, [xr, b['x2'], nr, n1, nx], 't21ld', '%s <_ ( 5 x. %s )' % (LAM, LX))
    T2 = '( %s + 2 )' % X3
    t2r = st([x3r, two], 'readdcld', '%s e. RR' % T2)
    NT2 = '( N x. %s )' % T2
    nt2r = st([nr, t2r], 'remulcld', '%s e. RR' % NT2)
    nt21 = lin.nlinarith(w, A0, [n1, b['x8']], '1 <_ %s' % NT2, leaves={'N': nr, X3: x3r})
    ntp = st([nt2r, lin.linarith(w, A0, [nt21], '0 < %s' % NT2, leaves={NT2: nt2r})], 'elrpd', '%s e. RR+' % NT2)
    lamr = st([ntp], 'relogcld', '%s e. RR' % LAM)
    lam0 = st([nt2r, nt21], 'logge0d', '0 <_ %s' % LAM)
    hr = st([num.real(w, HALF)], 'a1i', '%s e. RR' % HALF)
    FLX = '( 1 ... ( |_ ` %s ) )' % X3
    SN = 'sum_ n e. %s ( %s / ( n x. ( n + 1 ) ) )' % (FLX, NC(HALF, 'n'))
    lg = ap_(w, A0, [nn, hr, st([num.le_lit(w, '0', HALF, strict=True)], 'a1i', '0 < %s' % HALF), st([num.le_lit(w, HALF, '1')], 'a1i', '%s <_ 1' % HALF), x3r, b['t1']], 't21lgs',
             '%s <_ ( ( %s / %s ) + %s )' % (WS(HALF, X3), NC(HALF, X3), X3, SN))
    NLAM = '( N x. %s )' % LAM
    KV = '( %s x. %s )' % (C64, NLAM)
    nlr = st([nr, lamr], 'remulcld', '%s e. RR' % NLAM)
    kvr = st([st([num.real(w, C64)], 'a1i', '%s e. RR' % C64), nlr], 'remulcld', '%s e. RR' % KV)
    kv0 = st([st([num.real(w, C64)], 'a1i', '%s e. RR' % C64), nlr, st([num.le_lit(w, '0', C64)], 'a1i', '0 <_ %s' % C64), st([nr, lamr, n0, lam0], 'mulge0d', '0 <_ %s' % NLAM)], 'mulge0d', '0 <_ %s' % KV)
    # first term
    zT = ap_(w, A0, [nn, x3r, b['t1']], 'zc1sum', '%s <_ ( %s x. ( ( %s x. N ) x. %s ) )' % (NC(HALF, X3), C64, X3, LAM))
    x3p = st([x3r, lin.linarith(w, A0, [b['x8']], '0 < %s' % X3, leaves={X3: x3r})], 'elrpd', '%s e. RR+' % X3)
    c = _cl.Closure(w, A0, {})
    for E_, s_ in [('N', nr), (X3, x3r), (LAM, lamr)]:
        c.leaf(E_, 'RR', s_)
    idT = lin.lineq(w, A0, '( %s x. %s )' % (X3, KV), '( %s x. ( ( %s x. N ) x. %s ) )' % (C64, X3, LAM), closure=c, products=True)
    ncTr = st([nn, hr, st([num.le_lit(w, '0', HALF, strict=True)], 'a1i', '0 < %s' % HALF), st([num.le_lit(w, HALF, '1')], 'a1i', '%s <_ 1' % HALF), x3r], 'x', 'x') if False else None
    ncT, _ = nc_real(w, A0, nn, hr, st([num.le_lit(w, '0', HALF, strict=True)], 'a1i', '0 < %s' % HALF), st([num.le_lit(w, HALF, '1')], 'a1i', '%s <_ 1' % HALF), x3r, HALF, X3)
    f1 = st([st([zT, idT], 'breqtrrd', '%s <_ ( %s x. %s )' % (NC(HALF, X3), X3, KV)), st([ncT, kvr, x3p], 'ledivmuld', '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (NC(HALF, X3), X3, KV, NC(HALF, X3), X3, KV))], 'mpbird',
            '( %s / %s ) <_ %s' % (NC(HALF, X3), X3, KV))
    # n terms
    Cn = '( %s /\\ n e. %s )' % (A0, FLX)
    Ln = lambda s_: L_(s_, Cn)
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (Cn, FLX))
    nnn = ap_(w, Cn, [nin], 'elfznn', 'n e. NN')
    nr_ = w.s([nnn], 'nnred', '( %s -> n e. RR )' % Cn)
    ftr = w.s([w.s([Ln(x3r)], 'flcld', '( %s -> ( |_ ` %s ) e. ZZ )' % (Cn, X3))], 'zred', '( %s -> ( |_ ` %s ) e. RR )' % (Cn, X3))
    nT = w.s([nr_, ftr, Ln(x3r), ap_(w, Cn, [nin], 'elfzle2', 'n <_ ( |_ ` %s )' % X3), ap_(w, Cn, [Ln(x3r)], 'flle', '( |_ ` %s ) <_ %s' % (X3, X3))], 'letrd', '( %s -> n <_ %s )' % (Cn, X3))
    zn = ap_(w, Cn, [Ln(nn), nr_, w.s([nnn], 'nnge1d', '( %s -> 1 <_ n )' % Cn)], 'zc1sum', '%s <_ ( %s x. ( ( n x. N ) x. ( log ` ( N x. ( n + 2 ) ) ) ) )' % (NC(HALF, 'n'), C64))
    N2 = '( N x. ( n + 2 ) )'
    n2r = w.s([nr_, Ln(two)], 'readdcld', '( %s -> ( n + 2 ) e. RR )' % Cn)
    n2p = w.s([w.s([Ln(nr), n2r], 'remulcld', '( %s -> %s e. RR )' % (Cn, N2)), lin.nlinarith(w, Cn, [Ln(n1), w.s([nnn], 'nnge1d', '( %s -> 1 <_ n )' % Cn)], '0 < %s' % N2, leaves={'N': Ln(nr), 'n': nr_})], 'elrpd', '( %s -> %s e. RR+ )' % (Cn, N2))
    nle = w.s([n2r, Ln(t2r), Ln(nr), Ln(n0), lin.linarith(w, Cn, [nT], '( n + 2 ) <_ %s' % T2, leaves={'n': nr_, X3: Ln(x3r)})], 'lemul2ad', '( %s -> %s <_ %s )' % (Cn, N2, NT2))
    lle = w.s([nle, w.s([n2p, Ln(ntp)], 'logled', '( %s -> ( %s <_ %s <-> ( log ` %s ) <_ %s ) )' % (Cn, N2, NT2, N2, LAM))], 'mpbid', '( %s -> ( log ` %s ) <_ %s )' % (Cn, N2, LAM))
    NN_ = '( n x. N )'
    nnr_ = w.s([nr_, Ln(nr)], 'remulcld', '( %s -> %s e. RR )' % (Cn, NN_))
    nn0_ = w.s([nr_, Ln(nr), w.s([w.s([nnn], 'nnrpd', '( %s -> n e. RR+ )' % Cn)], 'rpge0d', '( %s -> 0 <_ n )' % Cn), Ln(n0)], 'mulge0d', '( %s -> 0 <_ %s )' % (Cn, NN_))
    m1 = w.s([w.s([n2p], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (Cn, N2)), Ln(lamr), nnr_, nn0_, lle], 'lemul2ad', '( %s -> ( %s x. ( log ` %s ) ) <_ ( %s x. %s ) )' % (Cn, NN_, N2, NN_, LAM))
    m2 = w.s([w.s([nnr_, w.s([n2p], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (Cn, N2))], 'remulcld', '( %s -> ( %s x. ( log ` %s ) ) e. RR )' % (Cn, NN_, N2)), w.s([nnr_, Ln(lamr)], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Cn, NN_, LAM)),
              w.s([num.real(w, C64)], 'a1i', '( %s -> %s e. RR )' % (Cn, C64)), w.s([num.le_lit(w, '0', C64)], 'a1i', '( %s -> 0 <_ %s )' % (Cn, C64)), m1], 'lemul2ad',
             '( %s -> ( %s x. ( %s x. ( log ` %s ) ) ) <_ ( %s x. ( %s x. %s ) ) )' % (Cn, C64, NN_, N2, C64, NN_, LAM))
    zn2 = w.s([zn, m2], 'x', 'x') if False else None
    D = '( n x. ( n + 1 ) )'
    R = '( 1 / ( n + 1 ) )'
    n1p = w.s([w.s([nnn], 'peano2nnd', '( %s -> ( n + 1 ) e. NN )' % Cn)], 'nnrpd', '( %s -> ( n + 1 ) e. RR+ )' % Cn)
    rr = w.s([w.s([n1p], 'rpreccld', '( %s -> %s e. RR+ )' % (Cn, R))], 'rpred', '( %s -> %s e. RR )' % (Cn, R))
    KR = '( %s x. %s )' % (KV, R)
    cn = _cl.Closure(w, Cn, {})
    for E_, s_ in [('n', nr_), ('N', Ln(nr)), (LAM, Ln(lamr)), (R, rr)]:
        cn.leaf(E_, 'RR', s_)
    i1 = lin.lineq(w, Cn, '( %s x. %s )' % (D, KR), '( ( n x. %s ) x. ( ( n + 1 ) x. %s ) )' % (KV, R), closure=cn, products=True)
    rc = w.s([w.s([n1p], 'rpcnd', '( %s -> ( n + 1 ) e. CC )' % Cn), w.s([n1p], 'rpne0d', '( %s -> ( n + 1 ) =/= 0 )' % Cn)], 'recidd', '( %s -> ( ( n + 1 ) x. %s ) = 1 )' % (Cn, R))
    i2 = w.s([w.s([rc], 'oveq2d', '( %s -> ( ( n x. %s ) x. ( ( n + 1 ) x. %s ) ) = ( ( n x. %s ) x. 1 ) )' % (Cn, KV, R, KV)), w.s([w.s([w.s([nr_, Ln(kvr)], 'remulcld', '( %s -> ( n x. %s ) e. RR )' % (Cn, KV))], 'recnd', '( %s -> ( n x. %s ) e. CC )' % (Cn, KV))], 'mulridd', '( %s -> ( ( n x. %s ) x. 1 ) = ( n x. %s ) )' % (Cn, KV, KV))], 'eqtrd',
             '( %s -> ( ( n x. %s ) x. ( ( n + 1 ) x. %s ) ) = ( n x. %s ) )' % (Cn, KV, R, KV))
    i3 = lin.lineq(w, Cn, '( n x. %s )' % KV, '( %s x. ( %s x. %s ) )' % (C64, NN_, LAM), closure=cn, products=True)
    ide = w.s([w.s([i1, i2], 'eqtrd', '( %s -> ( %s x. %s ) = ( n x. %s ) )' % (Cn, D, KR, KV)), i3], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. %s ) ) )' % (Cn, D, KR, C64, NN_, LAM))
    ncn, _ = nc_real(w, Cn, Ln(nn), Ln(hr), Ln(st([num.le_lit(w, '0', HALF, strict=True)], 'a1i', '0 < %s' % HALF)), Ln(st([num.le_lit(w, HALF, '1')], 'a1i', '%s <_ 1' % HALF)), nr_, HALF, 'n')
    zle = w.s([ncn, w.s([w.s([num.real(w, C64)], 'a1i', '( %s -> %s e. RR )' % (Cn, C64)), w.s([nnr_, w.s([n2p], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (Cn, N2))], 'remulcld', '( %s -> ( %s x. ( log ` %s ) ) e. RR )' % (Cn, NN_, N2))], 'remulcld', '( %s -> ( %s x. ( %s x. ( log ` %s ) ) ) e. RR )' % (Cn, C64, NN_, N2)),
              w.s([w.s([num.real(w, C64)], 'a1i', '( %s -> %s e. RR )' % (Cn, C64)), w.s([nnr_, Ln(lamr)], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Cn, NN_, LAM))], 'remulcld', '( %s -> ( %s x. ( %s x. %s ) ) e. RR )' % (Cn, C64, NN_, LAM)), zn, m2], 'letrd',
             '( %s -> %s <_ ( %s x. ( %s x. %s ) ) )' % (Cn, NC(HALF, 'n'), C64, NN_, LAM))
    dp = w.s([w.s([nnn, w.s([nnn], 'peano2nnd', '( %s -> ( n + 1 ) e. NN )' % Cn)], 'nnmulcld', '( %s -> %s e. NN )' % (Cn, D))], 'nnrpd', '( %s -> %s e. RR+ )' % (Cn, D))
    krr = w.s([Ln(kvr), rr], 'remulcld', '( %s -> %s e. RR )' % (Cn, KR))
    tn = w.s([w.s([zle, ide], 'breqtrrd', '( %s -> %s <_ ( %s x. %s ) )' % (Cn, NC(HALF, 'n'), D, KR)), w.s([ncn, krr, dp], 'ledivmuld', '( %s -> ( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) ) )' % (Cn, NC(HALF, 'n'), D, KR, NC(HALF, 'n'), D, KR))], 'mpbird',
             '( %s -> ( %s / %s ) <_ %s )' % (Cn, NC(HALF, 'n'), D, KR))
    fzf = st([], 'fzfid', '%s e. Fin' % FLX)
    tnr = w.s([ncn, dp], 'rerpdivcld', '( %s -> ( %s / %s ) e. RR )' % (Cn, NC(HALF, 'n'), D))
    s1 = st([fzf, tnr, krr, tn], 'fsumle', '%s <_ sum_ n e. %s %s' % (SN, FLX, KR))
    SR = 'sum_ n e. %s %s' % (FLX, R)
    s2 = st([fzf, st([kvr], 'recnd', '%s e. CC' % KV), w.s([rr], 'recnd', '( %s -> %s e. CC )' % (Cn, R))], 'fsummulc2', '( %s x. %s ) = sum_ n e. %s %s' % (KV, SR, FLX, KR))
    hm = ap_(w, A0, [x3r, b['t1']], 't21harm', '%s <_ ( log ` ( ( |_ ` %s ) + 1 ) )' % (SR, X3))
    LF = '( log ` ( ( |_ ` %s ) + 1 ) )' % X3
    # log ( floor T + 1 ) <_ 4 L
    FT1 = '( ( |_ ` %s ) + 1 )' % X3
    ftr0 = st([st([x3r], 'flcld', '( |_ ` %s ) e. ZZ' % X3)], 'zred', '( |_ ` %s ) e. RR' % X3)
    X4 = '( X ^ 4 )'
    x4e = st([st([xr], 'recnd', 'X e. CC'), st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'expp1d', '( X ^ ( 3 + 1 ) ) = ( %s x. X )' % X3)
    x4e2 = st([st([st([w.s([], '3p1e4', '( 3 + 1 ) = 4')], 'a1i', '( 3 + 1 ) = 4')], 'oveq2d', '( X ^ ( 3 + 1 ) ) = %s' % X4), x4e], 'eqtr3d', '%s = ( %s x. X )' % (X4, X3))
    x4r = st([xr, st([w.s([], '4nn0', '4 e. NN0')], 'a1i', '4 e. NN0')], 'reexpcld', '%s e. RR' % X4)
    cx = _cl.Closure(w, A0, {})
    for E_, s_ in [('X', xr), (X3, x3r), (X4, x4r), ('( |_ ` %s )' % X3, ftr0)]:
        cx.leaf(E_, 'RR', s_)
    x41 = lin.nlinarith(w, A0, [b['x2'], b['x8'], x4e2], '( %s + 1 ) <_ %s' % (X3, X4), closure=cx)
    fl1 = lin.linarith(w, A0, [ap_(w, A0, [x3r], 'flle', '( |_ ` %s ) <_ %s' % (X3, X3)), x41], '%s <_ %s' % (FT1, X4), closure=cx)
    ft1p = st([st([ftr0], 'peano2re' if False else 'x', 'x') if False else ap_(w, A0, [ftr0], 'peano2re', '%s e. RR' % FT1), lin.linarith(w, A0, [ap_(w, A0, [x3r, st([w.s([], '0z', '0 e. ZZ')], 'a1i', '0 e. ZZ')], 'flge', '( 0 <_ %s <-> 0 <_ ( |_ ` %s ) )' % (X3, X3)) and st([lin.linarith(w, A0, [b['x8']], '0 <_ %s' % X3, closure=cx), ap_(w, A0, [x3r, st([w.s([], '0z', '0 e. ZZ')], 'a1i', '0 e. ZZ')], 'flge', '( 0 <_ %s <-> 0 <_ ( |_ ` %s ) )' % (X3, X3))], 'mpbid', '0 <_ ( |_ ` %s )' % X3)], '0 < %s' % FT1, closure=cx)], 'elrpd', '%s e. RR+' % FT1)
    x4p = st([b['xp'], st([num.z_nat(w, 4)], 'a1i', '4 e. ZZ')], 'rpexpcld', '%s e. RR+' % X4)
    lf = st([fl1, st([ft1p, x4p], 'logled', '( %s <_ %s <-> %s <_ ( log ` %s ) )' % (FT1, X4, LF, X4))], 'mpbid', '%s <_ ( log ` %s )' % (LF, X4))
    l4 = ap_(w, A0, [b['xp'], st([num.z_nat(w, 4)], 'a1i', '4 e. ZZ')], 'relogexp', '( log ` %s ) = ( 4 x. %s )' % (X4, LX))
    lf4 = st([lf, l4], 'breqtrd', '%s <_ ( 4 x. %s )' % (LF, LX))
    # assemble: WS <_ KV + KV x. LF <_ 160000 N L^2
    lfr = st([ft1p], 'relogcld', '%s e. RR' % LF)
    srr = st([fzf, rr], 'fsumrecl', '%s e. RR' % SR)
    q1 = st([srr, lfr, kvr, kv0, hm], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (KV, SR, KV, LF))
    q2 = st([lfr, st([st([w.s([], '4re', '4 e. RR')], 'a1i', '4 e. RR'), lr], 'remulcld', '( 4 x. %s ) e. RR' % LX), kvr, kv0, lf4], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 4 x. %s ) )' % (KV, LF, KV, LX))
    P1 = st([lamr, st([st([w.s([], '5re', '5 e. RR')], 'a1i', '5 e. RR'), lr], 'remulcld', '( 5 x. %s ) e. RR' % LX), nr, n0, lam], 'lemul2ad', '%s <_ ( N x. ( 5 x. %s ) )' % (NLAM, LX))
    l0 = lin.linarith(w, A0, [b['l1']], '0 <_ %s' % LX, leaves={LX: lr})
    F1 = st([nlr, st([nr, st([st([w.s([], '5re', '5 e. RR')], 'a1i', '5 e. RR'), lr], 'remulcld', '( 5 x. %s ) e. RR' % LX)], 'remulcld', '( N x. ( 5 x. %s ) ) e. RR' % LX), lr, l0, P1], 'lemul1ad', '( %s x. %s ) <_ ( ( N x. ( 5 x. %s ) ) x. %s )' % (NLAM, LX, LX, LX))
    LL = '( %s x. ( %s - 1 ) )' % (LX, LX)
    F2 = st([nr, st([lr, st([lr, st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % LX)], 'remulcld', '%s e. RR' % LL), n0,
             st([lr, st([lr, st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % LX), l0, lin.linarith(w, A0, [b['l1']], '0 <_ ( %s - 1 )' % LX, leaves={LX: lr})], 'mulge0d', '0 <_ %s' % LL)], 'mulge0d', '0 <_ ( N x. %s )' % LL)
    L2e = st([st([lr], 'recnd', '%s e. CC' % LX)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (LX, LX, LX))
    cf = _cl.Closure(w, A0, {})
    for E_, s_ in [('N', nr), (LX, lr), (LAM, lamr), (SR, srr), (LF, lfr), (NC(HALF, X3), ncT), (SN, st([fzf, tnr], 'fsumrecl', '%s e. RR' % SN)), ('sum_ n e. %s %s' % (FLX, KR), st([fzf, krr], 'fsumrecl', 'sum_ n e. %s %s e. RR' % (FLX, KR)))]:
        cf.leaf(E_, 'RR', s_)
    for E_ in ['( %s / %s )' % (NC(HALF, X3), X3), WS(HALF, X3), '( %s ^ 2 )' % LX]:
        cf.atom(E_)
    cf.leaf('( %s / %s )' % (NC(HALF, X3), X3), 'RR', st([ncT, x3p], 'rerpdivcld', '( %s / %s ) e. RR' % (NC(HALF, X3), X3)))
    cf.leaf(WS(HALF, X3), 'RR', ws_real(w, A0, nn, hr, st([num.le_lit(w, '0', HALF, strict=True)], 'a1i', '0 < %s' % HALF), st([num.le_lit(w, HALF, '1')], 'a1i', '%s <_ 1' % HALF), x3r, HALF, X3))
    cf.leaf('( %s ^ 2 )' % LX, 'RR', st([lr], 'resqcld', '( %s ^ 2 ) e. RR' % LX))
    C16 = '; ; ; ; ; 1 6 0 0 0 0'
    LLx = '( %s x. %s )' % (LX, LX)
    fin0 = lin.linarith(w, A0, [lg, f1, s1, s2, q1, q2, P1, F1, F2], '%s <_ ( %s x. ( N x. %s ) )' % (WS(HALF, X3), C16, LLx), closure=cf, products=True)
    eqq = st([st([st([L2e], 'eqcomd', '%s = ( %s ^ 2 )' % (LLx, LX))], 'oveq2d', '( N x. %s ) = ( N x. ( %s ^ 2 ) )' % (LLx, LX))], 'oveq2d', '( %s x. ( N x. %s ) ) = ( %s x. ( N x. ( %s ^ 2 ) ) )' % (C16, LLx, C16, LX))
    fin = st([fin0, eqq], 'breqtrd', '%s <_ ( %s x. ( N x. ( %s ^ 2 ) ) )' % (WS(HALF, X3), C16, LX))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21wsi']))
    return run(w)

def gen_z1():
    w = W('t21z1', 'Zone I ( ` 1 / 2 <_ beta < 39 / 50 ` ) at ` T = X ^ 3 ` : ` S_I <_ 160000 N log ^ 2 X Y ^ ( 39 / 50 ) <_ E Y / 27 ` once ` 4320000 log ^ 2 X <_ E X ^ ( 7 / 900 ) ` (Lean ` zoneI_le ` with the box count 6400 for 1120; ~ t21wsi , ~ t21dpow ).')
    A0 = ante_of(S['t21z1'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L_ = lambda s_, A_: _cl.lift(w, s_, A_)
    u = unpack(w, A0)
    nn, xr, xe, yr, er, nx, ny = [u[k] for k in ['N e. NN', 'X e. RR', '( exp ` 1 ) <_ X', 'Y e. RR', 'E e. RR', 'N <_ ( X ^c %s )' % F191, '( N x. ( X ^c %s ) ) <_ Y' % F709]]
    C43 = '; ; ; ; ; ; 4 3 2 0 0 0 0'; C16 = '; ; ; ; ; 1 6 0 0 0 0'
    L2 = '( %s ^ 2 )' % LX
    hx = u['( %s x. %s ) <_ ( E x. ( X ^c %s ) )' % (C43, L2, F7900)]
    b = x_basics(w, A0, xr, xe)
    nr = st([nn], 'nnred', 'N e. RR'); n1 = st([nn], 'nnge1d', '1 <_ N'); n0 = st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')
    X7p = '( X ^c %s )' % F709
    x70 = st([xr, b['x1'], st([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), st([num.real(w, F709)], 'a1i', '%s e. RR' % F709), st([num.le_lit(w, '0', F709)], 'a1i', '0 <_ %s' % F709)], 'cxplead', '( X ^c 0 ) <_ %s' % X7p)
    x71 = st([st([st([xr], 'recnd', 'X e. CC')], 'cxp0d', '( X ^c 0 ) = 1'), x70], 'eqbrtrrd', '1 <_ %s' % X7p)
    x7r = st([st([b['xp'], st([num.real(w, F709)], 'a1i', '%s e. RR' % F709)], 'rpcxpcld', '%s e. RR+' % X7p)], 'rpred', '%s e. RR' % X7p)
    m11 = st([b['one'], nr, b['one'], x7r, st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), n1, x71], 'lemul12ad', '( 1 x. 1 ) <_ ( N x. %s )' % X7p)
    y1 = st([b['one'], st([nr, x7r], 'remulcld', '( N x. %s ) e. RR' % X7p), yr, st([st([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'), m11], 'eqbrtrrd', '1 <_ ( N x. %s )' % X7p), ny], 'letrd', '1 <_ Y')
    yp = st([yr, lin.linarith(w, A0, [y1], '0 < Y', leaves={'Y': yr})], 'elrpd', 'Y e. RR+'); y0 = st([yp], 'rpge0d', '0 <_ Y')
    Y39 = '( Y ^c %s )' % F3950; Y11 = '( Y ^c ( ; 1 1 / ; 5 0 ) )'
    f39 = st([num.real(w, F3950)], 'a1i', '%s e. RR' % F3950)
    y39r = st([yr, y0, f39], 'recxpcld', '%s e. RR' % Y39); y390 = st([yr, y0, f39], 'cxpge0d', '0 <_ %s' % Y39)
    # step 1: zone <_ Y39 x. WS
    Z0, Z1 = ZFX(HALF, X3), ZFX(F3950, X3)
    DD = '( %s \\ %s )' % (Z0, Z1)
    C1 = '( %s /\\ x e. %s )' % (A0, DB)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (C1, DB))
    hr = st([num.real(w, HALF)], 'a1i', '%s e. RR' % HALF)
    h0 = st([num.le_lit(w, '0', HALF, strict=True)], 'a1i', '0 < %s' % HALF); h1 = st([num.le_lit(w, HALF, '1')], 'a1i', '%s <_ 1' % HALF)
    ez = ap_(w, C1, [L_(nn, C1), xin, L_(hr, C1), L_(h0, C1), L_(h1, C1), L_(b['x3r'], C1)], 'ezf', '( %s e. Fin /\\ A. q e. %s %s e. NN )' % (Z0, Z0, ORD()))
    z0f = w.s([ez], 'simpld', '( %s -> %s e. Fin )' % (C1, Z0))
    C2 = '( %s /\\ q e. %s )' % (C1, Z0)
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, Z0))
    qf = q_facts(w, C2, qin, L_(hr, C2), L_(b['x3r'], C2), HALF, X3)
    ordn = w.s([L_(w.s([ez], 'simprd', '( %s -> A. q e. %s %s e. NN )' % (C1, Z0, ORD())), C2), qin, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (Z0, ORD(), Z0, ORD()))], 'sylc', '( %s -> %s e. NN )' % (C2, ORD()))
    wr, w0, _ = wt_facts(w, C2, w.s([ordn], 'nnred', '( %s -> %s e. RR )' % (C2, ORD())), w.s([w.s([ordn], 'nnnn0d', '( %s -> %s e. NN0 )' % (C2, ORD()))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (C2, ORD())), qf)
    YW = '( %s x. %s )' % (Y39, WT())
    ywr = w.s([L_(y39r, C2), wr], 'remulcld', '( %s -> %s e. RR )' % (C2, YW))
    yw0 = w.s([L_(y39r, C2), wr, L_(y390, C2), w0], 'mulge0d', '( %s -> 0 <_ %s )' % (C2, YW))
    C3 = '( %s /\\ q e. %s )' % (C1, DD)
    zd = ap_(w, C3, [L_(hr, C3), L_(f39, C3), L_(b['x3r'], C3), w.s([], 'simpr', '( %s -> q e. %s )' % (C3, DD))], 't21zfd', '( q e. %s /\\ ( Re ` q ) < %s )' % (Z0, F3950))
    m32 = w.s([w.s([], 'simpl', '( %s -> %s )' % (C3, C1)), w.s([zd], 'simpld', '( %s -> q e. %s )' % (C3, Z0))], 'jca', '( %s -> %s )' % (C3, C2))
    v3 = lambda s_, f: w.s([m32, s_], 'syl', '( %s -> %s )' % (C3, f))
    re3 = v3(qf['re'], '( Re ` q ) e. RR')
    ylt = w.s([L_(yr, C3), L_(y1, C3), re3, L_(f39, C3), w.s([w.s([zd], 'simprd', '( %s -> ( Re ` q ) < %s )' % (C3, F3950))], 'ltled', '( %s -> ( Re ` q ) <_ %s )' % (C3, F3950))], 'cxplead', '( %s -> ( Y ^c ( Re ` q ) ) <_ %s )' % (C3, Y39))
    yre3 = w.s([L_(yr, C3), L_(y0, C3), re3], 'recxpcld', '( %s -> ( Y ^c ( Re ` q ) ) e. RR )' % C3)
    bw = w.s([yre3, L_(y39r, C3), v3(wr, '%s e. RR' % WT()), v3(w0, '0 <_ %s' % WT()), ylt], 'lemul2ad', '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) <_ ( %s x. %s ) )' % (C3, WT(), WT(), Y39))
    bw2 = w.s([bw, w.s([w.s([v3(wr, '%s e. RR' % WT())], 'recnd', '( %s -> %s e. CC )' % (C3, WT())), L_(st([y39r], 'recnd', '%s e. CC' % Y39), C3)], 'mulcomd', '( %s -> ( %s x. %s ) = %s )' % (C3, WT(), Y39, YW))], 'breqtrd',
              '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) <_ %s )' % (C3, WT(), YW))
    dfin = ap_(w, C1, [z0f], 'diffi', '%s e. Fin' % DD)
    lhsb = w.s([v3(wr, '%s e. RR' % WT()), yre3], 'remulcld', '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) e. RR )' % (C3, WT()))
    a1 = w.s([dfin, lhsb, v3(ywr, '%s e. RR' % YW), bw2], 'fsumle', '( %s -> sum_ q e. %s ( %s x. ( Y ^c ( Re ` q ) ) ) <_ sum_ q e. %s %s )' % (C1, DD, WT(), DD, YW))
    a2 = w.s([z0f, ywr, yw0, w.s([w.s([], 'difss', '%s C_ %s' % (DD, Z0))], 'a1i', '( %s -> %s C_ %s )' % (C1, DD, Z0))], 'fsumless', '( %s -> sum_ q e. %s %s <_ sum_ q e. %s %s )' % (C1, DD, YW, Z0, YW))
    a3 = w.s([z0f, L_(st([y39r], 'recnd', '%s e. CC' % Y39), C1), w.s([wr], 'recnd', '( %s -> %s e. CC )' % (C2, WT()))], 'fsummulc2', '( %s -> ( %s x. sum_ q e. %s %s ) = sum_ q e. %s %s )' % (C1, Y39, Z0, WT(), Z0, YW))
    IZ = 'sum_ q e. %s ( %s x. ( Y ^c ( Re ` q ) ) )' % (DD, WT())
    SW0 = 'sum_ q e. %s %s' % (Z0, WT())
    izr = w.s([dfin, lhsb], 'fsumrecl', '( %s -> %s e. RR )' % (C1, IZ))
    sywr = w.s([z0f, ywr], 'fsumrecl', '( %s -> sum_ q e. %s %s e. RR )' % (C1, DD, YW)) if False else w.s([dfin, v3(ywr, '%s e. RR' % YW)], 'fsumrecl', '( %s -> sum_ q e. %s %s e. RR )' % (C1, DD, YW))
    sy0 = w.s([z0f, ywr], 'fsumrecl', '( %s -> sum_ q e. %s %s e. RR )' % (C1, Z0, YW))
    per = w.s([izr, sywr, sy0, a1, a2], 'letrd', '( %s -> %s <_ sum_ q e. %s %s )' % (C1, IZ, Z0, YW))
    per2 = w.s([per, a3], 'breqtrrd', '( %s -> %s <_ ( %s x. %s ) )' % (C1, IZ, Y39, SW0))
    DBfin = w.s([nn, w.s([w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'), w.s([], 'eqid', '%s = %s' % (DB, DB))], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB)], 'syl', '( %s -> %s e. Fin )' % (A0, DB))
    sw0r = w.s([z0f, wr], 'fsumrecl', '( %s -> %s e. RR )' % (C1, SW0))
    o1 = st([DBfin, izr, w.s([L_(y39r, C1), sw0r], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (C1, Y39, SW0)), per2], 'fsumle', '%s <_ sum_ x e. %s ( %s x. %s )' % (ZS(X3, 'Y', HALF, F3950), DB, Y39, SW0))
    o2 = st([DBfin, st([y39r], 'recnd', '%s e. CC' % Y39), w.s([sw0r], 'recnd', '( %s -> %s e. CC )' % (C1, SW0))], 'fsummulc2', '( %s x. %s ) = sum_ x e. %s ( %s x. %s )' % (Y39, WS(HALF, X3), DB, Y39, SW0))
    zs1 = st([o1, o2], 'breqtrrd', '%s <_ ( %s x. %s )' % (ZS(X3, 'Y', HALF, F3950), Y39, WS(HALF, X3)))
    # step 2
    wsI = ap_(w, A0, [nn, xr, xe, nx], 't21wsi', '%s <_ ( %s x. ( N x. %s ) )' % (WS(HALF, X3), C16, L2))
    # step 3: level
    F11 = '( ; 1 1 / ; 5 0 )'
    EXX = '( ( %s x. ( 1 - %s ) ) - ( %s x. %s ) )' % (F191, F11, F709, F11)
    lr_ = lambda t_: st([num.real(w, t_)], 'a1i', '%s e. RR' % t_)
    dp_ = ap_(w, A0, [xr, b['x1'], nr, n1, nx, lr_(F191), lr_(F709), yr, ny, b['one'], lr_(F11), st([num.le_lit(w, '0', F11)], 'a1i', '0 <_ %s' % F11), st([num.le_lit(w, F11, '1')], 'a1i', '%s <_ 1' % F11)], 't21dpow',
              '( N ^c 1 ) <_ ( ( X ^c %s ) x. %s )' % (EXX, Y11))
    exe = lin.lineq(w, A0, EXX, '-u %s' % F7900, leaves={})
    Xm7 = '( X ^c -u %s )' % F7900; X7 = '( X ^c %s )' % F7900
    lev = st([st([st([st([nr], 'recnd', 'N e. CC')], 'cxp1d', '( N ^c 1 ) = N'), dp_], 'eqbrtrrd', 'N <_ ( ( X ^c %s ) x. %s )' % (EXX, Y11)),
              st([st([exe], 'oveq2d', '( X ^c %s ) = %s' % (EXX, Xm7))], 'oveq1d', '( ( X ^c %s ) x. %s ) = ( %s x. %s )' % (EXX, Y11, Xm7, Y11))], 'breqtrd', 'N <_ ( %s x. %s )' % (Xm7, Y11))
    # step 4
    x7p = st([b['xp'], lr_(F7900)], 'rpcxpcld', '%s e. RR+' % X7)
    xm7p = st([b['xp'], st([num.real(w, '-u %s' % F7900)], 'a1i', '-u %s e. RR' % F7900)], 'rpcxpcld', '%s e. RR+' % Xm7)
    y11r = st([yr, y0, lr_(F11)], 'recxpcld', '%s e. RR' % Y11); y110 = st([yr, y0, lr_(F11)], 'cxpge0d', '0 <_ %s' % Y11)
    XY = '( %s x. %s )' % (Xm7, Y11)
    xyr = st([st([xm7p], 'rpred', '%s e. RR' % Xm7), y11r], 'remulcld', '%s e. RR' % XY)
    xy0 = st([st([xm7p], 'rpred', '%s e. RR' % Xm7), y11r, st([xm7p], 'rpge0d', '0 <_ %s' % Xm7), y110], 'mulge0d', '0 <_ %s' % XY)
    CL = '( %s x. %s )' % (C43, L2)
    l2r = st([b['lr']], 'resqcld', '%s e. RR' % L2)
    clr = st([lr_(C43), l2r], 'remulcld', '%s e. RR' % CL)
    cl0 = st([lr_(C43), l2r, st([num.le_lit(w, '0', C43)], 'a1i', '0 <_ %s' % C43), st([b['lr']], 'sqge0d', '0 <_ %s' % L2)], 'mulge0d', '0 <_ %s' % CL)
    p1 = st([nr, xyr, clr, cl0, lev], 'lemul2ad', '( %s x. N ) <_ ( %s x. %s )' % (CL, CL, XY))
    EX7 = '( E x. %s )' % X7
    ex7r = st([er, st([x7p], 'rpred', '%s e. RR' % X7)], 'remulcld', '%s e. RR' % EX7)
    p2 = st([clr, ex7r, xyr, xy0, hx], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (CL, XY, EX7, XY))
    c4 = _cl.Closure(w, A0, {})
    for E_, s_ in [('E', er), (X7, st([x7p], 'rpred', '%s e. RR' % X7)), (Xm7, st([xm7p], 'rpred', '%s e. RR' % Xm7)), (Y11, y11r), ('N', nr), (L2, l2r), (Y39, y39r), ('Y', yr), (WS(HALF, X3), None)]:
        if s_ is not None:
            c4.leaf(E_, 'RR', s_)
    p3 = lin.lineq(w, A0, '( %s x. %s )' % (EX7, XY), '( ( E x. %s ) x. ( %s x. %s ) )' % (Y11, X7, Xm7), closure=c4, products=True)
    ng = st([st([b['xp'], ], 'x', 'x') if False else st([b['xp']], 'rpcnd', 'X e. CC'), st([b['xp']], 'rpne0d', 'X =/= 0'), st([lr_(F7900)], 'recnd', '%s e. CC' % F7900)], 'cxpnegd', '%s = ( 1 / %s )' % (Xm7, X7))
    p4 = st([st([ng], 'oveq2d', '( %s x. %s ) = ( %s x. ( 1 / %s ) )' % (X7, Xm7, X7, X7)), st([st([x7p], 'rpcnd', '%s e. CC' % X7), st([x7p], 'rpne0d', '%s =/= 0' % X7)], 'recidd', '( %s x. ( 1 / %s ) ) = 1' % (X7, X7))], 'eqtrd', '( %s x. %s ) = 1' % (X7, Xm7))
    p5 = st([st([p4], 'oveq2d', '( ( E x. %s ) x. ( %s x. %s ) ) = ( ( E x. %s ) x. 1 )' % (Y11, X7, Xm7, Y11)), st([st([st([er, y11r], 'remulcld', '( E x. %s ) e. RR' % Y11)], 'recnd', '( E x. %s ) e. CC' % Y11)], 'mulridd', '( ( E x. %s ) x. 1 ) = ( E x. %s )' % (Y11, Y11))], 'eqtrd',
            '( ( E x. %s ) x. ( %s x. %s ) ) = ( E x. %s )' % (Y11, X7, Xm7, Y11))
    c4.atom('( E x. %s )' % Y11) if False else None
    k27 = lin.linarith(w, A0, [p1, p2, p3, p5], '( %s x. ( N x. %s ) ) <_ ( ( E x. %s ) / ; 2 7 )' % (C16, L2, Y11), closure=c4, products=True)
    # step 5
    wsr = ws_real(w, A0, nn, hr, h0, h1, b['x3r'], HALF, X3)
    k1r = st([lr_(C16), st([nr, l2r], 'remulcld', '( N x. %s ) e. RR' % L2)], 'remulcld', '( %s x. ( N x. %s ) ) e. RR' % (C16, L2))
    eyr = st([st([er, y11r], 'remulcld', '( E x. %s ) e. RR' % Y11), st([num.rp(w, '; 2 7')], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '( ( E x. %s ) / ; 2 7 ) e. RR' % Y11)
    q1 = st([wsr, k1r, y39r, y390, wsI], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s x. ( N x. %s ) ) )' % (Y39, WS(HALF, X3), Y39, C16, L2))
    q2 = st([k1r, eyr, y39r, y390, k27], 'lemul2ad', '( %s x. ( %s x. ( N x. %s ) ) ) <_ ( %s x. ( ( E x. %s ) / ; 2 7 ) )' % (Y39, C16, L2, Y39, Y11))
    yy = st([st([yp], 'rpcnd', 'Y e. CC'), st([yp], 'rpne0d', 'Y =/= 0'), st([f39], 'recnd', '%s e. CC' % F3950), st([lr_(F11)], 'recnd', '%s e. CC' % F11)], 'cxpaddd', '( Y ^c ( %s + %s ) ) = ( %s x. %s )' % (F3950, F11, Y39, Y11))
    sm = lin.lineq(w, A0, '( %s + %s )' % (F3950, F11), '1', leaves={})
    yy2 = st([st([st([sm], 'oveq2d', '( Y ^c ( %s + %s ) ) = ( Y ^c 1 )' % (F3950, F11)), st([st([yp], 'rpcnd', 'Y e. CC')], 'cxp1d', '( Y ^c 1 ) = Y')], 'eqtrd', '( Y ^c ( %s + %s ) ) = Y' % (F3950, F11)), yy], 'eqtr3d', '( %s x. %s ) = Y' % (Y39, Y11))
    YY = '( %s x. %s )' % (Y39, Y11)
    c4.leaf(YY, 'RR', st([y39r, y11r], 'remulcld', '%s e. RR' % YY)) if False else None
    q3 = lin.lineq(w, A0, '( %s x. ( ( E x. %s ) / ; 2 7 ) )' % (Y39, Y11), '( ( E x. %s ) / ; 2 7 )' % YY, closure=c4, products=True)
    q4 = st([q3, st([st([yy2], 'oveq2d', '( E x. %s ) = ( E x. Y )' % YY)], 'oveq1d', '( ( E x. %s ) / ; 2 7 ) = ( ( E x. Y ) / ; 2 7 )' % YY)], 'eqtrd', '( %s x. ( ( E x. %s ) / ; 2 7 ) ) = ( ( E x. Y ) / ; 2 7 )' % (Y39, Y11))
    c5 = _cl.Closure(w, A0, {})
    zsr = st([DBfin, izr], 'fsumrecl', '%s e. RR' % ZS(X3, 'Y', HALF, F3950))
    for E_, s_ in [(ZS(X3, 'Y', HALF, F3950), zsr), ('( %s x. %s )' % (Y39, WS(HALF, X3)), st([y39r, wsr], 'remulcld', '( %s x. %s ) e. RR' % (Y39, WS(HALF, X3)))),
                   ('( %s x. ( %s x. ( N x. %s ) ) )' % (Y39, C16, L2), st([y39r, k1r], 'remulcld', '( %s x. ( %s x. ( N x. %s ) ) ) e. RR' % (Y39, C16, L2))),
                   ('( %s x. ( ( E x. %s ) / ; 2 7 ) )' % (Y39, Y11), st([y39r, eyr], 'remulcld', '( %s x. ( ( E x. %s ) / ; 2 7 ) ) e. RR' % (Y39, Y11))), ('( E x. Y )', st([er, yr], 'remulcld', '( E x. Y ) e. RR'))]:
        c5.leaf(E_, 'RR', s_)
    fin = lin.linarith(w, A0, [zs1, q1, q2, q4], '%s <_ ( ( E x. Y ) / ; 2 7 )' % ZS(X3, 'Y', HALF, F3950), closure=c5)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21z1']))
    return run(w)


if __name__ == '__main__':
    only = sys.argv[1:]
    for lab, f in [('t21wsi', gen_wsI), ('t21z1', gen_z1)]:
        if not only or lab in only:
            f()
