"""Sortie LD1, section 1 (ld1bvatau ld1tau1 ld1cpow) and the Taylor remainder ld1tayrem.
Run: MM_DB=sorties/ld1.mm MM_ENGINE=mmatch python3 tools/gen/ld1_b.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ld1lib import *
import lin as _L
_L.MAXPOW = 8

only = sys.argv[1:]
want = lambda l: not only or l in only


def fin(w):
    qedlast(w)
    return go(w)


def ld1bvatau():
    w = W('ld1bvatau', 'Lean ` abs_bvA_le_card_divisors ` : ` abs a ( n ) <_ tau ( n ) ` from ` abs lambda <_ 1 ` (~ bvaval , ~ fsumabs , ~ z5lamabs , ~ fsumconst ).')
    A = '( %s /\\ N e. NN )' % HAB0; P = parts(w, A)
    ar, br, nn, hab = P['A e. RR'], P['B e. RR'], P['N e. NN'], P[HAB0]
    LAM = lambda d: '( ( A bvLam B ) ` %s )' % d
    DVN = DV('N')
    av = dst(w, A, [ar], 'elexd', 'A e. _V'); bv = dst(w, A, [br], 'elexd', 'B e. _V')
    bval = ap(w, A, 'bvaval', [J(w, A, av, bv), nn], '( ( A bvA B ) ` N ) = sum_ d e. %s %s' % (DVN, LAM('d')))
    fi = ap(w, A, 'dvdsfi', [nn], '%s e. Fin' % DVN)
    Ad = '( %s /\\ d e. %s )' % (A, DVN)
    dn = ap(w, Ad, 'elrabi', [w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, DVN))], 'd e. NN')
    lb = ap(w, Ad, 'z5lamabs', [J(w, Ad, lift(w, hab, Ad), dn)], '( abs ` %s ) <_ 1' % LAM('d'))
    lr = ap(w, Ad, 'bvlamre', [J(w, Ad, J(w, Ad, dst(w, Ad, [lift(w, ar, Ad), lift(w, P['0 < A'], Ad)], 'elrpd', 'A e. RR+'),
                                              dst(w, Ad, [lift(w, br, Ad), dst(w, Ad, [w.s([], '0red', '( %s -> 0 e. RR )' % Ad), lift(w, ar, Ad), lift(w, br, Ad), lift(w, P['0 < A'], Ad), lift(w, P['A < B'], Ad)], 'lttrd', '0 < B')], 'elrpd', 'B e. RR+'),
                                              lift(w, P['A < B'], Ad)), dn)], '%s e. RR' % LAM('d'))
    lc = dst(w, Ad, [lr], 'recnd', '%s e. CC' % LAM('d'))
    ab = dst(w, A, [fi, lc], 'fsumabs', '( abs ` sum_ d e. %s %s ) <_ sum_ d e. %s ( abs ` %s )' % (DVN, LAM('d'), DVN, LAM('d')))
    le = dst(w, A, [fi, dst(w, Ad, [lc], 'abscld', '( abs ` %s ) e. RR' % LAM('d')), w.s([], '1red', '( %s -> 1 e. RR )' % Ad), lb], 'fsumle',
             'sum_ d e. %s ( abs ` %s ) <_ sum_ d e. %s 1' % (DVN, LAM('d'), DVN))
    fc = ap(w, A, 'fsumconst', [fi, w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'sum_ d e. %s 1 = ( %s x. 1 )' % (DVN, TAU('N')))
    tc = dst(w, A, [dst(w, A, [ap(w, A, 'hashcl', [fi], '%s e. NN0' % TAU('N'))], 'nn0red', '%s e. RR' % TAU('N'))], 'recnd', '%s e. CC' % TAU('N'))
    m1 = dst(w, A, [tc], 'mulridd', '( %s x. 1 ) = %s' % (TAU('N'), TAU('N')))
    s1 = dst(w, A, [ab, dst(w, A, [le, eqt(w, A, fc, m1)], 'breqtrd', 'sum_ d e. %s ( abs ` %s ) <_ %s' % (DVN, LAM('d'), TAU('N')))], 'letrd' if False else 'x', 'x') if False else None
    absr = dst(w, A, [dst(w, A, [fi, lc], 'fsumcl', 'sum_ d e. %s %s e. CC' % (DVN, LAM('d')))], 'abscld', '( abs ` sum_ d e. %s %s ) e. RR' % (DVN, LAM('d')))
    sumr = dst(w, A, [fi, dst(w, Ad, [lc], 'abscld', '( abs ` %s ) e. RR' % LAM('d'))], 'fsumrecl', 'sum_ d e. %s ( abs ` %s ) e. RR' % (DVN, LAM('d')))
    tr = dst(w, A, [dst(w, A, [ap(w, A, 'hashcl', [fi], '%s e. NN0' % TAU('N'))], 'nn0red', '%s e. RR' % TAU('N'))], 'x', 'x') if False else dst(w, A, [ap(w, A, 'hashcl', [fi], '%s e. NN0' % TAU('N'))], 'nn0red', '%s e. RR' % TAU('N'))
    s2 = dst(w, A, [le, eqt(w, A, fc, m1)], 'breqtrd', 'sum_ d e. %s ( abs ` %s ) <_ %s' % (DVN, LAM('d'), TAU('N')))
    s3 = dst(w, A, [absr, sumr, tr, ab, s2], 'letrd', '( abs ` sum_ d e. %s %s ) <_ %s' % (DVN, LAM('d'), TAU('N')))
    dst(w, A, [dst(w, A, [bval], 'fveq2d', '( abs ` ( ( A bvA B ) ` N ) ) = ( abs ` sum_ d e. %s %s )' % (DVN, LAM('d'))), s3], 'eqbrtrd',
        '( abs ` ( ( A bvA B ) ` N ) ) <_ %s' % TAU('N'))
    return fin(w)


def ld1tau1():
    w = W('ld1tau1', 'Lean ` sum_card_divisors_eq ` and ` sum_card_divisors_le ` : ` sum_ ( n <_ x ) tau ( n ) = sum_ ( d <_ x ) |_ x / d <_ x ( 1 + log x ) ` (~ dvdsflsumcom , ~ harmonicubnd ).')
    A = '( X e. RR /\\ 1 <_ X )'; P = parts(w, A); xr, x1 = P['X e. RR'], P['1 <_ X']
    c = Closure(w, A, {'X': [('RR', xr), ('ge1', x1)]})
    FX = '( |_ ` X )'; R = '( 1 ... %s )' % FX
    An = '( %s /\\ n e. %s )' % (A, R)
    nn = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, R))], 'n e. NN')
    fi = ap(w, An, 'dvdsfi', [nn], '%s e. Fin' % DV('n'))
    fc = ap(w, An, 'fsumconst', [fi, w.s([], '1cnd', '( %s -> 1 e. CC )' % An)], 'sum_ d e. %s 1 = ( %s x. 1 )' % (DV('n'), TAU('n')))
    tc = dst(w, An, [dst(w, An, [ap(w, An, 'hashcl', [fi], '%s e. NN0' % TAU('n'))], 'nn0cnd', '%s e. CC' % TAU('n'))], 'mulridd', '( %s x. 1 ) = %s' % (TAU('n'), TAU('n')))
    e1 = eqc(w, An, eqt(w, An, fc, tc))
    s1 = dst(w, A, [e1], 'sumeq2dv', 'sum_ n e. %s %s = sum_ n e. %s sum_ d e. %s 1' % (R, TAU('n'), R, DV('n')))
    RD = lambda d: '( 1 ... ( |_ ` ( X / %s ) ) )' % d
    h1 = w.s([], 'eqidd', '( n = ( d x. m ) -> 1 = 1 )')
    And = '( %s /\\ ( n e. %s /\\ d e. %s ) )' % (A, R, DV('n'))
    h3 = w.s([], '1cnd', '( %s -> 1 e. CC )' % And)
    s2 = w.s([h1, xr, h3], 'dvdsflsumcom', '( %s -> sum_ n e. %s sum_ d e. %s 1 = sum_ d e. %s sum_ m e. %s 1 )' % (A, R, DV('n'), R, RD('d')))
    Ad = '( %s /\\ d e. %s )' % (A, R)
    dn = ap(w, Ad, 'elfznn', [w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, R))], 'd e. NN')
    cd = Closure(w, Ad, {'X': [('RR', lift(w, xr, Ad)), ('ge1', lift(w, x1, Ad))], 'd': ('NN', dn)})
    XD = '( X / d )'; FXD = '( |_ ` %s )' % XD
    cd.leaf('X', 'ge0', linarith(w, Ad, [lift(w, x1, Ad)], '0 <_ X', closure=cd))
    xd0 = cd.ge0(XD)
    fl0 = ap(w, Ad, 'flge0nn0', [J(w, Ad, cd.mem(XD, 'RR'), xd0)], '%s e. NN0' % FXD)
    fc2 = ap(w, Ad, 'fsumconst', [dst(w, Ad, [], 'fzfid', '%s e. Fin' % RD('d')), w.s([], '1cnd', '( %s -> 1 e. CC )' % Ad)],
             'sum_ m e. %s 1 = ( ( # ` %s ) x. 1 )' % (RD('d'), RD('d')))
    hf = ap(w, Ad, 'hashfz1', [fl0], '( # ` %s ) = %s' % (RD('d'), FXD))
    e2 = eqt(w, Ad, fc2, eqt(w, Ad, dst(w, Ad, [hf], 'oveq1d', '( ( # ` %s ) x. 1 ) = ( %s x. 1 )' % (RD('d'), FXD)),
                              dst(w, Ad, [dst(w, Ad, [fl0], 'nn0cnd', '%s e. CC' % FXD)], 'mulridd', '( %s x. 1 ) = %s' % (FXD, FXD))))
    s3 = dst(w, A, [e2], 'sumeq2dv', 'sum_ d e. %s sum_ m e. %s 1 = sum_ d e. %s %s' % (R, RD('d'), R, FXD))
    fl = ap(w, Ad, 'flle', [cd.mem(XD, 'RR')], '%s <_ %s' % (FXD, XD))
    rf = dst(w, A, [], 'fzfid', '%s e. Fin' % R)
    s4 = dst(w, A, [rf, dst(w, Ad, [fl0], 'nn0red', '%s e. RR' % FXD), cd.mem(XD, 'RR'), fl], 'fsumle', 'sum_ d e. %s %s <_ sum_ d e. %s %s' % (R, FXD, R, XD))
    dr = ap(w, Ad, 'divrecd', [dst(w, Ad, [lift(w, xr, Ad)], 'recnd', 'X e. CC'), dst(w, Ad, [dn], 'nncnd', 'd e. CC'), dst(w, Ad, [dn], 'nnne0d', 'd =/= 0')], '%s = ( X x. ( 1 / d ) )' % XD)
    s5 = dst(w, A, [dr], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s ( X x. ( 1 / d ) )' % (R, XD, R))
    xc = dst(w, A, [xr], 'recnd', 'X e. CC')
    s6 = eqc(w, A, dst(w, A, [rf, xc, dst(w, Ad, [dst(w, Ad, [dn], 'nnrecred', '( 1 / d ) e. RR')], 'recnd', '( 1 / d ) e. CC')], 'fsummulc2',
                        '( X x. sum_ d e. %s ( 1 / d ) ) = sum_ d e. %s ( X x. ( 1 / d ) )' % (R, R)))
    hb = ap(w, A, 'harmonicubnd', [J(w, A, xr, x1)], 'sum_ d e. %s ( 1 / d ) <_ ( ( log ` X ) + 1 )' % R)
    x0 = linarith(w, A, [x1], '0 <_ X', closure=c); c.leaf('X', 'ge0', x0)
    c.leaf('X', 'RR+', dst(w, A, [xr, linarith(w, A, [x1], '0 < X', closure=c)], 'elrpd', 'X e. RR+'))
    c.leaf('sum_ d e. %s ( 1 / d )' % R, 'RR', dst(w, A, [rf, dst(w, Ad, [dn], 'nnrecred', '( 1 / d ) e. RR')], 'fsumrecl', 'sum_ d e. %s ( 1 / d ) e. RR' % R))
    s7 = lemul(w, A, c, hb, 'X')
    lr = c.mem('( log ` X )', 'RR')
    ac = dst(w, A, [dst(w, A, [lr], 'recnd', '( log ` X ) e. CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'addcomd', '( ( log ` X ) + 1 ) = ( 1 + ( log ` X ) )')
    s8 = dst(w, A, [s7, dst(w, A, [ac], 'oveq2d', '( X x. ( ( log ` X ) + 1 ) ) = ( X x. ( 1 + ( log ` X ) ) )')], 'breqtrd',
             '( X x. sum_ d e. %s ( 1 / d ) ) <_ ( X x. ( 1 + ( log ` X ) ) )' % R)
    eqA = eqt(w, A, eqt(w, A, s1, s2), s3)                                  # sum tau = sum floor
    right = dst(w, A, [s4, eqt(w, A, s5, s6)], 'breqtrd', 'sum_ d e. %s %s <_ ( X x. sum_ d e. %s ( 1 / d ) )' % (R, FXD, R))
    r1 = dst(w, A, [rf, dst(w, Ad, [fl0], 'nn0red', '%s e. RR' % FXD)], 'fsumrecl', 'sum_ d e. %s %s e. RR' % (R, FXD))
    r2 = c.mem('( X x. sum_ d e. %s ( 1 / d ) )' % R, 'RR') if False else dst(w, A, [xr, dst(w, A, [rf, dst(w, Ad, [dn], 'nnrecred', '( 1 / d ) e. RR')], 'fsumrecl', 'sum_ d e. %s ( 1 / d ) e. RR' % R)], 'remulcld', '( X x. sum_ d e. %s ( 1 / d ) ) e. RR' % R)
    r3 = c.mem('( X x. ( 1 + ( log ` X ) ) )', 'RR')
    bnd = dst(w, A, [r1, r2, r3, right, s8], 'letrd', 'sum_ d e. %s %s <_ ( X x. ( 1 + ( log ` X ) ) )' % (R, FXD))
    dst(w, A, [eqA, bnd], 'eqbrtrd', 'sum_ n e. %s %s <_ ( X x. ( 1 + ( log ` X ) ) )' % (R, TAU('n')))
    return fin(w)


def ld1cpow():
    w = W('ld1cpow', 'Lean ` natCast_cpow_neg_eq ` : ` n ^ -u s = n ^ -u Re s x. e ^ ( i ( -u log n Im s ) ) ` (~ cxpefd , ~ replimd , ~ efadd ).')
    A = '( N e. NN /\\ S e. CC )'; P = parts(w, A); nn, sc = P['N e. NN'], P['S e. CC']
    nc = dst(w, A, [nn], 'nncnd', 'N e. CC'); n0 = dst(w, A, [nn], 'nnne0d', 'N =/= 0')
    nrp = dst(w, A, [nn], 'nnrpd', 'N e. RR+')
    L = '( log ` N )'
    lr = dst(w, A, [nrp], 'relogcld', '%s e. RR' % L); lc = dst(w, A, [lr], 'recnd', '%s e. CC' % L)
    re = dst(w, A, [sc], 'recld', '( Re ` S ) e. RR'); im = dst(w, A, [sc], 'imcld', '( Im ` S ) e. RR')
    rec = dst(w, A, [re], 'recnd', '( Re ` S ) e. CC'); imc = dst(w, A, [im], 'recnd', '( Im ` S ) e. CC')
    c = Closure(w, A, {'( Re ` S )': ('RR', re), '( Im ` S )': ('RR', im), L: ('RR', lr), '_i': ('CC', a1(w, A, 'ax-icn', '_i e. CC')), 'S': ('CC', sc)})
    e1 = dst(w, A, [nc, n0, dst(w, A, [sc], 'negcld', '-u S e. CC')], 'cxpefd', '( N ^c -u S ) = ( exp ` ( -u S x. %s ) )' % L)
    e2 = dst(w, A, [nc, n0, dst(w, A, [rec], 'negcld', '-u ( Re ` S ) e. CC')], 'cxpefd', '( N ^c -u ( Re ` S ) ) = ( exp ` ( -u ( Re ` S ) x. %s ) )' % L)
    rl = dst(w, A, [sc], 'replimd', 'S = ( ( Re ` S ) + ( _i x. ( Im ` S ) ) )')
    SR = '( ( Re ` S ) + ( _i x. ( Im ` S ) ) )'
    T1 = '( -u ( Re ` S ) x. %s )' % L; T2 = '( _i x. ( -u %s x. ( Im ` S ) ) )' % L
    sub = dst(w, A, [dst(w, A, [rl], 'negeqd', '-u S = -u %s' % SR)], 'oveq1d', '( -u S x. %s ) = ( -u %s x. %s )' % (L, SR, L))
    rg = ringeq(w, A, '( -u %s x. %s )' % (SR, L), '( %s + %s )' % (T1, T2), c)
    ea = ap(w, A, 'efadd', [c.mem(T1, 'CC'), c.mem(T2, 'CC')], '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (T1, T2, T1, T2))
    ch = eqt(w, A, eqt(w, A, e1, dst(w, A, [eqt(w, A, sub, rg)], 'fveq2d', '( exp ` ( -u S x. %s ) ) = ( exp ` ( %s + %s ) )' % (L, T1, T2))), ea)
    dst(w, A, [ch, dst(w, A, [eqc(w, A, e2)], 'oveq1d', '( ( exp ` %s ) x. ( exp ` %s ) ) = ( ( N ^c -u ( Re ` S ) ) x. ( exp ` %s ) )' % (T1, T2, T2))], 'eqtrd',
        '( N ^c -u S ) = ( ( N ^c -u ( Re ` S ) ) x. %s )' % NEX('N', '( Im ` S )'))
    return fin(w)


def ld1tayrem():
    w = W('ld1tayrem', 'Lean ` taylor_remainder_le ` (Mathlib ` Real.exp_bound ` ): ` abs ( e ^ x - sum_ ( k <_ J ) x ^ k / k ! ) <_ ( 1 / 5 ) ^ ( J + 1 ) ` for ` abs x <_ 1 / 6 ` , ` 3 <_ J ` (~ eftlub , ~ isumsplit , ~ efval ).')
    A = '( ( X e. RR /\\ ( abs ` X ) <_ ( 1 / 6 ) ) /\\ ( J e. NN0 /\\ 3 <_ J ) )'; P = parts(w, A)
    xr, xa, jn, j3 = P['X e. RR'], P['( abs ` X ) <_ ( 1 / 6 )'], P['J e. NN0'], P['3 <_ J']
    xc = dst(w, A, [xr], 'recnd', 'X e. CC')
    M = '( J + 1 )'; mn = ap(w, A, 'nn0p1nn', [jn], '%s e. NN' % M)
    mn0 = dst(w, A, [mn], 'nnnn0d', '%s e. NN0' % M)
    BODY = lambda v: '( ( X ^ %s ) / ( ! ` %s ) )' % (v, v)
    FM = '( n e. NN0 |-> %s )' % BODY('n')
    AX = '( abs ` X )'
    GM = '( n e. NN0 |-> ( ( %s ^ n ) / ( ! ` n ) ) )' % AX
    HM = '( n e. NN0 |-> ( ( ( %s ^ %s ) / ( ! ` %s ) ) x. ( ( 1 / ( %s + 1 ) ) ^ n ) ) )' % (AX, M, M, M)
    c = Closure(w, A, {'X': ('RR', xr), 'J': ('NN0', jn), AX: ('RR', dst(w, A, [xc], 'abscld', '%s e. RR' % AX))})
    xa1 = linarith(w, A, [xa], '%s <_ 1' % AX, closure=c)
    hf = w.s([], 'eqid', '%s = %s' % (FM, FM)); hg = w.s([], 'eqid', '%s = %s' % (GM, GM)); hh = w.s([], 'eqid', '%s = %s' % (HM, HM))
    Q = '( ( %s + 1 ) / ( ( ! ` %s ) x. %s ) )' % (M, M, M)
    W_ = '( ZZ>= ` %s )' % M
    tl = w.s([hf, hg, hh, mn, xc, xa1], 'eftlub', '( %s -> ( abs ` sum_ k e. %s ( %s ` k ) ) <_ ( ( %s ^ %s ) x. %s ) )' % (A, W_, FM, AX, M, Q))
    # exp X = sum_ k e. NN0 body = sum_{0..J} + sum_{k >= J+1}
    ev = ap(w, A, 'efval', [xc], '( exp ` X ) = sum_ k e. NN0 %s' % BODY('k'))
    Ak = '( %s /\\ k e. NN0 )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN0 )' % Ak)
    ck = Closure(w, Ak, {'X': ('RR', lift(w, xr, Ak)), 'k': ('NN0', kn)})
    ck.leaf('( ! ` k )', 'NN', dst(w, Ak, [kn], 'faccld', '( ! ` k ) e. NN'))
    bk = ck.mem(BODY('k'), 'CC')
    fv = fvmd(w, Ak, 'n', 'NN0', BODY('n'), 'k', kn, bk)
    z0 = w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )'); zw = w.s([], 'eqid', '%s = %s' % (W_, W_))
    m0 = dst(w, A, [mn0, w.s([z0], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % A)], 'eleqtrd', '%s e. ( ZZ>= ` 0 )' % M) if False else dst(w, A, [mn0], 'nn0zd', '%s e. ZZ' % M)
    m0 = dst(w, A, [mn0, w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '%s e. ( ZZ>= ` 0 )' % M)
    cvg = w.s([hf], 'efcvg', '( X e. CC -> seq 0 ( + , %s ) ~~> ( exp ` X ) )' % FM)
    dm = dst(w, A, [dst(w, A, [xc, cvg], 'syl', 'seq 0 ( + , %s ) ~~> ( exp ` X )' % FM)], 'climdm' if False else 'x', 'x') if False else None
    cv2 = w.s([hf], 'eftlcvg', '( ( X e. CC /\\ 0 e. NN0 ) -> seq 0 ( + , %s ) e. dom ~~> )' % FM)
    dm = dst(w, A, [J(w, A, xc, a1(w, A, '0nn0', '0 e. NN0')), cv2], 'syl', 'seq 0 ( + , %s ) e. dom ~~>' % FM)
    m0z = dst(w, A, [mn0, w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '%s e. ( ZZ>= ` 0 )' % M)
    sp = w.s([z0, zw, mn0, fv, bk, dm], 'isumsplit', '( %s -> sum_ k e. NN0 %s = ( sum_ k e. ( 0 ... ( %s - 1 ) ) %s + sum_ k e. %s %s ) )' % (A, BODY('k'), M, BODY('k'), W_, BODY('k')))
    pc = dst(w, A, [dst(w, A, [jn], 'nn0cnd', 'J e. CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'pncand', '( %s - 1 ) = J' % M)
    SJ = 'sum_ k e. ( 0 ... J ) %s' % BODY('k'); TL = 'sum_ k e. %s %s' % (W_, BODY('k'))
    sp2 = eqt(w, A, eqt(w, A, ev, sp), dst(w, A, [dst(w, A, [dst(w, A, [pc], 'oveq2d', '( 0 ... ( %s - 1 ) ) = ( 0 ... J )' % M)], 'sumeq1d',
                                                          'sum_ k e. ( 0 ... ( %s - 1 ) ) %s = %s' % (M, BODY('k'), SJ))], 'oveq1d',
                                                 '( sum_ k e. ( 0 ... ( %s - 1 ) ) %s + %s ) = ( %s + %s )' % (M, BODY('k'), TL, SJ, TL)))
    # the tail of eftlub is TL
    Aw = '( %s /\\ k e. %s )' % (A, W_)
    kw = w.s([], 'simpr', '( %s -> k e. %s )' % (Aw, W_))
    kn2 = dst(w, Aw, [dst(w, Aw, [kw, lift(w, mn0, Aw)], 'x', 'x') if False else kw], 'eluznn0' if False else 'x', 'x') if False else None
    kn2 = ap(w, Aw, 'eluznn0', [lift(w, mn0, Aw), kw], 'k e. NN0')
    cw = Closure(w, Aw, {'X': ('RR', lift(w, xr, Aw)), 'k': ('NN0', kn2)})
    cw.leaf('( ! ` k )', 'NN', dst(w, Aw, [kn2], 'faccld', '( ! ` k ) e. NN'))
    fvw = fvmd(w, Aw, 'n', 'NN0', BODY('n'), 'k', kn2, cw.mem(BODY('k'), 'CC'))
    tle = dst(w, A, [fvw], 'sumeq2dv', 'sum_ k e. %s ( %s ` k ) = %s' % (W_, FM, TL))
    tl2 = dst(w, A, [dst(w, A, [tle], 'fveq2d', '( abs ` sum_ k e. %s ( %s ` k ) ) = ( abs ` %s )' % (W_, FM, TL)), tl], 'eqbrtrrd', '( abs ` %s ) <_ ( ( %s ^ %s ) x. %s )' % (TL, AX, M, Q))
    # exp X - SJ = TL
    sjc = c.mem(SJ, 'CC') if False else dst(w, A, [dst(w, A, [], 'fzfid', '( 0 ... J ) e. Fin'), lift(w, bk, '( %s /\\ k e. ( 0 ... J ) )' % A) if False else None], 'x', 'x') if False else None
    Aj = '( %s /\\ k e. ( 0 ... J ) )' % A
    kj = ap(w, Aj, 'elfznn0', [w.s([], 'simpr', '( %s -> k e. ( 0 ... J ) )' % Aj)], 'k e. NN0')
    cj = Closure(w, Aj, {'X': ('RR', lift(w, xr, Aj)), 'k': ('NN0', kj)})
    cj.leaf('( ! ` k )', 'NN', dst(w, Aj, [kj], 'faccld', '( ! ` k ) e. NN'))
    sjc = dst(w, A, [dst(w, A, [], 'fzfid', '( 0 ... J ) e. Fin'), cj.mem(BODY('k'), 'CC')], 'fsumcl', '%s e. CC' % SJ)
    tlc = dst(w, A, [dst(w, A, [xc], 'efcld', '( exp ` X ) e. CC'), sjc], 'subcld', '( ( exp ` X ) - %s ) e. CC' % SJ) if False else None
    tlc = w.s([z0 if False else zw, lift(w, mn0, A) if False else dst(w, A, [mn0], 'nn0zd', '%s e. ZZ' % M), fvw, cw.mem(BODY('k'), 'CC'),
               dst(w, A, [J(w, A, xc, mn0), w.s([hf], 'eftlcvg', '( ( X e. CC /\\ %s e. NN0 ) -> seq %s ( + , %s ) e. dom ~~> )' % (M, M, FM))], 'syl', 'seq %s ( + , %s ) e. dom ~~>' % (M, FM))],
              'isumcl', '( %s -> %s e. CC )' % (A, TL))
    df = eqt(w, A, dst(w, A, [sp2], 'oveq1d', '( ( exp ` X ) - %s ) = ( ( %s + %s ) - %s )' % (SJ, SJ, TL, SJ)), dst(w, A, [sjc, tlc], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (SJ, TL, SJ, TL)))
    # the numeric bound: ( AX ^ M ) Q <_ ( 1 / 6 ) ^ M x. 2 <_ ( 1 / 5 ) ^ M
    P6 = '( ( 1 / 6 ) ^ %s )' % M; PX = '( %s ^ %s )' % (AX, M); P5 = '( ( 1 / 5 ) ^ %s )' % M; P65 = '( ( 6 / 5 ) ^ %s )' % M
    ax0 = dst(w, A, [xc], 'absge0d', '0 <_ %s' % AX)
    r16 = c.mem('( 1 / 6 )', 'RR')
    px6 = ap(w, A, 'leexp1a', [J(w, A, c.mem(AX, 'RR'), r16, mn0), J(w, A, ax0, xa)], '%s <_ %s' % (PX, P6))
    FM_ = '( ! ` %s )' % M
    fr = dst(w, A, [dst(w, A, [mn0], 'faccld', '%s e. NN' % FM_)], 'nnred', '%s e. RR' % FM_)
    f1 = dst(w, A, [dst(w, A, [mn0], 'faccld', '%s e. NN' % FM_)], 'nnge1d', '1 <_ %s' % FM_)
    mr = dst(w, A, [mn], 'nnred', '%s e. RR' % M); m1 = dst(w, A, [mn], 'nnge1d', '1 <_ %s' % M)
    c.leaf(FM_, 'NN', dst(w, A, [mn0], 'faccld', '%s e. NN' % FM_)); c.leaf(FM_, 'ge1', f1)
    DEN = '( %s x. %s )' % (FM_, M)
    den0 = c.gt0(DEN)
    # Q <_ 2  <=>  M + 1 <_ 2 DEN
    q2a = nlinarith(w, A, [f1, m1], '( %s + 1 ) <_ ( 2 x. %s )' % (M, DEN), closure=c)
    ldm = ap(w, A, 'ledivmul', [J(w, A, c.mem('( %s + 1 )' % M, 'RR'), c.mem('2', 'RR'), J(w, A, c.mem(DEN, 'RR'), den0))],
             '( %s <_ 2 <-> ( %s + 1 ) <_ ( %s x. 2 ) )' % (Q, M, DEN)) if False else None
    ldm = ap(w, A, 'ledivmul', [c.mem('( %s + 1 )' % M, 'RR'), c.mem('2', 'RR'), J(w, A, c.mem(DEN, 'RR'), den0)],
             '( %s <_ 2 <-> ( %s + 1 ) <_ ( %s x. 2 ) )' % (Q, M, DEN))
    q2b = dst(w, A, [q2a, dst(w, A, [c.mem(DEN, 'CC'), a1(w, A, '2cn', '2 e. CC')], 'mulcomd', '( %s x. 2 ) = ( 2 x. %s )' % (DEN, DEN))], 'breqtrrd', '( %s + 1 ) <_ ( %s x. 2 )' % (M, DEN))
    q2 = dst(w, A, [q2b, ldm], 'mpbird', '%s <_ 2' % Q)
    q0 = c.ge0(Q)
    m12 = dst(w, A, [c.mem(PX, 'RR'), c.mem(P6, 'RR'), c.mem(Q, 'RR'), c.mem('2', 'RR'), c.ge0(PX), q0, px6, q2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. 2 )' % (PX, Q, P6))
    # 2 <_ P65, P5 = P65 P6
    p4 = ringeqp(w, A, '( ( 6 / 5 ) ^ 4 )', '( ; ; ; 1 2 9 6 / ; ; 6 2 5 )', c)
    l2 = w.s([num.le_lit(w, '2', '( ; ; ; 1 2 9 6 / ; ; 6 2 5 )')], 'a1i', '( %s -> 2 <_ ( ; ; ; 1 2 9 6 / ; ; 6 2 5 ) )' % A)
    m4 = linarith(w, A, [j3], '4 <_ %s' % M, closure=c)
    mz = dst(w, A, [mn], 'nnzd', '%s e. ZZ' % M)
    uz = dst(w, A, [J(w, A, a1(w, A, '4z', '4 e. ZZ'), mz, m4), a1(w, A, 'eluz2', '( %s e. ( ZZ>= ` 4 ) <-> ( 4 e. ZZ /\\ %s e. ZZ /\\ 4 <_ %s ) )' % (M, M, M))], 'mpbird', '%s e. ( ZZ>= ` 4 )' % M)
    r65 = c.mem('( 6 / 5 )', 'RR'); ge65 = w.s([num.le_lit(w, '1', '( 6 / 5 )')], 'a1i', '( %s -> 1 <_ ( 6 / 5 ) )' % A)
    lx = ap(w, A, 'leexp2a', [r65, ge65, uz], '( ( 6 / 5 ) ^ 4 ) <_ %s' % P65)
    two = dst(w, A, [c.mem('2', 'RR'), c.mem('( ; ; ; 1 2 9 6 / ; ; 6 2 5 )', 'RR'), c.mem(P65, 'RR'), l2, dst(w, A, [p4, lx], 'eqbrtrrd', '( ; ; ; 1 2 9 6 / ; ; 6 2 5 ) <_ %s' % P65)], 'letrd', '2 <_ %s' % P65)
    mp = ap(w, A, 'mulexp', [c.mem('( 6 / 5 )', 'CC'), c.mem('( 1 / 6 )', 'CC'), mn0], '( ( ( 6 / 5 ) x. ( 1 / 6 ) ) ^ %s ) = ( %s x. %s )' % (M, P65, P6))
    ml = w.s([num.mul_lits(w, '( 6 / 5 )', '( 1 / 6 )')], 'a1i', '( %s -> ( ( 6 / 5 ) x. ( 1 / 6 ) ) = ( 1 / 5 ) )' % A)
    p5 = eqt(w, A, eqc(w, A, dst(w, A, [ml], 'oveq1d', '( ( ( 6 / 5 ) x. ( 1 / 6 ) ) ^ %s ) = %s' % (M, P5))), mp)   # P5 = P65 P6
    l65 = lemul(w, A, c, two, P6, side=1)
    l65b = dst(w, A, [dst(w, A, [c.mem(P6, 'CC'), a1(w, A, '2cn', '2 e. CC')], 'mulcomd', '( %s x. 2 ) = ( 2 x. %s )' % (P6, P6)), dst(w, A, [l65, eqc(w, A, p5)], 'breqtrd', '( 2 x. %s ) <_ %s' % (P6, P5))], 'eqbrtrd', '( %s x. 2 ) <_ %s' % (P6, P5))
    fin_ = dst(w, A, [c.mem('( %s x. %s )' % (PX, Q), 'RR'), c.mem('( %s x. 2 )' % P6, 'RR'), c.mem(P5, 'RR'), m12, l65b], 'letrd', '( %s x. %s ) <_ %s' % (PX, Q, P5))
    last = dst(w, A, [dst(w, A, [tlc], 'abscld', '( abs ` %s ) e. RR' % TL), c.mem('( %s x. %s )' % (PX, Q), 'RR'), c.mem(P5, 'RR'), tl2, fin_], 'letrd', '( abs ` %s ) <_ %s' % (TL, P5))
    dst(w, A, [dst(w, A, [df], 'fveq2d', '( abs ` ( ( exp ` X ) - %s ) ) = ( abs ` %s )' % (SJ, TL)), last], 'eqbrtrd', '( abs ` ( ( exp ` X ) - %s ) ) <_ %s' % (SJ, P5))
    return fin(w)


if __name__ == '__main__':
    for lab in ['ld1bvatau', 'ld1tau1', 'ld1cpow', 'ld1tayrem']:
        if want(lab):
            if not globals()[lab]():
                sys.exit(1)
