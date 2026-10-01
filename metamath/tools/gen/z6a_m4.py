"""Z6a (block D): the residue step (z6mgyvc, z6mrfp, z6mrdg, z6malg, z6malg2, z6mfp, z6mfu, z6mrect)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_mlib import *
from tm import sub

only = sys.argv[1:]
H = '( 1 / 2 )'
AL = '( -u K - ( 1 / 2 ) )'
BR = '( ( 1 / 2 ) - K )'


def want(lab):
    return not only or lab in only


def cbvral(w, body, x, y, X):
    """closed: ( A. x e. X body <-> A. y e. X body[y/x] ); returns (step, new body)"""
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, y, x, y))
    sb, nb = w.wcongr(body, {x: y}, '%s = %s' % (x, y), {x: idk})
    return w.s([sb], 'cbvralvw', '( A. %s e. %s %s <-> A. %s e. %s %s )' % (x, X, body, y, X, nb)), nb


# ---------------------------------------------------------------- z6mgyvc
def z6mgyvc():
    w = W('z6mgyvc', 'The vertical line integrals of the Mellin integrand converge, with the tail bound: ~ z6vlcvg for ` G = ` the Mellin '
          'integrand, its line majorant written on ` _G ( w ) Y ^ -u w ` ( ~ z6gyhol ).')
    A = split_imp(STATEMENTS['z6mgyvc'])[0]
    s = mkst(w, A)
    Zv = lambda v: '( C + ( _i x. %s ) )' % v
    LINE = lambda v: '%s e. %s' % (Zv(v), DG)
    BVv = lambda v: '( R <_ ( abs ` %s ) -> ( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ ( M x. %s ) )' % (v, Zv(v), Zv(v), E4('( abs ` %s )' % v))
    yrp = w.s([], 'simplll', '( %s -> Y e. RR+ )' % A)
    cr = w.s([], 'simpllr', '( %s -> C e. RR )' % A)
    alv = w.s([], 'simplr', '( %s -> A. v e. RR %s )' % (A, LINE('v')))
    mr = w.s([], 'simprll', '( %s -> M e. RR )' % A)
    rrp = w.s([], 'simprlr', '( %s -> R e. RR+ )' % A)
    alb = w.s([], 'simprr', '( %s -> A. v e. RR %s )' % (A, BVv('v')))
    gyc = s([s([yrp, w.inst('z6gyhol')], 'syl', HOLG(GYM, DG))], 'simpld', '%s e. ( %s -cn-> CC )' % (GYM, DG))
    c1_, _ = cbvral(w, LINE('v'), 'v', 'u', 'RR')
    alu = s([alv, a1(w, A, c1_, '( A. v e. RR %s <-> A. u e. RR %s )' % (LINE('v'), LINE('u')))], 'mpbid', 'A. u e. RR %s' % LINE('u'))
    c2_, _ = cbvral(w, BVv('v'), 'v', 'u', 'RR')
    albu = s([alb, a1(w, A, c2_, '( A. v e. RR %s <-> A. u e. RR %s )' % (BVv('v'), BVv('u')))], 'mpbid', 'A. u e. RR %s' % BVv('u'))
    Au = '( %s /\\ u e. RR )' % A
    t = mkst(w, Au)
    Z = Zv('u')
    zdg = w.s([alu], 'r19.21bi', '( %s -> %s )' % (Au, LINE('u')))
    bu = w.s([albu], 'r19.21bi', '( %s -> %s )' % (Au, BVv('u')))
    val, V = mpval(w, Au, 'w', DG, '( ( _G ` w ) x. ( Y ^c -u w ) )', Z, zdg)
    EM = '( M x. %s )' % E4('( abs ` u )')
    ab = t([val], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (GYM, Z, V))
    bi = t([ab], 'breq1d', '( ( abs ` ( %s ` %s ) ) <_ %s <-> ( abs ` %s ) <_ %s )' % (GYM, Z, EM, V, EM))
    bi2 = t([bi], 'imbi2d', '( ( R <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ %s ) <-> %s )' % (GYM, Z, EM, BVv('u')))
    bg = t([bu, bi2], 'mpbird', '( R <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ %s )' % (GYM, Z, EM))
    ral = s([bg], 'ralrimiva', 'A. u e. RR ( R <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ %s )' % (GYM, Z, EM))
    HV = sub(split_imp(STATEMENTS['z6vlcvg'])[0], {'G': GYM, 'D': DG, 'Y': 'R'})
    h = s([s([cr, s([gyc, alu], 'jca', '( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s )' % (GYM, DG, LINE('u')))], 'jca',
             '( C e. RR /\\ ( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s ) )' % (GYM, DG, LINE('u'))),
           s([s([mr, rrp], 'jca', '( M e. RR /\\ R e. RR+ )'), ral], 'jca', '( ( M e. RR /\\ R e. RR+ ) /\\ A. u e. RR ( R <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ %s ) )' % (GYM, Z, EM))],
          'jca', HV)
    w.qed([h, w.inst('z6vlcvg')], 'syl', STATEMENTS['z6mgyvc'])
    return w


# ---------------------------------------------------------------- z6mrfp
def z6mrfp():
    w = W('z6mrfp', 'The rising factorial is the product of ~ z6gamfe ( ~ risefacval , ~ fzoval ).')
    A = '( Z e. CC /\\ K e. NN0 )'
    s = mkst(w, A)
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A); kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A)
    FZ = '( 0 ... ( K - 1 ) )'
    rv = s([zc, kn, w.inst('risefacval')], 'syl2anc', '( Z RiseFac K ) = prod_ k e. %s ( Z + k )' % FZ)
    fz = s([s([kn], 'nn0zd', 'K e. ZZ'), w.inst('fzoval')], 'syl', '( 0 ..^ K ) = %s' % FZ)
    pe = s([fz], 'prodeq1d', 'prod_ j e. ( 0 ..^ K ) ( Z + j ) = prod_ j e. %s ( Z + j )' % FZ)
    cb = w.s([w.s([], 'oveq2', '( j = k -> ( Z + j ) = ( Z + k ) )')], 'cbvprodv', 'prod_ j e. %s ( Z + j ) = prod_ k e. %s ( Z + k )' % (FZ, FZ))
    e = s([pe, a1(w, A, cb, 'prod_ j e. %s ( Z + j ) = prod_ k e. %s ( Z + k )' % (FZ, FZ))], 'eqtrd', 'prod_ j e. ( 0 ..^ K ) ( Z + j ) = prod_ k e. %s ( Z + k )' % FZ)
    w.qed([e, rv], 'eqtr4d', STATEMENTS['z6mrfp'])
    return w


# ---------------------------------------------------------------- z6mrdg
def z6mrdg():
    w = W('z6mrdg', 'The only integer on ` -u K - 1 / 2 <_ Re w <_ 1 / 2 - K ` is ` -u K ` : the rectangle minus that point lies in the domain of ` _G ` .')
    A = split_imp(STATEMENTS['z6mrdg'])[0]
    s = mkst(w, A)
    kn = w.s([], 'simpl', '( %s -> K e. NN0 )' % A)
    uc = w.s([], 'simprl', '( %s -> U e. CC )' % A)
    rest = w.s([], 'simprr', '( %s -> ( ( %s <_ ( Re ` U ) /\\ ( Re ` U ) <_ %s ) /\\ U =/= -u K ) )' % (A, AL, BR))
    lo = s([rest], 'simplld', '%s <_ ( Re ` U )' % AL)
    hi = s([rest], 'simplrd', '( Re ` U ) <_ %s' % BR)
    ne = s([rest], 'simprd', 'U =/= -u K')
    A1 = '( %s /\\ U e. ( ZZ \\ NN ) )' % A
    t = mkst(w, A1)
    uz = t([w.s([], 'simpr', '( %s -> U e. ( ZZ \\ NN ) )' % A1)], 'eldifad', 'U e. ZZ')
    ur = t([uz], 'zred', 'U e. RR')
    re = t([ur], 'rered', '( Re ` U ) = U')
    lo2 = t([lift(w, lo, A1), re], 'breqtrd', '%s <_ U' % AL)
    hi2 = t([re, lift(w, hi, A1)], 'eqbrtrrd', 'U <_ %s' % BR)
    kz = t([lift(w, kn, A1)], 'nn0zd', 'K e. ZZ')
    kr = t([kz], 'zred', 'K e. RR')
    nkz = t([kz], 'znegcld', '-u K e. ZZ')
    cl = Closure(w, A1, {'K': ('RR', kr), 'U': ('RR', ur)})
    M1 = '( -u K - 1 )'
    m1z = t([nkz, c1(w, A1, '1z', '1 e. ZZ')], 'zsubcld', '%s e. ZZ' % M1)
    l1 = linarith(w, A1, [lo2], '%s < U' % M1, closure=cl)
    l2 = t([l1, t([m1z, uz, w.inst('zltp1le')], 'syl2anc', '( %s < U <-> ( %s + 1 ) <_ U )' % (M1, M1))], 'mpbid', '( %s + 1 ) <_ U' % M1)
    l3 = linarith(w, A1, [l2], '-u K <_ U', closure=cl)
    h1 = linarith(w, A1, [hi2], 'U < ( -u K + 1 )', closure=cl)
    h2 = t([h1, t([uz, nkz, w.inst('zleltp1')], 'syl2anc', '( U <_ -u K <-> U < ( -u K + 1 ) )')], 'mpbird', 'U <_ -u K')
    eq = t([t([h2, l3], 'jca', '( U <_ -u K /\\ -u K <_ U )'), t([ur, cl.mem('-u K', 'RR')], 'letri3d', '( U = -u K <-> ( U <_ -u K /\\ -u K <_ U ) )')], 'mpbird', 'U = -u K')
    nz = w.s([eq, lift(w, s([ne], 'neneqd', '-. U = -u K'), A1)], 'pm2.65da', '( %s -> -. U e. ( ZZ \\ NN ) )' % A)
    w.qed([uc, nz], 'eldifd', STATEMENTS['z6mrdg'])
    return w


# ---------------------------------------------------------------- z6malg
def z6malg():
    w = W('z6malg', 'Field algebra: ` ( ( ( A ( R S ) ) Y ) / R ) / S = A Y ` .')
    A = split_imp(STATEMENTS['z6malg'])[0]
    s = mkst(w, A)
    ac = w.s([], 'simp1l', '( %s -> A e. CC )' % A); yc = w.s([], 'simp1r', '( %s -> Y e. CC )' % A)
    rc = w.s([], 'simp2l', '( %s -> R e. CC )' % A); rn = w.s([], 'simp2r', '( %s -> R =/= 0 )' % A)
    sc = w.s([], 'simp3l', '( %s -> S e. CC )' % A); sn = w.s([], 'simp3r', '( %s -> S =/= 0 )' % A)
    RS = '( R x. S )'
    rsc = s([rc, sc], 'mulcld', '%s e. CC' % RS); rsn = s([rc, sc, rn, sn], 'mulne0d', '%s =/= 0' % RS)
    X = '( ( A x. %s ) x. Y )' % RS
    xc = s([s([ac, rsc], 'mulcld', '( A x. %s ) e. CC' % RS), yc], 'mulcld', '%s e. CC' % X)
    e2 = s([xc, rc, sc, rn, sn], 'divdiv1d', '( ( %s / R ) / S ) = ( %s / %s )' % (X, X, RS))
    e1 = s([ac, rsc, yc], 'mul32d', '%s = ( ( A x. Y ) x. %s )' % (X, RS))
    e3 = s([e1], 'oveq1d', '( %s / %s ) = ( ( ( A x. Y ) x. %s ) / %s )' % (X, RS, RS, RS))
    e4 = s([s([ac, yc], 'mulcld', '( A x. Y ) e. CC'), rsc, rsn], 'divcan4d', '( ( ( A x. Y ) x. %s ) / %s ) = ( A x. Y )' % (RS, RS))
    w.qed([s([e2, e3], 'eqtrd', '( ( %s / R ) / S ) = ( ( ( A x. Y ) x. %s ) / %s )' % (X, RS, RS)), e4], 'eqtrd', STATEMENTS['z6malg'])
    return w


# ---------------------------------------------------------------- z6malg2
def z6malg2():
    w = W('z6malg2', 'Field algebra: ` ( 1 X ) / ( E F ) = ( E X ) / F ` when ` E E = 1 ` .')
    A = split_imp(STATEMENTS['z6malg2'])[0]
    s = mkst(w, A)
    xc = w.s([], 'simpl1', '( %s -> X e. CC )' % A); fc = w.s([], 'simpl2', '( %s -> F e. CC )' % A); fn = w.s([], 'simpl3', '( %s -> F =/= 0 )' % A)
    ec = w.s([], 'simprl', '( %s -> E e. CC )' % A); ee = w.s([], 'simprr', '( %s -> ( E x. E ) = 1 )' % A)
    een = s([ee, c1(w, A, 'ax-1ne0', '1 =/= 0')], 'eqnetrd', '( E x. E ) =/= 0')
    en = s([ec, ec, een], 'mulne0bad', 'E =/= 0')
    e1 = s([s([ee], 'eqcomd', '1 = ( E x. E )')], 'oveq1d', '( 1 x. X ) = ( ( E x. E ) x. X )')
    e2 = s([ec, ec, xc], 'mulassd', '( ( E x. E ) x. X ) = ( E x. ( E x. X ) )')
    e3 = s([s([e1, e2], 'eqtrd', '( 1 x. X ) = ( E x. ( E x. X ) )')], 'oveq1d', '( ( 1 x. X ) / ( E x. F ) ) = ( ( E x. ( E x. X ) ) / ( E x. F ) )')
    e4 = s([s([ec, xc], 'mulcld', '( E x. X ) e. CC'), fc, ec, fn, en], 'divcan5d', '( ( E x. ( E x. X ) ) / ( E x. F ) ) = ( ( E x. X ) / F )')
    w.qed([e3, e4], 'eqtrd', STATEMENTS['z6malg2'])
    return w


# ---------------------------------------------------------------- z6mfp
def z6mfp():
    w = W('z6mfp', 'The residue of the Mellin integrand at ` w = -u K ` : the Cauchy numerator there is '
          '` _G ( 1 ) Y ^ K / ( -u K RiseFac K ) = ( -u Y ) ^ K / K ! ` ( ~ gam1 , ~ risefallfac , ~ fallfacfac ).')
    A = '( Y e. RR+ /\\ K e. NN0 )'
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A); kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A)
    kr = s([kn], 'nn0red', 'K e. RR'); kc = s([kn], 'nn0cnd', 'K e. CC')
    yc = s([yrp], 'rpcnd', 'Y e. CC')
    cl = Closure(w, A, {'K': ('RR', kr)})
    S = MSTRIP
    nk = s([kr], 'renegcld', '-u K e. RR')
    rk = s([nk], 'rered', '( Re ` -u K ) = -u K')
    lo = s([linarith(w, A, [], '( -u K - 1 ) < -u K', closure=cl), rk], 'breqtrrd', '( -u K - 1 ) < ( Re ` -u K )')
    hi = s([rk, linarith(w, A, [], '-u K < ( 1 - K )', closure=cl)], 'eqbrtrd', '( Re ` -u K ) < ( 1 - K )')
    bi = s([s([cl.mem('( -u K - 1 )', 'RR')], 'rexrd', '( -u K - 1 ) e. RR*'), s([cl.mem('( 1 - K )', 'RR')], 'rexrd', '( 1 - K ) e. RR*'), w.inst('z6melst')], 'syl2anc',
           '( -u K e. %s <-> ( -u K e. CC /\\ ( ( -u K - 1 ) < ( Re ` -u K ) /\\ ( Re ` -u K ) < ( 1 - K ) ) ) )' % S)
    pS = s([s([s([nk], 'recnd', '-u K e. CC'), s([lo, hi], 'jca', '( ( -u K - 1 ) < ( Re ` -u K ) /\\ ( Re ` -u K ) < ( 1 - K ) )')], 'jca',
              '( -u K e. CC /\\ ( ( -u K - 1 ) < ( Re ` -u K ) /\\ ( Re ` -u K ) < ( 1 - K ) ) )'), bi], 'mpbird', '-u K e. %s' % S)
    BODY = '( ( ( _G ` ( w + ( K + 1 ) ) ) x. ( Y ^c -u w ) ) / ( w RiseFac K ) )'
    val, V = mpval(w, A, 'w', S, BODY, '-u K', pS)
    g1 = s([s([lineq(w, A, '( -u K + ( K + 1 ) )', '1', closure=cl)], 'fveq2d', '( _G ` ( -u K + ( K + 1 ) ) ) = ( _G ` 1 )'), c1(w, A, 'gam1', '( _G ` 1 ) = 1')],
           'eqtrd', '( _G ` ( -u K + ( K + 1 ) ) ) = 1')
    nn = s([kc], 'negnegd', '-u -u K = K')
    y1 = s([s([nn], 'oveq2d', '( Y ^c -u -u K ) = ( Y ^c K )'), s([yc, kn, w.inst('cxpexp')], 'syl2anc', '( Y ^c K ) = ( Y ^ K )')], 'eqtrd', '( Y ^c -u -u K ) = ( Y ^ K )')
    num_ = s([g1, y1], 'oveq12d', '( ( _G ` ( -u K + ( K + 1 ) ) ) x. ( Y ^c -u -u K ) ) = ( 1 x. ( Y ^ K ) )')
    E = '( -u 1 ^ K )'; F = '( ! ` K )'
    rf = s([s([kc], 'negcld', '-u K e. CC'), kn, w.inst('risefallfac')], 'syl2anc', '( -u K RiseFac K ) = ( %s x. ( -u -u K FallFac K ) )' % E)
    ff = s([s([nn], 'oveq1d', '( -u -u K FallFac K ) = ( K FallFac K )'), s([kn, w.inst('fallfacfac')], 'syl', '( K FallFac K ) = %s' % F)], 'eqtrd', '( -u -u K FallFac K ) = %s' % F)
    rf2 = s([rf, s([ff], 'oveq2d', '( %s x. ( -u -u K FallFac K ) ) = ( %s x. %s )' % (E, E, F))], 'eqtrd', '( -u K RiseFac K ) = ( %s x. %s )' % (E, F))
    v2 = s([val, s([num_, rf2], 'oveq12d', '%s = ( ( 1 x. ( Y ^ K ) ) / ( %s x. %s ) )' % (V, E, F))], 'eqtrd', '( %s ` -u K ) = ( ( 1 x. ( Y ^ K ) ) / ( %s x. %s ) )' % (MF0, E, F))
    m1c = c1(w, A, 'neg1cn', '-u 1 e. CC')
    ee = s([s([s([m1c, m1c, kn], 'mulexpd', '( ( -u 1 x. -u 1 ) ^ K ) = ( %s x. %s )' % (E, E))], 'eqcomd', '( %s x. %s ) = ( ( -u 1 x. -u 1 ) ^ K )' % (E, E)),
            s([s([c1(w, A, 'neg1mulneg1e1', '( -u 1 x. -u 1 ) = 1')], 'oveq1d', '( ( -u 1 x. -u 1 ) ^ K ) = ( 1 ^ K )'), s([s([kn], 'nn0zd', 'K e. ZZ'), w.inst('1exp')], 'syl', '( 1 ^ K ) = 1')],
              'eqtrd', '( ( -u 1 x. -u 1 ) ^ K ) = 1')], 'eqtrd', '( %s x. %s ) = 1' % (E, E))
    fn = s([kn, w.inst('faccl')], 'syl', '%s e. NN' % F)
    ykc = s([yc, kn], 'expcld', '( Y ^ K ) e. CC')
    ec = s([m1c, kn], 'expcld', '%s e. CC' % E)
    al = s([s([ykc, s([fn], 'nncnd', '%s e. CC' % F), s([fn], 'nnne0d', '%s =/= 0' % F)], '3jca', '( ( Y ^ K ) e. CC /\\ %s e. CC /\\ %s =/= 0 )' % (F, F)),
            s([ec, ee], 'jca', '( %s e. CC /\\ ( %s x. %s ) = 1 )' % (E, E, E)), w.inst('z6malg2')], 'syl2anc',
           '( ( 1 x. ( Y ^ K ) ) / ( %s x. %s ) ) = ( ( %s x. ( Y ^ K ) ) / %s )' % (E, F, E, F))
    ny = s([s([s([s([yc], 'mulm1d', '( -u 1 x. Y ) = -u Y')], 'eqcomd', '-u Y = ( -u 1 x. Y )')], 'oveq1d', '( -u Y ^ K ) = ( ( -u 1 x. Y ) ^ K )'),
            s([m1c, yc, kn], 'mulexpd', '( ( -u 1 x. Y ) ^ K ) = ( %s x. ( Y ^ K ) )' % E)], 'eqtrd', '( -u Y ^ K ) = ( %s x. ( Y ^ K ) )' % E)
    fin = s([s([v2, al], 'eqtrd', '( %s ` -u K ) = ( ( %s x. ( Y ^ K ) ) / %s )' % (MF0, E, F)), s([ny], 'oveq1d', '( ( -u Y ^ K ) / %s ) = ( ( %s x. ( Y ^ K ) ) / %s )' % (F, E, F))],
            'eqtr4d', '( %s ` -u K ) = ( ( -u Y ^ K ) / %s )' % (MF0, F))
    toqed(w, fin, 'z6mfp')
    return w


# ---------------------------------------------------------------- z6mfu
def z6mfu():
    w = W('z6mfu', 'Off ` w = -u K ` the Cauchy integrand of ~ z6mstep is the Mellin integrand: ` _G ( U + K + 1 ) = _G ( U ) ( U RiseFac K ) ( U + K ) ` '
          '( ~ z6gamfe , ~ z6mrfp , ~ risefacp1 ).')
    A = split_imp(STATEMENTS['z6mfu'])[0]
    s = mkst(w, A)
    S = MSTRIP
    yrp = w.s([], 'simpll', '( %s -> Y e. RR+ )' % A); kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % A)
    um = w.s([], 'simprl', '( %s -> U e. %s )' % (A, S)); ud = w.s([], 'simprr', '( %s -> U e. %s )' % (A, DG))
    uc = s([ud], 'eldifad', 'U e. CC'); kc = s([kn], 'nn0cnd', 'K e. CC')
    BODY = '( ( ( _G ` ( w + ( K + 1 ) ) ) x. ( Y ^c -u w ) ) / ( w RiseFac K ) )'
    val, V = mpval(w, A, 'w', S, BODY, 'U', um)
    sb = s([uc, kc], 'subnegd', '( U - -u K ) = ( U + K )')
    K1 = '( K + 1 )'
    k1n = s([kn, w.inst('peano2nn0')], 'syl', '%s e. NN0' % K1)
    PR = 'prod_ j e. ( 0 ..^ %s ) ( U + j )' % K1
    fe = s([ud, k1n, w.inst('z6gamfe')], 'syl2anc', '( _G ` ( U + %s ) ) = ( ( _G ` U ) x. %s )' % (K1, PR))
    RF = '( U RiseFac K )'; SK = '( U + K )'
    rp = s([s([uc, k1n, w.inst('z6mrfp')], 'syl2anc', '%s = ( U RiseFac %s )' % (PR, K1)), s([uc, kn, w.inst('risefacp1')], 'syl2anc', '( U RiseFac %s ) = ( %s x. %s )' % (K1, RF, SK))],
           'eqtrd', '%s = ( %s x. %s )' % (PR, RF, SK))
    ge = s([fe, s([rp], 'oveq2d', '( ( _G ` U ) x. %s ) = ( ( _G ` U ) x. ( %s x. %s ) )' % (PR, RF, SK))], 'eqtrd', '( _G ` ( U + %s ) ) = ( ( _G ` U ) x. ( %s x. %s ) )' % (K1, RF, SK))
    # R =/= 0
    FZ = '( 0 ... ( K - 1 ) )'
    rv = s([uc, kn, w.inst('risefacval')], 'syl2anc', '%s = prod_ k e. %s ( U + k )' % (RF, FZ))
    Ak = '( %s /\\ k e. %s )' % (A, FZ)
    tk = mkst(w, Ak)
    kk = w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, FZ)), w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % Ak)
    ukc = tk([lift(w, uc, Ak), tk([kk], 'nn0cnd', 'k e. CC')], 'addcld', '( U + k ) e. CC')
    ukn = tk([lift(w, ud, Ak), kk, w.inst('dmgmaddn0')], 'syl2anc', '( U + k ) =/= 0')
    pn = s([c1(w, A, 'fzfi', '%s e. Fin' % FZ), ukc, ukn], 'fprodn0', 'prod_ k e. %s ( U + k ) =/= 0' % FZ)
    rn = s([rv, pn], 'eqnetrd', '%s =/= 0' % RF)
    sn = s([ud, kn, w.inst('dmgmaddn0')], 'syl2anc', '%s =/= 0' % SK)
    Yu = '( Y ^c -u U )'
    yuc = s([s([yrp], 'rpcnd', 'Y e. CC'), s([uc], 'negcld', '-u U e. CC')], 'cxpcld', '%s e. CC' % Yu)
    gc = s([ud, w.inst('gamcl')], 'syl', '( _G ` U ) e. CC')
    al = s([s([gc, yuc], 'jca', '( ( _G ` U ) e. CC /\\ %s e. CC )' % Yu), s([s([uc, kn, w.inst('risefaccl')], 'syl2anc', '%s e. CC' % RF), rn], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (RF, RF)),
            s([s([uc, kc], 'addcld', '%s e. CC' % SK), sn], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (SK, SK)), w.inst('z6malg')], 'syl3anc',
           '( ( ( ( ( _G ` U ) x. ( %s x. %s ) ) x. %s ) / %s ) / %s ) = ( ( _G ` U ) x. %s )' % (RF, SK, Yu, RF, SK, Yu))
    GK = '( _G ` ( U + %s ) )' % K1
    e1 = s([val, sb], 'oveq12d', '( ( %s ` U ) / ( U - -u K ) ) = ( %s / %s )' % (MF0, V, SK))
    e2 = s([s([s([ge], 'oveq1d', '( %s x. %s ) = ( ( ( _G ` U ) x. ( %s x. %s ) ) x. %s )' % (GK, Yu, RF, SK, Yu))], 'oveq1d',
              '( ( %s x. %s ) / %s ) = ( ( ( ( _G ` U ) x. ( %s x. %s ) ) x. %s ) / %s )' % (GK, Yu, RF, RF, SK, Yu, RF))], 'oveq1d',
           '( %s / %s ) = ( ( ( ( ( _G ` U ) x. ( %s x. %s ) ) x. %s ) / %s ) / %s )' % (V, SK, RF, SK, Yu, RF, SK))
    w.qed([s([e1, e2], 'eqtrd', '( ( %s ` U ) / ( U - -u K ) ) = ( ( ( ( ( _G ` U ) x. ( %s x. %s ) ) x. %s ) / %s ) / %s )' % (MF0, RF, SK, Yu, RF, SK)), al],
          'eqtrd', STATEMENTS['z6mfu'])
    return w


# ---------------------------------------------------------------- z6mrect
def z6mrect():
    w = W('z6mrect', 'The rectangle ` [ -u K - 1 / 2 , 1 / 2 - K ] x [ -u T , T ] ` integral of the Mellin integrand is ` 2 pi i ( -u Y ) ^ K / K ! ` : '
          'Cauchy\'s formula ~ rectintcau at ` -u K ` for the numerator of ~ z6mfhol , ~ rectinteqp with ~ z6mfu , the residue ~ z6mfp .')
    A = split_imp(STATEMENTS['z6mrect'])[0]
    s = mkst(w, A)
    S = MSTRIP
    yrp = w.s([], 'simpll', '( %s -> Y e. RR+ )' % A); kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % A); trp = w.s([], 'simpr', '( %s -> T e. RR+ )' % A)
    kr = s([kn], 'nn0red', 'K e. RR'); tr = s([trp], 'rpred', 'T e. RR')
    cl = Closure(w, A, {'K': ('RR', kr), 'T': ('RR', tr)})
    alr = cl.mem(AL, 'RR'); brr = cl.mem(BR, 'RR'); ntr = cl.mem('-u T', 'RR')
    CA = '( %s + ( _i x. -u T ) )' % AL; CB = '( %s + ( _i x. T ) )' % BR; P = '-u K'
    ic = a1c(w, A, 'ax-icn', '_i e. CC')
    cac = s([s([alr], 'recnd', '%s e. CC' % AL), s([ic, s([ntr], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = s([s([brr], 'recnd', '%s e. CC' % BR), s([ic, s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CB)
    reA = s([alr, ntr], 'crred', '( Re ` %s ) = %s' % (CA, AL)); imA = s([alr, ntr], 'crimd', '( Im ` %s ) = -u T' % CA)
    reB = s([brr, tr], 'crred', '( Re ` %s ) = %s' % (CB, BR)); imB = s([brr, tr], 'crimd', '( Im ` %s ) = T' % CB)
    pr = cl.mem('-u K', 'RR'); pc = s([pr], 'recnd', '-u K e. CC')
    reP = s([pr], 'rered', '( Re ` -u K ) = -u K'); imP = s([pr, w.inst('reim0')], 'syl', '( Im ` -u K ) = 0')
    i1 = s([linarith(w, A, [], '%s < -u K' % AL, closure=cl), reA, reP], '3brtr4d', '( Re ` %s ) < ( Re ` -u K )' % CA)
    i2 = s([linarith(w, A, [], '-u K < %s' % BR, closure=cl), reP, reB], '3brtr4d', '( Re ` -u K ) < ( Re ` %s )' % CB)
    tg = s([trp], 'rpgt0d', '0 < T')
    i3 = s([linarith(w, A, [tg], '-u T < 0', closure=cl), imA, imP], '3brtr4d', '( Im ` %s ) < ( Im ` -u K )' % CA)
    i4 = s([tg, imP, imB], '3brtr4d', '( Im ` -u K ) < ( Im ` %s )' % CB)
    QP = '( ( ( Re ` %s ) < ( Re ` -u K ) /\\ ( Re ` -u K ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` -u K ) /\\ ( Im ` -u K ) < ( Im ` %s ) ) )' % (CA, CB, CA, CB)
    qp = s([s([i1, i2], 'jca', '( ( Re ` %s ) < ( Re ` -u K ) /\\ ( Re ` -u K ) < ( Re ` %s ) )' % (CA, CB)),
            s([i3, i4], 'jca', '( ( Im ` %s ) < ( Im ` -u K ) /\\ ( Im ` -u K ) < ( Im ` %s ) )' % (CA, CB))], 'jca', QP)
    ab = s([cac, cbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (CA, CB))
    pq = s([pc, qp], 'jca', '( -u K e. CC /\\ %s )' % QP)
    hol = s([s([yrp, kn], 'jca', '( Y e. RR+ /\\ K e. NN0 )'), w.inst('z6mfhol')], 'syl', HOLG(MF0, S))
    RT = '( %s crect %s )' % (CA, CB)
    riv = s([reA, reB], 'oveq12d', '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( %s [,] %s )' % (CA, CB, AL, BR))

    def inrect(Az, zm, z):
        t = mkst(w, Az)
        ec = t([lift(w, cac, Az), lift(w, cbc, Az), w.inst('elcrect')], 'syl2anc',
               '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (z, RT, z, z, CA, CB, z, CA, CB))
        z3 = t([zm, ec], 'mpbid', '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (z, z, CA, CB, z, CA, CB))
        zc = t([z3], 'simp1d', '%s e. CC' % z)
        ri = t([t([z3], 'simp2d', '( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (z, CA, CB)), lift(w, riv, Az)], 'eleqtrd', '( Re ` %s ) e. ( %s [,] %s )' % (z, AL, BR))
        r3 = t([ri, t([lift(w, alr, Az), lift(w, brr, Az), w.inst('elicc2')], 'syl2anc', '( ( Re ` %s ) e. ( %s [,] %s ) <-> ( ( Re ` %s ) e. RR /\\ %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) )'
                                                                                             % (z, AL, BR, z, AL, z, z, BR))],
               'mpbid', '( ( Re ` %s ) e. RR /\\ %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s )' % (z, AL, z, z, BR))
        rzr = t([r3], 'simp1d', '( Re ` %s ) e. RR' % z)
        lo = t([r3], 'simp2d', '%s <_ ( Re ` %s )' % (AL, z)); hi = t([r3], 'simp3d', '( Re ` %s ) <_ %s' % (z, BR))
        clz = Closure(w, Az, {'K': ('RR', lift(w, kr, Az)), '( Re ` %s )' % z: ('RR', rzr)})
        l1 = linarith(w, Az, [lo], '( -u K - 1 ) < ( Re ` %s )' % z, closure=clz)
        h1 = linarith(w, Az, [hi], '( Re ` %s ) < ( 1 - K )' % z, closure=clz)
        bi = t([t([clz.mem('( -u K - 1 )', 'RR')], 'rexrd', '( -u K - 1 ) e. RR*'), t([clz.mem('( 1 - K )', 'RR')], 'rexrd', '( 1 - K ) e. RR*'), w.inst('z6melst')], 'syl2anc',
               '( %s e. %s <-> ( %s e. CC /\\ ( ( -u K - 1 ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( 1 - K ) ) ) )' % (z, S, z, z, z))
        zs = t([t([zc, t([l1, h1], 'jca', '( ( -u K - 1 ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( 1 - K ) )' % (z, z))], 'jca',
                  '( %s e. CC /\\ ( ( -u K - 1 ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( 1 - K ) ) )' % (z, z, z)), bi], 'mpbird', '%s e. %s' % (z, S))
        return zc, lo, hi, zs
    Az = '( %s /\\ z e. %s )' % (A, RT)
    _, _, _, zs = inrect(Az, w.s([], 'simpr', '( %s -> z e. %s )' % (Az, RT)), 'z')
    rs = s([w.s([zs], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (A, RT, S))], 'ssrdv', '%s C_ %s' % (RT, S))
    rdom = s([rs, s([hol], 'simprd', '%s C_ dom ( CC _D %s )' % (S, MF0))], 'sstrd', '%s C_ dom ( CC _D %s )' % (RT, MF0))
    HZ = '( z e. ( %s \\ { -u K } ) |-> ( ( %s ` z ) / ( z - -u K ) ) )' % (RT, MF0)
    cau = s([s([ab, pq, s([s([hol], 'simpld', '%s e. ( %s -cn-> CC )' % (MF0, S)), rdom], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (MF0, S, RT, MF0))], '3jca',
               '( ( %s e. CC /\\ %s e. CC ) /\\ ( -u K e. CC /\\ %s ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (CA, CB, QP, MF0, S, RT, MF0)),
             w.inst('rectintcau')], 'syl', '( %s rectint <. %s , %s >. ) = ( %s x. ( %s ` -u K ) )' % (HZ, CA, CB, TPI, MF0))
    # the Mellin integrand agrees with HZ off -u K
    RP = '( %s \\ { -u K } )' % RT
    Au = '( %s /\\ u e. %s )' % (A, RP)
    t = mkst(w, Au)
    um = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, RP))
    ud2 = t([um, w.s([], 'eldifsn', '( u e. %s <-> ( u e. %s /\\ u =/= -u K ) )' % (RP, RT))], 'sylib', '( u e. %s /\\ u =/= -u K )' % RT)
    urt = t([ud2], 'simpld', 'u e. %s' % RT); une = t([ud2], 'simprd', 'u =/= -u K')
    uc, lo, hi, us = inrect(Au, urt, 'u')
    udg = t([lift(w, kn, Au), t([uc, t([t([lo, hi], 'jca', '( %s <_ ( Re ` u ) /\\ ( Re ` u ) <_ %s )' % (AL, BR)), une], 'jca',
                                      '( ( %s <_ ( Re ` u ) /\\ ( Re ` u ) <_ %s ) /\\ u =/= -u K )' % (AL, BR))], 'jca',
                                '( u e. CC /\\ ( ( %s <_ ( Re ` u ) /\\ ( Re ` u ) <_ %s ) /\\ u =/= -u K ) )' % (AL, BR)), w.inst('z6mrdg')], 'syl2anc', 'u e. %s' % DG)
    gyv, _ = mpval(w, Au, 'w', DG, '( ( _G ` w ) x. ( Y ^c -u w ) )', 'u', udg)
    hzv, _ = mpval(w, Au, 'z', RP, '( ( %s ` z ) / ( z - -u K ) )' % MF0, 'u', um)
    fu = t([t([lift(w, yrp, Au), lift(w, kn, Au)], 'jca', '( Y e. RR+ /\\ K e. NN0 )'), t([us, udg], 'jca', '( u e. %s /\\ u e. %s )' % (S, DG)), w.inst('z6mfu')], 'syl2anc',
           '( ( %s ` u ) / ( u - -u K ) ) = ( ( _G ` u ) x. ( Y ^c -u u ) )' % MF0)
    eu = t([gyv, t([hzv, fu], 'eqtrd', '( %s ` u ) = ( ( _G ` u ) x. ( Y ^c -u u ) )' % HZ)], 'eqtr4d', '( %s ` u ) = ( %s ` u )' % (GYM, HZ))
    ral = s([eu], 'ralrimiva', 'A. u e. %s ( %s ` u ) = ( %s ` u )' % (RP, GYM, HZ))
    dgv = w.s([w.s([], 'cnex', 'CC e. _V')], 'difexi', '%s e. _V' % DG)
    gyx = a1(w, A, w.s([dgv], 'mptex', '%s e. _V' % GYM), '%s e. _V' % GYM)
    rpv = w.s([w.s([], 'ovex', '%s e. _V' % RT)], 'difexi', '%s e. _V' % RP)
    hzx = a1(w, A, w.s([rpv], 'mptex', '%s e. _V' % HZ), '%s e. _V' % HZ)
    eqp = s([s([s([ab, pq], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( -u K e. CC /\\ %s ) )' % (CA, CB, QP)), s([gyx, hzx], 'jca', '( %s e. _V /\\ %s e. _V )' % (GYM, HZ)), ral], '3jca',
               '( ( ( %s e. CC /\\ %s e. CC ) /\\ ( -u K e. CC /\\ %s ) ) /\\ ( %s e. _V /\\ %s e. _V ) /\\ A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (CA, CB, QP, GYM, HZ, RP, GYM, HZ)),
             w.inst('rectinteqp')], 'syl', '( %s rectint <. %s , %s >. ) = ( %s rectint <. %s , %s >. )' % (GYM, CA, CB, HZ, CA, CB))
    fp = s([s([yrp, kn], 'jca', '( Y e. RR+ /\\ K e. NN0 )'), w.inst('z6mfp')], 'syl', '( %s ` -u K ) = ( ( -u Y ^ K ) / ( ! ` K ) )' % MF0)
    fin = s([s([eqp, cau], 'eqtrd', '( %s rectint <. %s , %s >. ) = ( %s x. ( %s ` -u K ) )' % (GYM, CA, CB, TPI, MF0)),
             s([fp], 'oveq2d', '( %s x. ( %s ` -u K ) ) = ( %s x. ( ( -u Y ^ K ) / ( ! ` K ) ) )' % (TPI, MF0, TPI))], 'eqtrd',
            '( %s rectint <. %s , %s >. ) = ( %s x. ( ( -u Y ^ K ) / ( ! ` K ) ) )' % (GYM, CA, CB, TPI))
    toqed(w, fin, 'z6mrect')
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6mgyvc, z6mrfp, z6mrdg, z6malg, z6malg2, z6mfp, z6mfu, z6mrect]:
        if want(f.__name__):
            if run(f()):
                status(f.__name__)
            else:
                break
