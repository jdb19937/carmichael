"""Z6a (block z6ab): Gamma is holomorphic on ( CC \\ ( ZZ \\ NN ) ) (z6hdgopn, z6hgind, z6gamhold)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_ghlib import *
from lin import linarith

EN = lambda N: '( %s i^i %s )' % (HPT('-u %s' % N), DG)
PN = lambda N: HOLG('( x e. %s |-> ( _G ` x ) )' % EN(N), EN(N))
S_DGOPN = '%s e. %s' % (DG, TOP)
S_GIND = '( N e. NN0 -> %s )' % PN('N')
GZ = '( z e. %s |-> ( _G ` z ) )' % HPZ


def cbvm(w, ante, x, y, X, bx):
    """( ante -> ( x e. X |-> bx ) = ( y e. X |-> by ) )"""
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, y, x, y))
    stp, by = w.congr(bx, {x: y}, '%s = %s' % (x, y), {x: idk})
    c = w.s([stp if stp else idk], 'cbvmptv', '( %s e. %s |-> %s ) = ( %s e. %s |-> %s )' % (x, X, bx, y, X, by))
    return w.s([c], 'a1i', '( %s -> ( %s e. %s |-> %s ) = ( %s e. %s |-> %s ) )' % (ante, x, X, bx, y, X, by)), '( %s e. %s |-> %s )' % (y, X, by)


def hpmem(w, ante, T, tr, X, xc, lt):
    """( ante -> X e. HPT(T) ) from tr: T e. RR, xc: X e. CC, lt: T < Re X"""
    bi = w.s([tr, w.inst('elhp2')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ %s < ( Re ` %s ) ) ) )' % (ante, X, HPT(T), X, T, X))
    return w.s([w.s([xc, lt], 'jca', '( %s -> ( %s e. CC /\\ %s < ( Re ` %s ) ) )' % (ante, X, T, X)), bi], 'mpbird', '( %s -> %s e. %s )' % (ante, X, HPT(T)))


def hpget(w, ante, T, tr, X, xm):
    """from xm: ( ante -> X e. HPT(T) ): (X e. CC, T < Re X)"""
    bi = w.s([tr, w.inst('elhp2')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ %s < ( Re ` %s ) ) ) )' % (ante, X, HPT(T), X, T, X))
    both = w.s([xm, bi], 'mpbid', '( %s -> ( %s e. CC /\\ %s < ( Re ` %s ) ) )' % (ante, X, T, X))
    return w.s([both], 'simpld', '( %s -> %s e. CC )' % (ante, X)), w.s([both], 'simprd', '( %s -> %s < ( Re ` %s ) )' % (ante, T, X))


def dgopn():
    w = W('z6hdgopn', 'The domain of the Gamma function, the plane minus the nonpositive integers, is open ( ~ sszcld ).')
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    cl = w.s([w.s([], 'difss', '( ZZ \\ NN ) C_ ZZ'), w.s([e], 'sszcld', '( ( ZZ \\ NN ) C_ ZZ -> ( ZZ \\ NN ) e. ( Clsd ` %s ) )' % TOP)], 'ax-mp',
             '( ZZ \\ NN ) e. ( Clsd ` %s )' % TOP)
    w.qed([cl, w.s([w.s([], 'unicntop', 'CC = U. %s' % TOP)], 'cldopn', '( ( ZZ \\ NN ) e. ( Clsd ` %s ) -> %s e. %s )' % (TOP, DG, TOP))], 'ax-mp', S_DGOPN)
    return run(w)


def gind():
    w = W('z6hgind', 'The Gamma function is holomorphic on ` -u N < Re z ` minus the poles, for every ` N e. NN0 ` : '
          'induction on ` N ` with ` Gamma ( z ) = Gamma ( z + 1 ) / z ` ( ~ gamp1 , ~ z6hshift , ~ holdiv ).')

    def holbi(A, Ma, Da, Mb, Db, meq, deq):
        b1 = w.s([meq, w.s([deq], 'oveq1d', '( %s -> ( %s -cn-> CC ) = ( %s -cn-> CC ) )' % (A, Da, Db))], 'eleq12d',
                 '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (A, Ma, Da, Mb, Db))
        b2 = w.s([deq, w.s([w.s([meq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A, Ma, Mb))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A, Ma, Mb))],
                 'sseq12d', '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (A, Da, Ma, Db, Mb))
        return w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (A, HOLG(Ma, Da), HOLG(Mb, Db)))

    def eneq(T):
        A = 'n = %s' % T
        s1 = w.s([], 'negeq', '( %s -> -u n = -u %s )' % (A, T))
        s2 = w.s([s1], 'oveq1d', '( %s -> ( -u n (,) +oo ) = ( -u %s (,) +oo ) )' % (A, T))
        s3 = w.s([s2], 'imaeq2d', '( %s -> %s = %s )' % (A, HPT('-u n'), HPT('-u %s' % T)))
        return w.s([s3], 'ineq1d', '( %s -> %s = %s )' % (A, EN('n'), EN(T)))

    def eqv(T):
        A = 'n = %s' % T
        d = eneq(T)
        m = w.s([d], 'mpteq1d', '( %s -> ( x e. %s |-> ( _G ` x ) ) = ( x e. %s |-> ( _G ` x ) ) )' % (A, EN('n'), EN(T)))
        return holbi(A, '( x e. %s |-> ( _G ` x ) )' % EN('n'), EN('n'), '( x e. %s |-> ( _G ` x ) )' % EN(T), EN(T), m, d)
    # n = 0: E_n = HPZ and the mapping is GZ
    A = 'n = 0'
    e1 = eneq('0')
    hz = w.s([w.s([w.s([w.s([], 'neg0', '-u 0 = 0')], 'oveq1i', '( -u 0 (,) +oo ) = ( 0 (,) +oo )')], 'imaeq2i', '%s = %s' % (HPT('-u 0'), HPZ))], 'ineq1i',
             '%s = ( %s i^i %s )' % (EN('0'), HPZ, DG))
    Az = 'z e. %s' % HPZ
    r0 = w.s([], '0re', '0 e. RR')
    bz = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (Az, Az)), w.s([w.s([r0, w.inst('elhp2')], 'ax-mp', '( z e. %s <-> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % HPZ)], 'a1i',
                                                                   '( %s -> ( z e. %s <-> ( z e. CC /\\ 0 < ( Re ` z ) ) ) )' % (Az, HPZ))], 'mpbid',
              '( %s -> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % Az), w.inst('zrenn')], 'syl', '( %s -> z e. %s )' % (Az, DG))
    ssd = w.s([bz], 'ssriv', '%s C_ %s' % (HPZ, DG))
    inq = w.s([ssd, w.inst('dfss2')], 'mpbi', '( %s i^i %s ) = %s' % (HPZ, DG, HPZ))
    e0 = w.s([hz, inq], 'eqtri', '%s = %s' % (EN('0'), HPZ))
    en0 = w.s([e1, w.s([e0], 'a1i', '( %s -> %s = %s )' % (A, EN('0'), HPZ))], 'eqtrd', '( %s -> %s = %s )' % (A, EN('n'), HPZ))
    MX = '( x e. %s |-> ( _G ` x ) )' % EN('n')
    m1 = w.s([en0], 'mpteq1d', '( %s -> %s = ( x e. %s |-> ( _G ` x ) ) )' % (A, MX, HPZ))
    cz, _ = cbvm(w, A, 'x', 'z', HPZ, '( _G ` x )')
    mq = w.s([m1, cz], 'eqtrd', '( %s -> %s = %s )' % (A, MX, GZ))
    b1 = w.s([mq, w.s([en0], 'oveq1d', '( %s -> ( %s -cn-> CC ) = ( %s -cn-> CC ) )' % (A, EN('n'), HPZ))], 'eleq12d',
             '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (A, MX, EN('n'), GZ, HPZ))
    b2 = w.s([en0, w.s([w.s([mq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A, MX, GZ))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A, MX, GZ))],
             'sseq12d', '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (A, EN('n'), MX, HPZ, GZ))
    h1 = w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (A, PN('n'), HOLG(GZ, HPZ)))
    h2 = eqv('m'); h3 = eqv('( m + 1 )'); h4 = eqv('N')
    h5 = w.s([], 'z6gamhol', HOLG(GZ, HPZ))
    # the step
    A = '( m e. NN0 /\\ %s )' % PN('m')
    s = st(w, A)
    mn = w.s([], 'simpl', '( %s -> m e. NN0 )' % A)
    hm = w.s([], 'simpr', '( %s -> %s )' % (A, PN('m')))
    mr = s([mn], 'nn0red', 'm e. RR')
    nm = s([mr], 'renegcld', '-u m e. RR')
    nm1 = s([s([mr, w.inst('peano2re')], 'syl', '( m + 1 ) e. RR')], 'renegcld', '-u ( m + 1 ) e. RR')
    e_ = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    top = c1(w, A, 'cnfldtop', '%s e. Top' % TOP)
    w.lines[-2] = w.lines[-2].replace('::cnfldtop', ':%s:cnfldtop' % e_)
    dgo = c1(w, A, 'z6hdgopn', S_DGOPN)
    em1o = s([top, c1(w, A, 'hpopn', '%s e. %s' % (HPT('-u ( m + 1 )'), TOP)), dgo, w.inst('inopn')], 'syl3anc', '%s e. %s' % (EN('( m + 1 )'), TOP))
    # ( w + 1 ) e. E_m for w e. E_( m + 1 )
    Aw = '( %s /\\ w e. %s )' % (A, EN('( m + 1 )'))
    t = st(w, Aw)
    wm = w.s([], 'simpr', '( %s -> w e. %s )' % (Aw, EN('( m + 1 )')))
    wh = t([wm], 'elin1d', 'w e. %s' % HPT('-u ( m + 1 )'))
    wd = t([wm], 'elin2d', 'w e. %s' % DG)
    wc, wlt = hpget(w, Aw, '-u ( m + 1 )', w.s([nm1], 'adantr', '( %s -> -u ( m + 1 ) e. RR )' % Aw), 'w', wh)
    w1d = t([wd, c1(w, Aw, '1nn0', '1 e. NN0')], 'dmgmaddnn0', '( w + 1 ) e. %s' % DG)
    rw1 = t([t([wc, c1(w, Aw, 'ax-1cn', '1 e. CC')], 'readdd', '( Re ` ( w + 1 ) ) = ( ( Re ` w ) + ( Re ` 1 ) )'),
             t([c1(w, Aw, 're1', '( Re ` 1 ) = 1')], 'oveq2d', '( ( Re ` w ) + ( Re ` 1 ) ) = ( ( Re ` w ) + 1 )')], 'eqtrd', '( Re ` ( w + 1 ) ) = ( ( Re ` w ) + 1 )')
    rwr = t([wc], 'recld', '( Re ` w ) e. RR')
    mrw = w.s([mr], 'adantr', '( %s -> m e. RR )' % Aw)
    lt1 = linarith(w, Aw, [wlt], '-u m < ( ( Re ` w ) + 1 )', leaves={'( Re ` w )': rwr, 'm': mrw})
    w1h = hpmem(w, Aw, '-u m', w.s([nm], 'adantr', '( %s -> -u m e. RR )' % Aw), '( w + 1 )', t([wc, c1(w, Aw, 'ax-1cn', '1 e. CC')], 'addcld', '( w + 1 ) e. CC'),
                t([lt1, rw1], 'breqtrrd', '-u m < ( Re ` ( w + 1 ) )'))
    w1e = t([w1h, w1d], 'elind', '( w + 1 ) e. %s' % EN('m'))
    ral = s([w1e], 'ralrimiva', 'A. w e. %s ( w + 1 ) e. %s' % (EN('( m + 1 )'), EN('m')))
    FX = '( x e. %s |-> ( _G ` x ) )' % EN('m')
    E1 = EN('( m + 1 )')
    ZS = '( z e. %s |-> ( %s ` ( z + 1 ) ) )' % (E1, FX)
    sh = s([hm, s([em1o, c1(w, A, 'ax-1cn', '1 e. CC'), ral], '3jca', '( %s e. %s /\\ 1 e. CC /\\ A. w e. %s ( w + 1 ) e. %s )' % (E1, TOP, E1, EN('m'))), w.inst('z6hshift')],
           'syl2anc', HOLG(ZS, E1))
    c2, F2 = cbvm(w, A, 'z', 'b', E1, '( %s ` ( z + 1 ) )' % FX)
    hf2 = holeq(w, A, ZS, F2, E1, sh, c2)
    ZI = '( z e. %s |-> z )' % E1
    hiz = s([em1o, w.inst('z6hid')], 'syl', HOLG(ZI, E1))
    c3, G2 = cbvm(w, A, 'z', 'b', E1, 'z')
    hg2 = holeq(w, A, ZI, G2, E1, hiz, c3)
    Av = '( %s /\\ v e. %s )' % (A, E1)
    vm = w.s([], 'simpr', '( %s -> v e. %s )' % (Av, E1))
    gv, _ = mpval(w, Av, 'b', E1, 'b', 'v', vm, exs=w.s([w.s([], 'vex', 'v e. _V')], 'a1i', '( %s -> v e. _V )' % Av))
    vn = w.s([w.s([vm], 'elin2d', '( %s -> v e. %s )' % (Av, DG))], 'dmgmn0', '( %s -> v =/= 0 )' % Av)
    nz = s([w.s([gv, vn], 'eqnetrd', '( %s -> ( %s ` v ) =/= 0 )' % (Av, G2))], 'ralrimiva', 'A. v e. %s ( %s ` v ) =/= 0' % (E1, G2))
    DV = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (E1, F2, G2)
    hd = s([hf2, hg2, nz, w.inst('holdiv')], 'syl3anc', HOLG(DV, E1))
    Az = '( %s /\\ z e. %s )' % (A, E1)
    u = st(w, Az)
    zm = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, E1))
    zd = u([zm], 'elin2d', 'z e. %s' % DG)
    zc = u([zd], 'eldifad', 'z e. CC')
    zn = u([zd], 'dmgmn0', 'z =/= 0')
    z1 = u([w.s([w.s([], 'oveq1', '( w = z -> ( w + 1 ) = ( z + 1 ) )')], 'eleq1d', '( w = z -> ( ( w + 1 ) e. %s <-> ( z + 1 ) e. %s ) )' % (EN('m'), EN('m'))),
            w.s([ral], 'adantr', '( %s -> A. w e. %s ( w + 1 ) e. %s )' % (Az, E1, EN('m'))), zm], 'rspcdva', '( z + 1 ) e. %s' % EN('m'))
    f2z, _ = mpval(w, Az, 'b', E1, '( %s ` ( b + 1 ) )' % FX, 'z', zm)
    fxz, _ = mpval(w, Az, 'x', EN('m'), '( _G ` x )', '( z + 1 )', z1)
    g2z, _ = mpval(w, Az, 'b', E1, 'b', 'z', zm, exs=w.s([w.s([], 'vex', 'z e. _V')], 'a1i', '( %s -> z e. _V )' % Az))
    gp = u([zd, w.inst('gamp1')], 'syl', '( _G ` ( z + 1 ) ) = ( ( _G ` z ) x. z )')
    q = u([u([u([f2z, fxz, gp], '3eqtrd', '( %s ` z ) = ( ( _G ` z ) x. z )' % F2), g2z], 'oveq12d', '( ( %s ` z ) / ( %s ` z ) ) = ( ( ( _G ` z ) x. z ) / z )' % (F2, G2)),
           u([u([zd, w.inst('gamcl')], 'syl', '( _G ` z ) e. CC'), zc, zn], 'divcan4d', '( ( ( _G ` z ) x. z ) / z ) = ( _G ` z )')], 'eqtrd',
          '( ( %s ` z ) / ( %s ` z ) ) = ( _G ` z )' % (F2, G2))
    GE = '( z e. %s |-> ( _G ` z ) )' % E1
    hge = holeq(w, A, DV, GE, E1, hd, s([q], 'mpteq2dva', '%s = %s' % (DV, GE)))
    c4, GX = cbvm(w, A, 'z', 'x', E1, '( _G ` z )')
    fin = holeq(w, A, GE, GX, E1, hge, c4)
    h6 = w.s([fin], 'ex', '( m e. NN0 -> ( %s -> %s ) )' % (PN('m'), PN('( m + 1 )')))
    w.qed([h1, h2, h3, h4, h5, h6], 'nn0ind', S_GIND)
    return run(w)


def gamhold():
    w = W('z6gamhold', 'The Gamma function is holomorphic on its domain ` ( CC \\ ( ZZ \\ NN ) ) ` : Lean\'s '
          '` Complex.differentiableAt_Gamma ` ( ~ z6hgind on ` -u n < Re z ` , ~ holloc ).')
    G = '( z e. %s |-> ( _G ` z ) )' % DG
    Ay = 'y e. %s' % DG
    yc = w.s([], 'eldifi', '( %s -> y e. CC )' % Ay)
    ry = w.s([yc], 'recld', '( %s -> ( Re ` y ) e. RR )' % Ay)
    ar = w.s([w.s([ry], 'renegcld', '( %s -> -u ( Re ` y ) e. RR )' % Ay), w.inst('arch')], 'syl', '( %s -> E. n e. NN -u ( Re ` y ) < n )' % Ay)
    A = '( ( %s /\\ n e. NN ) /\\ -u ( Re ` y ) < n )' % Ay
    s = st(w, A)
    nn = w.s([], 'simplr', '( %s -> n e. NN )' % A)
    lt = w.s([], 'simpr', '( %s -> -u ( Re ` y ) < n )' % A)
    yd = w.s([], 'simpll', '( %s -> y e. %s )' % (A, DG))
    yca = s([yd], 'eldifad', 'y e. CC')
    nr = s([nn], 'nnred', 'n e. RR')
    rya = s([yca], 'recld', '( Re ` y ) e. RR')
    lt2 = linarith(w, A, [lt], '-u n < ( Re ` y )', leaves={'( Re ` y )': rya, 'n': nr})
    yh = hpmem(w, A, '-u n', s([nr], 'renegcld', '-u n e. RR'), 'y', yca, lt2)
    ye = s([yh, yd], 'elind', 'y e. %s' % EN('n'))
    e_ = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    top = s([w.s([e_], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '%s e. Top' % TOP)
    eo = s([top, c1(w, A, 'hpopn', '%s e. %s' % (HPT('-u n'), TOP)), c1(w, A, 'z6hdgopn', S_DGOPN), w.inst('inopn')], 'syl3anc', '%s e. %s' % (EN('n'), TOP))
    ess = c1(w, A, 'inss2', '%s C_ %s' % (EN('n'), DG))
    pn = s([s([nn], 'nnnn0d', 'n e. NN0'), w.inst('z6hgind')], 'syl', PN('n'))
    c, GZn = cbvm(w, A, 'x', 'z', EN('n'), '( _G ` x )')
    hz = holeq(w, A, '( x e. %s |-> ( _G ` x ) )' % EN('n'), GZn, EN('n'), pn, c)
    res = s([ess, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (G, EN('n'), GZn))
    dss = s([s([hz], 'simprd', '%s C_ dom ( CC _D %s )' % (EN('n'), GZn)),
             s([s([res], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D %s )' % (G, EN('n'), GZn))], 'dmeqd', 'dom ( CC _D ( %s |` %s ) ) = dom ( CC _D %s )' % (G, EN('n'), GZn))],
            'sseqtrrd', '%s C_ dom ( CC _D ( %s |` %s ) )' % (EN('n'), G, EN('n')))
    U = EN('n')
    LOC = lambda u: '( y e. %s /\\ %s C_ %s /\\ %s C_ dom ( CC _D ( %s |` %s ) ) )' % (u, u, DG, u, G, u)
    sub = w.s([w.s([], 'eleq2', '( u = %s -> ( y e. u <-> y e. %s ) )' % (U, U)), w.s([], 'sseq1', '( u = %s -> ( u C_ %s <-> %s C_ %s ) )' % (U, DG, U, DG)),
               w.s([w.s([], 'id', '( u = %s -> u = %s )' % (U, U)), w.s([w.s([w.s([], 'reseq2', '( u = %s -> ( %s |` u ) = ( %s |` %s ) )' % (U, G, G, U))], 'oveq2d',
                                                                             '( u = %s -> ( CC _D ( %s |` u ) ) = ( CC _D ( %s |` %s ) ) )' % (U, G, G, U))], 'dmeqd',
                                                                        '( u = %s -> dom ( CC _D ( %s |` u ) ) = dom ( CC _D ( %s |` %s ) ) )' % (U, G, G, U))], 'sseq12d',
                   '( u = %s -> ( u C_ dom ( CC _D ( %s |` u ) ) <-> %s C_ dom ( CC _D ( %s |` %s ) ) ) )' % (U, G, U, G, U))], '3anbi123d',
              '( u = %s -> ( %s <-> %s ) )' % (U, LOC('u'), LOC(U)))
    ex = s([s([eo, s([ye, ess, dss], '3jca', LOC(U))], 'jca', '( %s e. %s /\\ %s )' % (U, TOP, LOC(U))),
            w.s([sub], 'rspcev', '( ( %s e. %s /\\ %s ) -> E. u e. %s %s )' % (U, TOP, LOC(U), TOP, LOC('u')))], 'syl', 'E. u e. %s %s' % (TOP, LOC('u')))
    exy = w.s([ex, ar], 'r19.29a', '( %s -> E. u e. %s %s )' % (Ay, TOP, LOC('u')))
    ral = w.s([exy], 'rgen', 'A. y e. %s E. u e. %s %s' % (DG, TOP, LOC('u')))
    gf = w.s([w.s([], 'gamcl', '( z e. %s -> ( _G ` z ) e. CC )' % DG)], 'fmpti', '%s : %s --> CC' % (G, DG))
    pre = w.s([w.s([gf, w.s([], 'difss', '%s C_ CC' % DG)], 'pm3.2i', '( %s : %s --> CC /\\ %s C_ CC )' % (G, DG, DG)), ral], 'pm3.2i',
              '( ( %s : %s --> CC /\\ %s C_ CC ) /\\ A. y e. %s E. u e. %s %s )' % (G, DG, DG, DG, TOP, LOC('u')))
    w.qed([pre, w.inst('holloc')], 'ax-mp', STATEMENTS['z6gamhold'])
    return run(w)


if __name__ == '__main__':
    want = sys.argv[1:]
    for lab, fn in [('z6hdgopn', dgopn), ('z6hgind', gind), ('z6gamhold', gamhold)]:
        if lab in want:
            if fn():
                status(lab)
