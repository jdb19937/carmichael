"""Z6a (block D): holomorphy of the Mellin integrands (z6mstopn, z6melst, z6mycxh, z6gyhol, z6mrfhol, z6mfhol)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_mlib import *

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


# ---------------------------------------------------------------- z6mstopn
def z6mstopn():
    w = W('z6mstopn', 'An open vertical strip ` A < Re z < B ` is an open set of the complex plane ( ~ hpopn with a bounded interval).')
    X = STRIP('A', 'B')
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    s2 = w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))
    s3 = w.s([s2], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    s4 = w.s([], 'tgioo4', '( topGen ` ran (,) ) = ( %s |`t RR )' % TOP)
    s5 = w.s([], 'ssid', 'CC C_ CC')
    s6 = w.s([], 'ax-resscn', 'RR C_ CC')
    s7 = w.s([e, s3, s4], 'cncfcn', '( ( CC C_ CC /\\ RR C_ CC ) -> ( CC -cn-> RR ) = ( %s Cn ( topGen ` ran (,) ) ) )' % TOP)
    s8 = w.s([s5, s6, s7], 'mp2an', '( CC -cn-> RR ) = ( %s Cn ( topGen ` ran (,) ) )' % TOP)
    s9 = w.s([], 'recncf', 'Re e. ( CC -cn-> RR )')
    s10 = w.s([s9, s8], 'eleqtri', 'Re e. ( %s Cn ( topGen ` ran (,) ) )' % TOP)
    s11 = w.s([], 'iooretop', '( A (,) B ) e. ( topGen ` ran (,) )')
    w.qed([s10, s11, w.inst('cnima')], 'mp2an', STATEMENTS['z6mstopn'])
    return w


# ---------------------------------------------------------------- z6melst
def z6melst():
    w = W('z6melst', 'Membership in the open vertical strip ` A < Re z < B ` ( ~ elpreima , ~ elioo2 ).')
    X = STRIP('A', 'B')
    fr = w.s([], 'ref', 'Re : CC --> RR')
    fn = w.s([fr, w.inst('ffn')], 'ax-mp', 'Re Fn CC')
    ep = w.s([fn, w.inst('elpreima')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ ( Re ` Z ) e. ( A (,) B ) ) )' % X)
    AB = '( A e. RR* /\\ B e. RR* )'
    A0 = '( %s /\\ Z e. CC )' % AB
    st_ = mkst(w, A0)
    RZ = '( Re ` Z )'
    I2 = '( A < %s /\\ %s < B )' % (RZ, RZ)
    ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
    e2 = st_([ab, w.inst('elioo2')], 'syl', '( %s e. ( A (,) B ) <-> ( %s e. RR /\\ A < %s /\\ %s < B ) )' % (RZ, RZ, RZ, RZ))
    e3 = w.s([], '3anass', '( ( %s e. RR /\\ A < %s /\\ %s < B ) <-> ( %s e. RR /\\ %s ) )' % (RZ, RZ, RZ, RZ, I2))
    e23 = st_([e2, a1(w, A0, e3, '( ( %s e. RR /\\ A < %s /\\ %s < B ) <-> ( %s e. RR /\\ %s ) )' % (RZ, RZ, RZ, RZ, I2))], 'bitrd',
              '( %s e. ( A (,) B ) <-> ( %s e. RR /\\ %s ) )' % (RZ, RZ, I2))
    rz = st_([w.s([], 'simpr', '( %s -> Z e. CC )' % A0)], 'recld', '%s e. RR' % RZ)
    e4 = st_([rz], 'biantrurd', '( %s <-> ( %s e. RR /\\ %s ) )' % (I2, RZ, I2))
    e5 = st_([e23, e4], 'bitr4d', '( %s e. ( A (,) B ) <-> %s )' % (RZ, I2))
    e6 = w.s([e5], 'pm5.32da', '( %s -> ( ( Z e. CC /\\ %s e. ( A (,) B ) ) <-> ( Z e. CC /\\ %s ) ) )' % (AB, RZ, I2))
    w.qed([a1(w, AB, ep, '( Z e. %s <-> ( Z e. CC /\\ %s e. ( A (,) B ) ) )' % (X, RZ)), e6], 'bitrd', STATEMENTS['z6melst'])
    return w


# ---------------------------------------------------------------- restriction of an entire z |-> ( V ^c z ) to an open set
def cxres(w, A0, vrp, V, uo, U):
    """( A0 -> HOLG( ( z e. U |-> ( FB ` ( z + 0 ) ) ), U ) ), FB = ( b e. CC |-> ( V ^c b ) ); returns (step, mapping, FB)"""
    s = mkst(w, A0)
    FZ = '( z e. CC |-> ( %s ^c z ) )' % V
    hz = s([vrp, w.inst('cxfhol')], 'syl', HOLG(FZ, 'CC'))
    c, FB = cbvm(w, A0, 'z', 'b', 'CC', '( %s ^c z )' % V)
    hb = holeq(w, A0, FZ, FB, 'CC', hz, c)
    Aw = '( %s /\\ w e. %s )' % (A0, U)
    t = mkst(w, Aw)
    uss = opnss(w, A0, uo, U)
    wc = t([lift(w, uss, Aw), w.s([], 'simpr', '( %s -> w e. %s )' % (Aw, U))], 'sseldd', 'w e. CC')
    w0 = t([wc, w.s([], '0cnd', '( %s -> 0 e. CC )' % Aw)], 'addcld', '( w + 0 ) e. CC')
    ral = s([w0], 'ralrimiva', 'A. w e. %s ( w + 0 ) e. CC' % U)
    ZS = '( z e. %s |-> ( %s ` ( z + 0 ) ) )' % (U, FB)
    sh = s([hb, s([uo, c1(w, A0, '0cn', '0 e. CC'), ral], '3jca', '( %s e. %s /\\ 0 e. CC /\\ A. w e. %s ( w + 0 ) e. CC )' % (U, TOP, U)), w.inst('z6hshift')],
           'syl2anc', HOLG(ZS, U))
    return sh, ZS, FB, uss


def zval(w, A0, uss, U, FB, V):
    """under Az = ( A0 /\\ z e. U ): ( Az -> ( FB ` ( z + 0 ) ) = ( V ^c z ) ), and z e. CC"""
    Az = '( %s /\\ z e. %s )' % (A0, U)
    t = mkst(w, Az)
    zc = t([lift(w, uss, Az), w.s([], 'simpr', '( %s -> z e. %s )' % (Az, U))], 'sseldd', 'z e. CC')
    z0c = t([zc, w.s([], '0cnd', '( %s -> 0 e. CC )' % Az)], 'addcld', '( z + 0 ) e. CC')
    v1, _ = mpval(w, Az, 'b', 'CC', '( %s ^c b )' % V, '( z + 0 )', z0c)
    v2 = t([t([zc], 'addridd', '( z + 0 ) = z')], 'oveq2d', '( %s ^c ( z + 0 ) ) = ( %s ^c z )' % (V, V))
    return t([v1, v2], 'eqtrd', '( %s ` ( z + 0 ) ) = ( %s ^c z )' % (FB, V)), zc, Az


# ---------------------------------------------------------------- z6mycxh
def z6mycxh():
    w = W('z6mycxh', 'The function ` w |-> Y ^ -u w ` is holomorphic on every open set: it is ` ( 1 / Y ) ^ w ` ( ~ divcxp , ~ cxpneg ), '
          'entire by ~ cxfhol , restricted by ~ z6hshift at ` N = 0 ` .')
    A0 = '( Y e. RR+ /\\ U e. %s )' % TOP
    s = mkst(w, A0)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A0)
    uo = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, TOP))
    V = '( 1 / Y )'
    iy = s([yrp], 'rpreccld', '%s e. RR+' % V)
    sh, ZS, FB, uss = cxres(w, A0, iy, V, uo, 'U')
    v, zc, Az = zval(w, A0, uss, 'U', FB, V)
    t = mkst(w, Az)
    yrpz = lift(w, yrp, Az)
    d1 = t([t([c1(w, Az, '1re', '1 e. RR'), c1(w, Az, '0le1', '0 <_ 1')], 'jca', '( 1 e. RR /\\ 0 <_ 1 )'), yrpz, zc, w.inst('divcxp')], 'syl3anc',
           '( %s ^c z ) = ( ( 1 ^c z ) / ( Y ^c z ) )' % V)
    d2 = t([t([zc, w.inst('1cxp')], 'syl', '( 1 ^c z ) = 1')], 'oveq1d', '( ( 1 ^c z ) / ( Y ^c z ) ) = ( 1 / ( Y ^c z ) )')
    yc = t([yrpz], 'rpcnd', 'Y e. CC'); yn = t([yrpz], 'rpne0d', 'Y =/= 0')
    d3 = t([yc, yn, zc, w.inst('cxpneg')], 'syl3anc', '( Y ^c -u z ) = ( 1 / ( Y ^c z ) )')
    ch = t([t([t([v, d1], 'eqtrd', '( %s ` ( z + 0 ) ) = ( ( 1 ^c z ) / ( Y ^c z ) )' % FB), d2], 'eqtrd', '( %s ` ( z + 0 ) ) = ( 1 / ( Y ^c z ) )' % FB), d3],
           'eqtr4d', '( %s ` ( z + 0 ) ) = ( Y ^c -u z )' % FB)
    mq = s([ch], 'mpteq2dva', '%s = ( z e. U |-> ( Y ^c -u z ) )' % ZS)
    c2, MW = cbvm(w, A0, 'z', 'w', 'U', '( Y ^c -u z )')
    eq = s([mq, c2], 'eqtrd', '%s = %s' % (ZS, MW))
    fin = holeq(w, A0, ZS, MW, 'U', sh, eq)
    toqed(w, fin, 'z6mycxh')
    return w


# ---------------------------------------------------------------- z6gyhol
def z6gyhol():
    w = W('z6gyhol', 'The Mellin integrand ` _G ( w ) Y ^ -u w ` is holomorphic on the domain of ` _G ` ( ~ z6gamhold , ~ z6mycxh , ~ holmul ).')
    A0 = 'Y e. RR+'
    s = mkst(w, A0)
    GD = '( z e. %s |-> ( _G ` z ) )' % DG
    g = c1(w, A0, 'z6gamhold', HOLG(GD, DG))
    c, GDb = cbvm(w, A0, 'z', 'b', DG, '( _G ` z )')
    gb = holeq(w, A0, GD, GDb, DG, g, c)
    MY = '( w e. %s |-> ( Y ^c -u w ) )' % DG
    hy = s([w.s([], 'id', '( Y e. RR+ -> Y e. RR+ )'), c1(w, A0, 'z6hdgopn', '%s e. %s' % (DG, TOP)), w.inst('z6mycxh')], 'syl2anc', HOLG(MY, DG))
    PM = '( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (DG, GDb, MY)
    hm = s([gb, hy, w.inst('holmul')], 'syl2anc', HOLG(PM, DG))
    Az = '( %s /\\ z e. %s )' % (A0, DG)
    t = mkst(w, Az)
    zm = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, DG))
    v1, _ = mpval(w, Az, 'b', DG, '( _G ` b )', 'z', zm)
    v2, _ = mpval(w, Az, 'w', DG, '( Y ^c -u w )', 'z', zm)
    v = t([v1, v2], 'oveq12d', '( ( %s ` z ) x. ( %s ` z ) ) = ( ( _G ` z ) x. ( Y ^c -u z ) )' % (GDb, MY))
    mq = s([v], 'mpteq2dva', '%s = ( z e. %s |-> ( ( _G ` z ) x. ( Y ^c -u z ) ) )' % (PM, DG))
    c2, G2 = cbvm(w, A0, 'z', 'w', DG, '( ( _G ` z ) x. ( Y ^c -u z ) )')
    assert G2 == GYM
    eq = s([mq, c2], 'eqtrd', '%s = %s' % (PM, GYM))
    fin = holeq(w, A0, PM, GYM, DG, hm, eq)
    toqed(w, fin, 'z6gyhol')
    return w


# ---------------------------------------------------------------- z6mrfhol
def z6mrfhol():
    w = W('z6mrfhol', 'The rising factorial ` w |-> ( w RiseFac K ) ` is holomorphic on every open set: induction on ` K ` '
          '( ~ risefac0 , ~ risefacp1 , ~ holmul ; the constant ` 1 = 1 ^ w ` by ~ cxfhol ).')
    PU = lambda n: '( U e. %s -> %s )' % (TOP, HOLG('( w e. U |-> ( w RiseFac %s ) )' % n, 'U'))

    def sb(T):
        idk = w.s([], 'id', '( n = %s -> n = %s )' % (T, T))
        stp, new = w.wcongr(PU('n'), {'n': T}, 'n = %s' % T, {'n': idk})
        assert new == PU(T), new
        return stp
    h1 = sb('0'); h2 = sb('m'); h3 = sb('( m + 1 )'); h4 = sb('K')
    # base
    A0 = 'U e. %s' % TOP
    s = mkst(w, A0)
    uo = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    sh, ZS, FB, uss = cxres(w, A0, c1(w, A0, '1rp', '1 e. RR+'), '1', uo, 'U')
    v, zc, Az = zval(w, A0, uss, 'U', FB, '1')
    t = mkst(w, Az)
    ch = t([t([v, t([zc, w.inst('1cxp')], 'syl', '( 1 ^c z ) = 1')], 'eqtrd', '( %s ` ( z + 0 ) ) = 1' % FB), t([zc, w.inst('risefac0')], 'syl', '( z RiseFac 0 ) = 1')],
           'eqtr4d', '( %s ` ( z + 0 ) ) = ( z RiseFac 0 )' % FB)
    mq = s([ch], 'mpteq2dva', '%s = ( z e. U |-> ( z RiseFac 0 ) )' % ZS)
    c2, MW = cbvm(w, A0, 'z', 'w', 'U', '( z RiseFac 0 )')
    base = holeq(w, A0, ZS, MW, 'U', sh, s([mq, c2], 'eqtrd', '%s = %s' % (ZS, MW)))
    # step
    A = '( ( m e. NN0 /\\ %s ) /\\ U e. %s )' % (PU('m'), TOP)
    s = mkst(w, A)
    mn = w.s([], 'simpll', '( %s -> m e. NN0 )' % A)
    uo = w.s([], 'simpr', '( %s -> U e. %s )' % (A, TOP))
    Fm = '( w e. U |-> ( w RiseFac m ) )'
    hm = s([uo, w.s([], 'simplr', '( %s -> %s )' % (A, PU('m')))], 'mpd', HOLG(Fm, 'U'))
    IZ = '( z e. CC |-> z )'
    hid = s([c1(w, A, 'cnopn', 'CC e. %s' % TOP), w.inst('z6hid')], 'syl', HOLG(IZ, 'CC'))
    c, IB = cbvm(w, A, 'z', 'b', 'CC', 'z')
    hib = holeq(w, A, IZ, IB, 'CC', hid, c)
    A2 = '( U e. %s /\\ m e. NN0 )' % TOP
    Aw = '( %s /\\ w e. U )' % A2
    tw = mkst(w, Aw)
    uss2 = opnss(w, A2, w.s([], 'simpl', '( %s -> U e. %s )' % (A2, TOP)), 'U')
    wc = tw([lift(w, uss2, Aw), w.s([], 'simpr', '( %s -> w e. U )' % Aw)], 'sseldd', 'w e. CC')
    mc2 = w.s([w.s([], 'simpr', '( %s -> m e. NN0 )' % A2)], 'nn0cnd', '( %s -> m e. CC )' % A2)
    ral2 = w.s([tw([wc, lift(w, mc2, Aw)], 'addcld', '( w + m ) e. CC')], 'ralrimiva', '( %s -> A. w e. U ( w + m ) e. CC )' % A2)
    ral = s([uo, mn, ral2], 'syl2anc', 'A. w e. U ( w + m ) e. CC')
    uss = opnss(w, A, uo, 'U')
    mc = s([mn], 'nn0cnd', 'm e. CC')
    ZS = '( z e. U |-> ( %s ` ( z + m ) ) )' % IB
    sh = s([hib, s([uo, mc, ral], '3jca', '( U e. %s /\\ m e. CC /\\ A. w e. U ( w + m ) e. CC )' % TOP), w.inst('z6hshift')], 'syl2anc', HOLG(ZS, 'U'))
    c3, ZSc = cbvm(w, A, 'z', 'c', 'U', '( %s ` ( z + m ) )' % IB)
    shc = holeq(w, A, ZS, ZSc, 'U', sh, c3)
    PM = '( z e. U |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (Fm, ZSc)
    hp = s([hm, shc, w.inst('holmul')], 'syl2anc', HOLG(PM, 'U'))
    Az = '( %s /\\ z e. U )' % A
    t = mkst(w, Az)
    zm = w.s([], 'simpr', '( %s -> z e. U )' % Az)
    zc = t([lift(w, uss, Az), zm], 'sseldd', 'z e. CC')
    mz = lift(w, mn, Az)
    v1, _ = mpval(w, Az, 'w', 'U', '( w RiseFac m )', 'z', zm)
    v2, _ = mpval(w, Az, 'c', 'U', '( %s ` ( c + m ) )' % IB, 'z', zm)
    zmc = t([zc, t([mz], 'nn0cnd', 'm e. CC')], 'addcld', '( z + m ) e. CC')
    v3, _ = mpval(w, Az, 'b', 'CC', 'b', '( z + m )', zmc)
    v23 = t([v2, v3], 'eqtrd', '( %s ` z ) = ( z + m )' % ZSc)
    v = t([v1, v23], 'oveq12d', '( ( %s ` z ) x. ( %s ` z ) ) = ( ( z RiseFac m ) x. ( z + m ) )' % (Fm, ZSc))
    rp = t([zc, mz, w.inst('risefacp1')], 'syl2anc', '( z RiseFac ( m + 1 ) ) = ( ( z RiseFac m ) x. ( z + m ) )')
    vv = t([v, rp], 'eqtr4d', '( ( %s ` z ) x. ( %s ` z ) ) = ( z RiseFac ( m + 1 ) )' % (Fm, ZSc))
    mq = s([vv], 'mpteq2dva', '%s = ( z e. U |-> ( z RiseFac ( m + 1 ) ) )' % PM)
    c4, MW = cbvm(w, A, 'z', 'w', 'U', '( z RiseFac ( m + 1 ) )')
    stp = holeq(w, A, PM, MW, 'U', hp, s([mq, c4], 'eqtrd', '%s = %s' % (PM, MW)))
    e1 = w.s([stp], 'ex', '( ( m e. NN0 /\\ %s ) -> %s )' % (PU('m'), PU('( m + 1 )')))
    e2 = w.s([e1], 'ex', '( m e. NN0 -> ( %s -> %s ) )' % (PU('m'), PU('( m + 1 )')))
    ind = w.s([h1, h2, h3, h4, base, e2], 'nn0ind', '( K e. NN0 -> %s )' % PU('K'))
    w.qed([ind], 'imp', STATEMENTS['z6mrfhol'])
    return w


# ---------------------------------------------------------------- z6mfhol
def z6mfhol():
    w = W('z6mfhol', 'The Cauchy numerator of ~ z6mstep , ` _G ( w + K + 1 ) Y ^ -u w / ( w RiseFac K ) ` , is holomorphic on the strip '
          '` -u K - 1 < Re w < 1 - K ` ( ~ z6gamhol , ~ z6hshift , ~ z6mycxh , ~ z6mrfhol , ~ holmul , ~ holdiv ; the rising factorial '
          'has no zero there, ~ fprodn0 ).')
    A0 = '( Y e. RR+ /\\ K e. NN0 )'
    s = mkst(w, A0)
    S = MSTRIP
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A0)
    kn = w.s([], 'simpr', '( %s -> K e. NN0 )' % A0)
    kr = s([kn], 'nn0red', 'K e. RR')
    so = c1(w, A0, 'z6mstopn', '%s e. %s' % (S, TOP))
    uss = opnss(w, A0, so, S)
    lo = s([s([kr], 'renegcld', '-u K e. RR'), c1(w, A0, '1re', '1 e. RR')], 'resubcld', '( -u K - 1 ) e. RR')
    hi = s([c1(w, A0, '1re', '1 e. RR'), kr], 'resubcld', '( 1 - K ) e. RR')
    lox = s([lo], 'rexrd', '( -u K - 1 ) e. RR*'); hix = s([hi], 'rexrd', '( 1 - K ) e. RR*')

    def inS(Aw, v):
        """( Aw -> ( v e. CC /\\ ( ( -u K - 1 ) < ( Re ` v ) /\\ ( Re ` v ) < ( 1 - K ) ) ) ) from ( Aw -> v e. S )"""
        vm = w.s([], 'simpr', '( %s -> %s e. %s )' % (Aw, v, S))
        bi = w.s([lift(w, lox, Aw), lift(w, hix, Aw), w.inst('z6melst')], 'syl2anc',
                 '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( ( -u K - 1 ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( 1 - K ) ) ) ) )' % (Aw, v, S, v, v, v))
        both = w.s([vm, bi], 'mpbid', '( %s -> ( %s e. CC /\\ ( ( -u K - 1 ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( 1 - K ) ) ) )' % (Aw, v, v, v))
        vc = w.s([both], 'simpld', '( %s -> %s e. CC )' % (Aw, v))
        l_ = w.s([both], 'simprld', '( %s -> ( -u K - 1 ) < ( Re ` %s ) )' % (Aw, v))
        h_ = w.s([both], 'simprrd', '( %s -> ( Re ` %s ) < ( 1 - K ) )' % (Aw, v))
        return vm, vc, l_, h_
    # w + ( K + 1 ) e. HPZ for w e. S
    K1 = '( K + 1 )'
    k1r = s([kr, c1(w, A0, '1re', '1 e. RR')], 'readdcld', '%s e. RR' % K1)

    def hpz(Aw, v, vc, l_):
        t = mkst(w, Aw)
        k1 = lift(w, k1r, Aw)
        sc = t([vc, t([k1], 'recnd', '%s e. CC' % K1)], 'addcld', '( %s + %s ) e. CC' % (v, K1))
        re = t([t([vc, t([k1], 'recnd', '%s e. CC' % K1)], 'readdd', '( Re ` ( %s + %s ) ) = ( ( Re ` %s ) + ( Re ` %s ) )' % (v, K1, v, K1)),
                t([t([k1], 'rered', '( Re ` %s ) = %s' % (K1, K1))], 'oveq2d', '( ( Re ` %s ) + ( Re ` %s ) ) = ( ( Re ` %s ) + %s )' % (v, K1, v, K1))],
               'eqtrd', '( Re ` ( %s + %s ) ) = ( ( Re ` %s ) + %s )' % (v, K1, v, K1))
        rv = t([vc], 'recld', '( Re ` %s ) e. RR' % v)
        gt = linarith(w, Aw, [l_], '0 < ( ( Re ` %s ) + %s )' % (v, K1), leaves={'( Re ` %s )' % v: rv, 'K': lift(w, kr, Aw)})
        gt2 = t([gt, re], 'breqtrrd', '0 < ( Re ` ( %s + %s ) )' % (v, K1))
        bi = t([c1(w, Aw, '0re', '0 e. RR'), w.inst('elhp2')], 'syl', '( ( %s + %s ) e. %s <-> ( ( %s + %s ) e. CC /\\ 0 < ( Re ` ( %s + %s ) ) ) )' % (v, K1, HPZ, v, K1, v, K1))
        return t([t([sc, gt2], 'jca', '( ( %s + %s ) e. CC /\\ 0 < ( Re ` ( %s + %s ) ) )' % (v, K1, v, K1)), bi], 'mpbird', '( %s + %s ) e. %s' % (v, K1, HPZ))
    Aw = '( %s /\\ w e. %s )' % (A0, S)
    _, wc, wl, _ = inS(Aw, 'w')
    ral = s([hpz(Aw, 'w', wc, wl)], 'ralrimiva', 'A. w e. %s ( w + %s ) e. %s' % (S, K1, HPZ))
    GZ = '( z e. %s |-> ( _G ` z ) )' % HPZ
    g = c1(w, A0, 'z6gamhol', HOLG(GZ, HPZ))
    c, GZa = cbvm(w, A0, 'z', 'a', HPZ, '( _G ` z )')
    ga = holeq(w, A0, GZ, GZa, HPZ, g, c)
    M1 = '( z e. %s |-> ( %s ` ( z + %s ) ) )' % (S, GZa, K1)
    h1 = s([ga, s([so, s([k1r], 'recnd', '%s e. CC' % K1), ral], '3jca', '( %s e. %s /\\ %s e. CC /\\ A. w e. %s ( w + %s ) e. %s )' % (S, TOP, K1, S, K1, HPZ)),
            w.inst('z6hshift')], 'syl2anc', HOLG(M1, S))
    c1_, M1b = cbvm(w, A0, 'z', 'b', S, '( %s ` ( z + %s ) )' % (GZa, K1))
    h1b = holeq(w, A0, M1, M1b, S, h1, c1_)
    M2 = '( w e. %s |-> ( Y ^c -u w ) )' % S
    h2 = s([yrp, so, w.inst('z6mycxh')], 'syl2anc', HOLG(M2, S))
    M12 = '( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (S, M1b, M2)
    h12 = s([h1b, h2, w.inst('holmul')], 'syl2anc', HOLG(M12, S))
    c2_, M12c = cbvm(w, A0, 'z', 'c', S, '( ( %s ` z ) x. ( %s ` z ) )' % (M1b, M2))
    h12c = holeq(w, A0, M12, M12c, S, h12, c2_)
    M3 = '( w e. %s |-> ( w RiseFac K ) )' % S
    h3 = s([kn, so, w.inst('z6mrfhol')], 'syl2anc', HOLG(M3, S))
    # the rising factorial has no zero on S
    Av = '( %s /\\ v e. %s )' % (A0, S)
    tv = mkst(w, Av)
    vm, vc, _, vh = inS(Av, 'v')
    knv = lift(w, kn, Av)
    mv3, _ = mpval(w, Av, 'w', S, '( w RiseFac K )', 'v', vm, exs=w.s([], 'ovexd', '( %s -> ( v RiseFac K ) e. _V )' % Av))
    rv = tv([vc, knv, w.inst('risefacval')], 'syl2anc', '( v RiseFac K ) = prod_ k e. ( 0 ... ( K - 1 ) ) ( v + k )')
    FZ_ = '( 0 ... ( K - 1 ) )'
    Ak = '( %s /\\ k e. %s )' % (Av, FZ_)
    tk = mkst(w, Ak)
    km = w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, FZ_))
    kz = tk([km], 'elfzelzd', 'k e. ZZ')
    krr = tk([kz], 'zred', 'k e. RR')
    kle = w.s([km, w.inst('elfzle2')], 'syl', '( %s -> k <_ ( K - 1 ) )' % Ak)
    vck = lift(w, vc, Ak)
    vk = tk([vck, tk([krr], 'recnd', 'k e. CC')], 'addcld', '( v + k ) e. CC')
    rvk = tk([tk([vck, tk([krr], 'recnd', 'k e. CC')], 'readdd', '( Re ` ( v + k ) ) = ( ( Re ` v ) + ( Re ` k ) )'),
              tk([tk([krr], 'rered', '( Re ` k ) = k')], 'oveq2d', '( ( Re ` v ) + ( Re ` k ) ) = ( ( Re ` v ) + k )')], 'eqtrd', '( Re ` ( v + k ) ) = ( ( Re ` v ) + k )')
    rvr = tk([vck], 'recld', '( Re ` v ) e. RR')
    neg = linarith(w, Ak, [lift(w, vh, Ak), kle], '( ( Re ` v ) + k ) < 0', leaves={'( Re ` v )': rvr, 'k': krr, 'K': lift(w, kr, Ak)})
    rne = tk([tk([rvk, neg], 'eqbrtrd', '( Re ` ( v + k ) ) < 0')], 'ltned', '( Re ` ( v + k ) ) =/= 0')
    # v + k = 0 -> Re = 0
    Ae = '( %s /\\ ( v + k ) = 0 )' % Ak
    te = mkst(w, Ae)
    r0 = te([te([w.s([], 'simpr', '( %s -> ( v + k ) = 0 )' % Ae)], 'fveq2d', '( Re ` ( v + k ) ) = ( Re ` 0 )'), c1(w, Ae, 're0', '( Re ` 0 ) = 0')], 'eqtrd',
            '( Re ` ( v + k ) ) = 0')
    ne_ = tk([rne], 'neneqd', '-. ( Re ` ( v + k ) ) = 0')
    vkn = w.s([r0, lift(w, ne_, Ae)], 'pm2.65da', '( %s -> -. ( v + k ) = 0 )' % Ak)
    vkne = tk([vkn], 'neqned', '( v + k ) =/= 0')
    pn = tv([c1(w, Av, 'fzfi', '%s e. Fin' % FZ_), vk, vkne], 'fprodn0', 'prod_ k e. %s ( v + k ) =/= 0' % FZ_)
    nz = tv([tv([mv3, rv], 'eqtrd', '( %s ` v ) = prod_ k e. %s ( v + k )' % (M3, FZ_)), pn], 'eqnetrd', '( %s ` v ) =/= 0' % M3)
    alnz = s([nz], 'ralrimiva', 'A. v e. %s ( %s ` v ) =/= 0' % (S, M3))
    M4 = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (S, M12c, M3)
    h4 = s([h12c, h3, alnz, w.inst('holdiv')], 'syl3anc', HOLG(M4, S))
    # the values
    Az = '( %s /\\ z e. %s )' % (A0, S)
    t = mkst(w, Az)
    zm, zc, zl, _ = inS(Az, 'z')
    z1 = hpz(Az, 'z', zc, zl)
    a1_, _ = mpval(w, Az, 'c', S, '( ( %s ` c ) x. ( %s ` c ) )' % (M1b, M2), 'z', zm)
    a2, _ = mpval(w, Az, 'b', S, '( %s ` ( b + %s ) )' % (GZa, K1), 'z', zm)
    a3, _ = mpval(w, Az, 'a', HPZ, '( _G ` a )', '( z + %s )' % K1, z1)
    a4, _ = mpval(w, Az, 'w', S, '( Y ^c -u w )', 'z', zm)
    a5, _ = mpval(w, Az, 'w', S, '( w RiseFac K )', 'z', zm, exs=w.s([], 'ovexd', '( %s -> ( z RiseFac K ) e. _V )' % Az))
    GK = '( _G ` ( z + %s ) )' % K1
    a23 = t([a2, a3], 'eqtrd', '( %s ` z ) = %s' % (M1b, GK))
    num_ = t([a1_, t([a23, a4], 'oveq12d', '( ( %s ` z ) x. ( %s ` z ) ) = ( %s x. ( Y ^c -u z ) )' % (M1b, M2, GK))], 'eqtrd',
             '( %s ` z ) = ( %s x. ( Y ^c -u z ) )' % (M12c, GK))
    q = t([num_, a5], 'oveq12d', '( ( %s ` z ) / ( %s ` z ) ) = ( ( %s x. ( Y ^c -u z ) ) / ( z RiseFac K ) )' % (M12c, M3, GK))
    BODY = '( ( %s x. ( Y ^c -u z ) ) / ( z RiseFac K ) )' % GK
    mq = s([q], 'mpteq2dva', '%s = ( z e. %s |-> %s )' % (M4, S, BODY))
    c5, F0 = cbvm(w, A0, 'z', 'w', S, BODY)
    assert F0 == MF0, F0
    fin = holeq(w, A0, M4, F0, S, h4, s([mq, c5], 'eqtrd', '%s = %s' % (M4, F0)))
    toqed(w, fin, 'z6mfhol')
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6mstopn, z6melst, z6mycxh, z6gyhol, z6mrfhol, z6mfhol]:
        if want(f.__name__):
            if run(f()):
                status(f.__name__)
            else:
                break
