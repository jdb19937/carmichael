"""Sortie Z6a, block C: convergence of the vertical line integrals (z6segd, z6e4lim, z6half,
z6kalg, z6vltail, z6vlex, z6vlt, z6vlcvg)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z6alib import *
from cl import Closure, lift, split_imp, formula_of
import lin
from lin import linarith, lineq, nlinarith
import num

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'
SA = '( C + ( _i x. -u T ) )'
SB = '( C + ( _i x. T ) )'
SEG = '( %s cseg %s )' % (SA, SB)
DT = '( T - -u T )'
L2 = '( log ` 2 )'


def want(lab):
    return not only or lab in only


def ante_of(lab):
    return split_imp(STATEMENTS[lab])[0]


def segs(T):
    return '( C + ( _i x. -u %s ) )' % T, '( C + ( _i x. %s ) )' % T


# ---------------------------------------------------------------- z6segd
def z6segd():
    w = W('z6segd', 'The vertical segment from ` C - i T ` to ` C + i T ` lies in any ` D ` containing the vertical '
          'line ` Re = C ` ( ~ csegel , ~ z6segl ).')
    A = ante_of('z6segd')
    st = mkst(w, A)
    cr = st([], 'simpll', 'C e. RR'); trp = st([], 'simplr', 'T e. RR+'); al = st([], 'simpr', 'A. u e. RR ( C + ( _i x. u ) ) e. D')
    cl = Closure(w, A, {'C': ('RR', cr), 'T': ('RR+', trp)})
    tr = cl.mem('T', 'RR')
    cc = st([cr], 'recnd', 'C e. CC'); tc = st([tr], 'recnd', 'T e. CC'); ic = a1c(w, A, 'ax-icn', '_i e. CC')
    sac = st([cc, st([ic, st([tc], 'negcld', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % SA)
    sbc = st([cc, st([ic, tc], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SB)
    L = lambda t: '( %s + ( %s x. ( %s - %s ) ) )' % (SA, t, SB, SA)
    Az = '( %s /\\ z e. %s )' % (A, SEG)
    sz = mkst(w, Az)
    ex = sz([sz([], 'simpr', 'z e. %s' % SEG), sz([lift(w, sac, Az), lift(w, sbc, Az), w.inst('csegel')], 'syl2anc', '( z e. %s <-> E. t e. ( 0 [,] 1 ) z = %s )' % (SEG, L('t')))],
            'mpbid', 'E. t e. ( 0 [,] 1 ) z = %s' % L('t'))
    At = '( %s /\\ t e. ( 0 [,] 1 ) )' % Az
    s2 = mkst(w, At)
    t01 = s2([], 'simpr', 't e. ( 0 [,] 1 )')
    trr = s2([t01, w.inst('elunitrn')], 'syl', 't e. RR')
    sl = s2([s2([lift(w, cc, At), lift(w, tc, At), s2([trr], 'recnd', 't e. CC')], '3jca', '( C e. CC /\\ T e. CC /\\ t e. CC )'), w.inst('z6segl')], 'syl',
            '( %s = ( C + ( _i x. ( -u T + ( t x. %s ) ) ) ) /\\ ( %s - %s ) = ( _i x. %s ) )' % (L('t'), DT, SB, SA, DT))
    e1 = s2([sl], 'simpld', '%s = ( C + ( _i x. ( -u T + ( t x. %s ) ) ) )' % (L('t'), DT))
    R = '( -u T + ( t x. %s ) )' % DT
    clt = Closure(w, At, {'T': ('RR', lift(w, tr, At)), 't': ('RR', trr)})
    rr = clt.mem(R, 'RR')
    sb = w.s([w.s([w.s([], 'oveq2', '( u = %s -> ( _i x. u ) = ( _i x. %s ) )' % (R, R))], 'oveq2d', '( u = %s -> ( C + ( _i x. u ) ) = ( C + ( _i x. %s ) ) )' % (R, R))], 'eleq1d',
             '( u = %s -> ( ( C + ( _i x. u ) ) e. D <-> ( C + ( _i x. %s ) ) e. D ) )' % (R, R))
    rs = w.s([sb], 'rspcv', '( %s e. RR -> ( A. u e. RR ( C + ( _i x. u ) ) e. D -> ( C + ( _i x. %s ) ) e. D ) )' % (R, R))
    rd = s2([rr, lift(w, al, At), rs], 'sylc', '( C + ( _i x. %s ) ) e. D' % R)
    ld = s2([e1, rd], 'eqeltrd', '%s e. D' % L('t'))
    imp = s2([ld, w.inst('eleq1a')], 'syl', '( z = %s -> z e. D )' % L('t'))
    zd = sz([ex, sz([imp], 'rexlimdva', '( E. t e. ( 0 [,] 1 ) z = %s -> z e. D )' % L('t'))], 'mpd', 'z e. D')
    w.qed([w.s([zd], 'ex', '( %s -> ( z e. %s -> z e. D ) )' % (A, SEG))], 'ssrdv', STATEMENTS['z6segd'])
    return w


# ---------------------------------------------------------------- z6e4lim
def z6e4lim():
    w = W('z6e4lim', 'The exponential ` 2 ^ ( - t / 4 ) ` tends to ` 0 ` ( ~ cxp2lim at the base ` 2 ^ ( 1 / 4 ) > 1 ` ).')
    Q = '( 2 ^c ( 1 / 4 ) )'
    fr = w.s([], '1re', '1 e. RR')
    q4 = num.real(w, '( 1 / 4 )')
    qr = w.s([w.s([], '2rp', '2 e. RR+'), q4, w.inst('rpcxpcl')], 'mp2an', '%s e. RR+' % Q) if False else None
    two = w.s([], '2rp', '2 e. RR+')
    qrp = w.s([two, q4, w.inst('rpcxpcl')], 'mp2an', '%s e. RR+' % Q)
    qre = w.s([qrp, w.inst('rpre')], 'ax-mp', '%s e. RR' % Q)
    lt0 = num.le_lit(w, '0', '( 1 / 4 )', strict=True)
    c1 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2')], 'pm3.2i', '( 2 e. RR /\\ 1 < 2 )'), w.s([w.s([], '0re', '0 e. RR'), q4], 'pm3.2i', '( 0 e. RR /\\ ( 1 / 4 ) e. RR )'),
              w.inst('cxplt')], 'mp2an', '( 0 < ( 1 / 4 ) <-> ( 2 ^c 0 ) < %s )' % Q)
    c2 = w.s([lt0, c1], 'mpbi', '( 2 ^c 0 ) < %s' % Q)
    c3 = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.inst('cxp0')], 'ax-mp', '( 2 ^c 0 ) = 1'), c2], 'eqbrtrri', '1 < %s' % Q)
    lim = w.s([w.s([], '0re', '0 e. RR'), qre, c3, w.inst('cxp2lim')], 'mp3an', '( t e. RR+ |-> ( ( t ^c 0 ) / ( %s ^c t ) ) ) ~~>r 0' % Q)
    A = 't e. RR+'
    st = mkst(w, A)
    trp = st([], 'id', 't e. RR+')
    tc = st([trp], 'rpcnd', 't e. CC'); tr = st([trp], 'rpred', 't e. RR')
    e0 = st([tc], 'cxp0d', '( t ^c 0 ) = 1')
    em = st([a1c(w, A, '2rp', '2 e. RR+'), a1(w, A, q4, '( 1 / 4 ) e. RR'), tc], 'cxpmuld', '( 2 ^c ( ( 1 / 4 ) x. t ) ) = ( %s ^c t )' % Q)
    lq = lineq(w, A, '( ( 1 / 4 ) x. t )', '( t / 4 )', leaves={'t': tr})
    em2 = st([st([lq], 'oveq2d', '( 2 ^c ( ( 1 / 4 ) x. t ) ) = ( 2 ^c ( t / 4 ) )'), em], 'eqtr3d', '( 2 ^c ( t / 4 ) ) = ( %s ^c t )' % Q)
    en = st([a1c(w, A, '2cn', '2 e. CC'), a1c(w, A, '2ne0', '2 =/= 0'), st([tc, a1c(w, A, '4cn', '4 e. CC'), a1c(w, A, '4ne0', '4 =/= 0')], 'divcld', '( t / 4 ) e. CC')], 'cxpnegd',
            '( 2 ^c -u ( t / 4 ) ) = ( 1 / ( 2 ^c ( t / 4 ) ) )')
    val = st([st([e0, st([em2], 'eqcomd', '( %s ^c t ) = ( 2 ^c ( t / 4 ) )' % Q)], 'oveq12d', '( ( t ^c 0 ) / ( %s ^c t ) ) = ( 1 / ( 2 ^c ( t / 4 ) ) )' % Q), en], 'eqtr4d',
             '( ( t ^c 0 ) / ( %s ^c t ) ) = ( 2 ^c -u ( t / 4 ) )' % Q)
    meq = w.s([val], 'mpteq2ia', '( t e. RR+ |-> ( ( t ^c 0 ) / ( %s ^c t ) ) ) = ( t e. RR+ |-> ( 2 ^c -u ( t / 4 ) ) )' % Q)
    w.qed([meq, lim], 'eqbrtrri', STATEMENTS['z6e4lim'])
    return w


# ---------------------------------------------------------------- z6half
def z6half():
    w = W('z6half', 'One tail of a line integral against the exponential majorant ` M 2 ^ ( K v ) ` : '
          '` | S. ( A , B ) F | <_ M ( 2 ^ ( K B ) - 2 ^ ( K A ) ) / ( K log 2 ) ` ( ~ itgabs , ~ itgle , ~ cxpaffitg2 ).')
    h = hyps_of(w, 'z6half')
    P = 'ph'
    st = mkst(w, P)
    h1, h2, h3, h4, h5, h6 = h
    ar = st([st([h1], 'simpld', '( A e. RR /\\ B e. RR )')], 'simpld', 'A e. RR'); br = st([st([h1], 'simpld', '( A e. RR /\\ B e. RR )')], 'simprd', 'B e. RR')
    ale = st([h1], 'simprd', 'A <_ B')
    kr = st([h2], 'simpld', 'K e. RR'); kne = st([h2], 'simprd', 'K =/= 0')
    AB = '( A (,) B )'
    ai = st([h4, h5], 'itgabs', '( abs ` S. %s F _d v ) <_ S. %s ( abs ` F ) _d v' % (AB, AB))
    fai = st([h4, h5], 'iblabs', '( v e. %s |-> ( abs ` F ) ) e. L^1' % AB)
    E = '( 2 ^c ( K x. v ) )'
    cx = st([st([a1c(w, P, '2rp', '2 e. RR+'), st([kr, st([ar, br], 'jca', '( A e. RR /\\ B e. RR )')], 'jca', '( K e. RR /\\ ( A e. RR /\\ B e. RR ) )')], 'jca',
                '( 2 e. RR+ /\\ ( K e. RR /\\ ( A e. RR /\\ B e. RR ) ) )'), w.inst('cxpaffibl2')], 'syl',
            '( ( v e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ ( v e. %s |-> %s ) e. L^1 )' % (AB, E, AB, AB, E))
    eibl = st([cx], 'simprd', '( v e. %s |-> %s ) e. L^1' % (AB, E))
    Av = '( ph /\\ v e. %s )' % AB
    sv = mkst(w, Av)
    vr = sv([sv([], 'simpr', 'v e. %s' % AB), w.inst('elioore')], 'syl', 'v e. RR')
    erp = sv([sv([], '2rpd' if False else 'simpr', 'v e. %s' % AB) if False else lift(w, a1c(w, P, '2rp', '2 e. RR+'), Av), sv([lift(w, kr, Av), vr], 'remulcld', '( K x. v ) e. RR')], 'rpcxpcld', '%s e. RR+' % E)
    er = sv([erp], 'rpred', '%s e. RR' % E)
    mc = st([h3], 'recnd', 'M e. CC')
    mibl = st([mc, sv([er], 'recnd', '%s e. CC' % E), eibl], 'iblmulc2', '( v e. %s |-> ( M x. %s ) ) e. L^1' % (AB, E))
    far = sv([h4], 'abscld', '( abs ` F ) e. RR')
    mer = sv([lift(w, h3, Av), er], 'remulcld', '( M x. %s ) e. RR' % E)
    il = st([fai, mibl, far, mer, h6], 'itgle', 'S. %s ( abs ` F ) _d v <_ S. %s ( M x. %s ) _d v' % (AB, AB, E))
    im = st([mc, sv([er], 'recnd', '%s e. CC' % E), eibl], 'itgmulc2', '( M x. S. %s %s _d v ) = S. %s ( M x. %s ) _d v' % (AB, E, AB, E))
    VAL = '( ( ( 2 ^c ( K x. B ) ) - ( 2 ^c ( K x. A ) ) ) / ( K x. %s ) )' % L2
    ic = st([st([a1c(w, P, '2rp', '2 e. RR+'), a1(w, P, w.s([w.s([], '1ne2', '1 =/= 2')], 'necomi', '2 =/= 1'), '2 =/= 1')], 'jca', '( 2 e. RR+ /\\ 2 =/= 1 )'),
             st([st([kr, kne], 'jca', '( K e. RR /\\ K =/= 0 )'), st([ar, br, ale], '3jca', '( A e. RR /\\ B e. RR /\\ A <_ B )')], 'jca',
                '( ( K e. RR /\\ K =/= 0 ) /\\ ( A e. RR /\\ B e. RR /\\ A <_ B ) )'), w.inst('cxpaffitg2')], 'syl2anc', 'S. %s %s _d v = %s' % (AB, E, VAL))
    t1 = st([il, im], 'breqtrrd', 'S. %s ( abs ` F ) _d v <_ ( M x. S. %s %s _d v )' % (AB, AB, E))
    t2 = st([t1, st([ic], 'oveq2d', '( M x. S. %s %s _d v ) = ( M x. %s )' % (AB, E, VAL))], 'breqtrd', 'S. %s ( abs ` F ) _d v <_ ( M x. %s )' % (AB, VAL))
    icr = st([st([h4, h5], 'itgcl', 'S. %s F _d v e. CC' % AB)], 'abscld', '( abs ` S. %s F _d v ) e. RR' % AB)
    iar = st([far, fai], 'itgrecl', 'S. %s ( abs ` F ) _d v e. RR' % AB)
    vr_ = st([st([st([er, eibl], 'itgrecl', 'S. %s %s _d v e. RR' % (AB, E)), ic], 'eqeltrrd', '%s e. RR' % VAL) if False else
              st([ic, st([er, eibl], 'itgrecl', 'S. %s %s _d v e. RR' % (AB, E))], 'eqeltrrd', '%s e. RR' % VAL), h3], 'jca', '( %s e. RR /\\ M e. RR )' % VAL) if False else None
    valr = st([ic, st([er, eibl], 'itgrecl', 'S. %s %s _d v e. RR' % (AB, E))], 'eqeltrrd', '%s e. RR' % VAL)
    rhs = st([h3, valr], 'remulcld', '( M x. %s ) e. RR' % VAL)
    w.qed([icr, iar, rhs, ai, t2], 'letrd', '( ph -> ( abs ` S. %s F _d v ) <_ ( M x. %s ) )' % (AB, VAL))
    return w


# ---------------------------------------------------------------- z6kalg
def l2rp(w, A):
    st = mkst(w, A)
    lr = st([a1c(w, A, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '%s e. RR' % L2)
    gt = linarith(w, A, [a1c(w, A, 'log2ge', '( 1 / 2 ) <_ %s' % L2)], '0 < %s' % L2, leaves={L2: lr})
    return st([lr, gt], 'elrpd', '%s e. RR+' % L2)


def z6kalg():
    w = W('z6kalg', 'The two tails of ~ z6vltail add up: ` M V1 + M V2 = ( 8 M / log 2 ) ( 2 ^ ( - P / 4 ) - 2 ^ ( - Q / 4 ) ) ` '
          'for the values ` V1 ` , ` V2 ` of ~ cxpaffitg2 at the slopes ` 1 / 4 ` and ` -u ( 1 / 4 ) ` .')
    A = ante_of('z6kalg')
    st = mkst(w, A)
    mr = st([], 'simpl', 'M e. RR'); pr = st([], 'simprl', 'P e. RR'); qr = st([], 'simprr', 'Q e. RR')
    lrp = l2rp(w, A)
    lc = st([lrp], 'rpcnd', '%s e. CC' % L2); lne = st([lrp], 'rpne0d', '%s =/= 0' % L2)
    e1 = E4('P'); e2 = E4('Q')
    cl0 = Closure(w, A, {'P': ('RR', pr), 'Q': ('RR', qr), 'M': ('RR', mr)})
    e1r = st([a1c(w, A, '2rp', '2 e. RR+'), cl0.mem('-u ( P / 4 )', 'RR')], 'rpcxpcld', '%s e. RR+' % e1)
    e2r = st([a1c(w, A, '2rp', '2 e. RR+'), cl0.mem('-u ( Q / 4 )', 'RR')], 'rpcxpcld', '%s e. RR+' % e2)

    def ex(x, y):
        q = lineq(w, A, x, y, closure=cl0)
        return q
    x1 = st([ex('( ( 1 / 4 ) x. -u P )', '-u ( P / 4 )')], 'oveq2d', '( 2 ^c ( ( 1 / 4 ) x. -u P ) ) = %s' % e1)
    x2 = st([ex('( ( 1 / 4 ) x. -u Q )', '-u ( Q / 4 )')], 'oveq2d', '( 2 ^c ( ( 1 / 4 ) x. -u Q ) ) = %s' % e2)
    x3 = st([ex('( -u ( 1 / 4 ) x. Q )', '-u ( Q / 4 )')], 'oveq2d', '( 2 ^c ( -u ( 1 / 4 ) x. Q ) ) = %s' % e2)
    x4 = st([ex('( -u ( 1 / 4 ) x. P )', '-u ( P / 4 )')], 'oveq2d', '( 2 ^c ( -u ( 1 / 4 ) x. P ) ) = %s' % e1)
    C1 = '( ( 1 / 4 ) x. %s )' % L2; C2 = '( -u ( 1 / 4 ) x. %s )' % L2
    D12 = '( %s - %s )' % (e1, e2); D21 = '( %s - %s )' % (e2, e1)
    V1 = '( ( ( 2 ^c ( ( 1 / 4 ) x. -u P ) ) - ( 2 ^c ( ( 1 / 4 ) x. -u Q ) ) ) / %s )' % C1
    V2 = '( ( ( 2 ^c ( -u ( 1 / 4 ) x. Q ) ) - ( 2 ^c ( -u ( 1 / 4 ) x. P ) ) ) / %s )' % C2
    r1 = st([st([x1, x2], 'oveq12d', '( ( 2 ^c ( ( 1 / 4 ) x. -u P ) ) - ( 2 ^c ( ( 1 / 4 ) x. -u Q ) ) ) = %s' % D12)], 'oveq1d', '%s = ( %s / %s )' % (V1, D12, C1))
    r2 = st([st([x3, x4], 'oveq12d', '( ( 2 ^c ( -u ( 1 / 4 ) x. Q ) ) - ( 2 ^c ( -u ( 1 / 4 ) x. P ) ) ) = %s' % D21)], 'oveq1d', '%s = ( %s / %s )' % (V2, D21, C2))
    Z = '( %s / %s )' % (D12, L2)
    e1c = st([e1r], 'rpcnd', '%s e. CC' % e1); e2c = st([e2r], 'rpcnd', '%s e. CC' % e2)
    d12c = st([e1c, e2c], 'subcld', '%s e. CC' % D12); d21c = st([e2c, e1c], 'subcld', '%s e. CC' % D21)
    zl = st([d12c, lc, lne], 'divcan1d', '( %s x. %s ) = %s' % (Z, L2, D12))
    zr = st([st([e1r], 'rpred', '%s e. RR' % e1) and st([st([e1r], 'rpred', '%s e. RR' % e1), st([e2r], 'rpred', '%s e. RR' % e2)], 'resubcld', '%s e. RR' % D12), lrp], 'rerpdivcld', '%s e. RR' % Z)
    cl = Closure(w, A, {'P': ('RR', pr), 'Q': ('RR', qr), 'M': ('RR', mr)})
    cl.leaf(e1, 'RR', st([e1r], 'rpred', '%s e. RR' % e1)); cl.leaf(e2, 'RR', st([e2r], 'rpred', '%s e. RR' % e2))
    cl.leaf(L2, 'RR+', lrp); cl.leaf(Z, 'RR', zr)
    q4 = cl.mem('( 1 / 4 )', 'CC')
    c1c = st([q4, lc], 'mulcld', '%s e. CC' % C1); c1n = st([q4, cl.ne0('( 1 / 4 )'), lc, lne], 'mulne0d', '%s =/= 0' % C1) if False else \
        st([q4, lc, cl.ne0('( 1 / 4 )'), lne], 'mulne0d', '%s =/= 0' % C1)
    nq4 = cl.mem('-u ( 1 / 4 )', 'CC')
    c2c = st([nq4, lc], 'mulcld', '%s e. CC' % C2)
    c2n = st([nq4, lc, st([q4, cl.ne0('( 1 / 4 )')], 'negne0d', '-u ( 1 / 4 ) =/= 0'), lne], 'mulne0d', '%s =/= 0' % C2)
    Z4 = '( 4 x. %s )' % Z
    z4c = st([a1c(w, A, '4cn', '4 e. CC'), st([zr], 'recnd', '%s e. CC' % Z)], 'mulcld', '%s e. CC' % Z4)
    q1 = lineq(w, A, D12, '( %s x. %s )' % (Z4, C1), hyps=[zl], closure=cl, products=True)
    v1 = st([q1, st([d12c, z4c, c1c, c1n], 'divmul3d', '( ( %s / %s ) = %s <-> %s = ( %s x. %s ) )' % (D12, C1, Z4, D12, Z4, C1))], 'mpbird', '( %s / %s ) = %s' % (D12, C1, Z4))
    q2 = lineq(w, A, D21, '( %s x. %s )' % (Z4, C2), hyps=[zl], closure=cl, products=True)
    v2 = st([q2, st([d21c, z4c, c2c, c2n], 'divmul3d', '( ( %s / %s ) = %s <-> %s = ( %s x. %s ) )' % (D21, C2, Z4, D21, Z4, C2))], 'mpbird', '( %s / %s ) = %s' % (D21, C2, Z4))
    w1 = st([r1, v1], 'eqtrd', '%s = %s' % (V1, Z4)); w2 = st([r2, v2], 'eqtrd', '%s = %s' % (V2, Z4))
    lhs = st([st([w1], 'oveq2d', '( M x. %s ) = ( M x. %s )' % (V1, Z4)), st([w2], 'oveq2d', '( M x. %s ) = ( M x. %s )' % (V2, Z4))], 'oveq12d',
             '( ( M x. %s ) + ( M x. %s ) ) = ( ( M x. %s ) + ( M x. %s ) )' % (V1, V2, Z4, Z4))
    K8 = '( ( 8 x. M ) / %s )' % L2
    m8c = st([a1c(w, A, '8cn', '8 e. CC'), st([mr], 'recnd', 'M e. CC')], 'mulcld', '( 8 x. M ) e. CC')
    rhs = st([m8c, lc, d12c, lne], 'div32d', '( %s x. %s ) = ( ( 8 x. M ) x. %s )' % (K8, D12, Z))
    mid = lineq(w, A, '( ( M x. %s ) + ( M x. %s ) )' % (Z4, Z4), '( ( 8 x. M ) x. %s )' % Z, closure=cl, products=True)
    w.qed([st([lhs, mid], 'eqtrd', '( ( M x. %s ) + ( M x. %s ) ) = ( ( 8 x. M ) x. %s )' % (V1, V2, Z)), rhs], 'eqtr4d',
          '( %s -> ( ( M x. %s ) + ( M x. %s ) ) = ( %s x. %s ) )' % (A, V1, V2, K8, D12))
    return w


# ---------------------------------------------------------------- z6vltail
def hvparts(w, A, hv):
    """the conjuncts of z6vlcvg's antecedent from hv: ( A -> HV )"""
    st = mkst(w, A)
    d = {}
    l = st([hv], 'simpld', '( C e. RR /\\ ( G e. ( D -cn-> CC ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. D ) )')
    r = st([hv], 'simprd', '( ( M e. RR /\\ Y e. RR+ ) /\\ %s )' % BNDU)
    d['cr'] = st([l], 'simpld', 'C e. RR')
    g2 = st([l], 'simprd', '( G e. ( D -cn-> CC ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. D )')
    d['gcn'] = st([g2], 'simpld', 'G e. ( D -cn-> CC )')
    d['al'] = st([g2], 'simprd', 'A. u e. RR ( C + ( _i x. u ) ) e. D')
    my = st([r], 'simpld', '( M e. RR /\\ Y e. RR+ )')
    d['mr'] = st([my], 'simpld', 'M e. RR'); d['yrp'] = st([my], 'simprd', 'Y e. RR+')
    d['bnd'] = st([r], 'simprd', BNDU)
    return d


BNDU = 'A. u e. RR ( Y <_ ( abs ` u ) -> ( abs ` ( G ` ( C + ( _i x. u ) ) ) ) <_ ( M x. %s ) )' % E4('( abs ` u )')
GV = '( G ` ( C + ( _i x. v ) ) )'


def bndat(w, A, d, X, xr):
    """( A -> ( Y <_ ( abs ` X ) -> ( abs ` ( G ` ( C + ( _i x. X ) ) ) ) <_ ( M x. E4 ( abs ` X ) ) ) ) for a real X"""
    body = '( Y <_ ( abs ` u ) -> ( abs ` ( G ` ( C + ( _i x. u ) ) ) ) <_ ( M x. %s ) )' % E4('( abs ` u )')
    idk = w.s([], 'id', '( u = %s -> u = %s )' % (X, X))
    sb, new = w.wcongr(body, {'u': X}, 'u = %s' % X, {'u': idk})
    rs = w.s([sb], 'rspcv', '( %s e. RR -> ( %s -> %s ) )' % (X, BNDU, new))
    return w.s([xr, lift(w, d['bnd'], A), rs], 'sylc', '( %s -> %s )' % (A, new)), new


def gcl(w, A, d, X, xr):
    """( A -> ( G ` ( C + ( _i x. X ) ) ) e. CC )"""
    sb = w.s([w.s([w.s([], 'oveq2', '( u = %s -> ( _i x. u ) = ( _i x. %s ) )' % (X, X))], 'oveq2d', '( u = %s -> ( C + ( _i x. u ) ) = ( C + ( _i x. %s ) ) )' % (X, X))], 'eleq1d',
             '( u = %s -> ( ( C + ( _i x. u ) ) e. D <-> ( C + ( _i x. %s ) ) e. D ) )' % (X, X))
    rs = w.s([sb], 'rspcv', '( %s e. RR -> ( A. u e. RR ( C + ( _i x. u ) ) e. D -> ( C + ( _i x. %s ) ) e. D ) )' % (X, X))
    xd = w.s([xr, lift(w, d['al'], A), rs], 'sylc', '( %s -> ( C + ( _i x. %s ) ) e. D )' % (A, X))
    gf = w.s([lift(w, d['gcn'], A), w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A)
    return w.s([gf, xd], 'ffvelcdmd', '( %s -> ( G ` ( C + ( _i x. %s ) ) ) e. CC )' % (A, X))


def z6vltail():
    w = W('z6vltail', 'The Cauchy tail of the truncated vertical line integrals: for ` Y <_ P <_ Q ` , '
          '` | LI ( Q ) - LI ( P ) | <_ ( 8 M / log 2 ) 2 ^ ( - P / 4 ) ` ( ~ z6lvert , ~ itgsplitioo , ~ z6half on '
          'both tails, ~ z6kalg ).')
    A = ante_of('z6vltail')
    st = mkst(w, A)
    HVt = split_imp(STATEMENTS['z6vlcvg'])[0]
    hv = st([], 'simpl', HVt)
    d = hvparts(w, A, hv)
    pq = st([], 'simpr', '( ( P e. RR /\\ Q e. RR ) /\\ ( Y <_ P /\\ P <_ Q ) )')
    pr = st([st([pq], 'simpld', '( P e. RR /\\ Q e. RR )')], 'simpld', 'P e. RR'); qr = st([st([pq], 'simpld', '( P e. RR /\\ Q e. RR )')], 'simprd', 'Q e. RR')
    yp = st([st([pq], 'simprd', '( Y <_ P /\\ P <_ Q )')], 'simpld', 'Y <_ P'); pqle = st([st([pq], 'simprd', '( Y <_ P /\\ P <_ Q )')], 'simprd', 'P <_ Q')
    cl = Closure(w, A, {'P': ('RR', pr), 'Q': ('RR', qr), 'Y': ('RR+', d['yrp']), 'M': ('RR', d['mr']), 'C': ('RR', d['cr'])})
    ppos = linarith(w, A, [yp, cl.gt0('Y')], '0 < P', closure=cl)
    qpos = linarith(w, A, [yp, pqle, cl.gt0('Y')], '0 < Q', closure=cl)
    prp = st([pr, ppos], 'elrpd', 'P e. RR+'); qrp = st([qr, qpos], 'elrpd', 'Q e. RR+')
    crd = d['cr']
    segP = st([st([st([crd, prp], 'jca', '( C e. RR /\\ P e. RR+ )'), d['al']], 'jca', '( ( C e. RR /\\ P e. RR+ ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. D )'), w.inst('z6segd')], 'syl',
              '( %s cseg %s ) C_ D' % segs('P'))
    segQ = st([st([st([crd, qrp], 'jca', '( C e. RR /\\ Q e. RR+ )'), d['al']], 'jca', '( ( C e. RR /\\ Q e. RR+ ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. D )'), w.inst('z6segd')], 'syl',
              '( %s cseg %s ) C_ D' % segs('Q'))

    def lv(T, trp, seg):
        IT = 'S. ( -u %s (,) %s ) %s _d v' % (T, T, GV)
        f = st([st([st([crd, trp], 'jca', '( C e. RR /\\ %s e. RR+ )' % T), st([d['gcn'], seg], 'jca', '( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % segs(T))], 'jca',
                   '( ( C e. RR /\\ %s e. RR+ ) /\\ ( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % ((T,) + segs(T))), w.inst('z6lvert')], 'syl',
               '( ( v e. ( -u %s (,) %s ) |-> %s ) e. L^1 /\\ %s = ( _i x. %s ) )' % (T, T, GV, LI('G', 'C', T), IT))
        return st([f], 'simpld', '( v e. ( -u %s (,) %s ) |-> %s ) e. L^1' % (T, T, GV)), st([f], 'simprd', '%s = ( _i x. %s )' % (LI('G', 'C', T), IT)), IT
    iblP, eqP, IP = lv('P', prp, segP)
    iblQ, eqQ, IQ = lv('Q', qrp, segQ)
    NP = '-u P'; NQ = '-u Q'
    npr = cl.mem(NP, 'RR'); nqr = cl.mem(NQ, 'RR')
    xr = lambda E, s: st([s], 'rexrd', '%s e. RR*' % E)

    def ccunder(I):
        Av = '( %s /\\ v e. %s )' % (A, I)
        vr = w.s([w.s([], 'simpr', '( %s -> v e. %s )' % (Av, I)), w.inst('elioore')], 'syl', '( %s -> v e. RR )' % Av)
        return gcl(w, Av, d, 'v', vr), Av, vr
    IQQ = '( %s (,) Q )' % NQ
    ccQ, _, _ = ccunder(IQQ)

    def sub_ibl(lo, hi, lostep, histep):
        ss = st([st([xr(NQ, nqr), xr('Q', qr)], 'jca', '( %s e. RR* /\\ Q e. RR* )' % NQ), st([lostep, histep], 'jca', '( %s <_ %s /\\ %s <_ Q )' % (NQ, lo, hi))], 'ioossioo',
                '( %s (,) %s ) C_ %s' % (lo, hi, IQQ)) if False else \
            st([st([xr(NQ, nqr), xr('Q', qr)], 'jca', '( %s e. RR* /\\ Q e. RR* )' % NQ), st([lostep, histep], 'jca', '( %s <_ %s /\\ %s <_ Q )' % (NQ, lo, hi)), w.inst('ioossioo')], 'syl2anc',
               '( %s (,) %s ) C_ %s' % (lo, hi, IQQ))
        return st([ss, a1c(w, A, 'ioombl', '( %s (,) %s ) e. dom vol' % (lo, hi)), ccQ, iblQ], 'iblss', '( v e. ( %s (,) %s ) |-> %s ) e. L^1' % (lo, hi, GV))
    nqle = linarith(w, A, [], '%s <_ %s' % (NQ, NQ), closure=cl)
    nqnp = linarith(w, A, [pqle], '%s <_ %s' % (NQ, NP), closure=cl)
    npq = linarith(w, A, [ppos, qpos], '%s <_ Q' % NP, closure=cl)
    qq = linarith(w, A, [], 'Q <_ Q', closure=cl)
    nqp = linarith(w, A, [ppos, qpos], '%s <_ P' % NQ, closure=cl)
    ibl1 = sub_ibl(NQ, NP, nqle, npq)
    ibl2 = sub_ibl(NP, 'Q', nqnp, qq)
    ibl3 = sub_ibl('P', 'Q', nqp, qq)
    S1 = 'S. ( %s (,) %s ) %s _d v' % (NQ, NP, GV); S2 = 'S. ( P (,) Q ) %s _d v' % GV; IPQ = 'S. ( %s (,) Q ) %s _d v' % (NP, GV)
    npin = st([st([nqr, qr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] Q ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ Q ) )' % (NP, NQ, NP, NQ, NP, NP)), npr, nqnp, npq], 'mpbir3and' if False else 'mpbir3and',
              '%s e. ( %s [,] Q )' % (NP, NQ)) if False else \
        st([npr, nqnp, npq, st([nqr, qr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] Q ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ Q ) )' % (NP, NQ, NP, NQ, NP, NP))], 'mpbir3and',
           '%s e. ( %s [,] Q )' % (NP, NQ))
    sp1 = st([nqr, qr, npin, ccQ, ibl1, ibl2], 'itgsplitioo', '%s = ( %s + %s )' % (IQ, S1, IPQ))
    ccPQ, _, _ = ccunder('( %s (,) Q )' % NP)
    npp = linarith(w, A, [ppos], '%s <_ P' % NP, closure=cl)
    pin = st([pr, npp, pqle, st([npr, qr, w.inst('elicc2')], 'syl2anc', '( P e. ( %s [,] Q ) <-> ( P e. RR /\\ %s <_ P /\\ P <_ Q ) )' % (NP, NP))], 'mpbir3and', 'P e. ( %s [,] Q )' % NP)
    sp2 = st([npr, qr, pin, ccPQ, iblP, ibl3], 'itgsplitioo', '%s = ( %s + %s )' % (IPQ, IP, S2))
    cc1, _, _ = ccunder('( %s (,) %s )' % (NQ, NP)); cc2, _, _ = ccunder('( P (,) Q )'); ccP, _, _ = ccunder('( %s (,) P )' % NP)
    s1c = st([cc1, ibl1], 'itgcl', '%s e. CC' % S1); s2c = st([cc2, ibl3], 'itgcl', '%s e. CC' % S2); ipc = st([ccP, iblP], 'itgcl', '%s e. CC' % IP)
    iq2 = st([sp1, st([sp2], 'oveq2d', '( %s + %s ) = ( %s + ( %s + %s ) )' % (S1, IPQ, S1, IP, S2))], 'eqtrd', '%s = ( %s + ( %s + %s ) )' % (IQ, S1, IP, S2))
    iq3 = st([iq2, st([s1c, ipc, s2c], 'add12d', '( %s + ( %s + %s ) ) = ( %s + ( %s + %s ) )' % (S1, IP, S2, IP, S1, S2))], 'eqtrd', '%s = ( %s + ( %s + %s ) )' % (IQ, IP, S1, S2))
    SS = '( %s + %s )' % (S1, S2)
    ssc = st([s1c, s2c], 'addcld', '%s e. CC' % SS)
    dif = st([st([iq3], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (IQ, IP, IP, SS, IP)), st([ipc, ssc], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (IP, SS, IP, SS))], 'eqtrd',
             '( %s - %s ) = %s' % (IQ, IP, SS))
    ic = a1c(w, A, 'ax-icn', '_i e. CC')
    iqc = st([iq3, st([ipc, ssc], 'addcld', '( %s + %s ) e. CC' % (IP, SS))], 'eqeltrd', '%s e. CC' % IQ)
    LQ = LI('G', 'C', 'Q'); LP = LI('G', 'C', 'P')
    ld = st([st([eqQ, eqP], 'oveq12d', '( %s - %s ) = ( ( _i x. %s ) - ( _i x. %s ) )' % (LQ, LP, IQ, IP)), st([ic, iqc, ipc], 'subdid', '( _i x. ( %s - %s ) ) = ( ( _i x. %s ) - ( _i x. %s ) )' % (IQ, IP, IQ, IP))],
            'eqtr4d', '( %s - %s ) = ( _i x. ( %s - %s ) )' % (LQ, LP, IQ, IP))
    ld2 = st([ld, st([dif], 'oveq2d', '( _i x. ( %s - %s ) ) = ( _i x. %s )' % (IQ, IP, SS))], 'eqtrd', '( %s - %s ) = ( _i x. %s )' % (LQ, LP, SS))
    ab = st([st([ld2], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( _i x. %s ) )' % (LQ, LP, SS)),
             st([st([ic, ssc], 'absmuld', '( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (SS, SS)),
                 st([st([a1c(w, A, 'absi', '( abs ` _i ) = 1')], 'oveq1d', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) )' % (SS, SS)),
                     st([st([ssc], 'abscld', '( abs ` %s ) e. RR' % SS)], 'recnd', '( abs ` %s ) e. CC' % SS) and
                     st([st([st([ssc], 'abscld', '( abs ` %s ) e. RR' % SS)], 'recnd', '( abs ` %s ) e. CC' % SS)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (SS, SS))],
                    'eqtrd', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s )' % (SS, SS))], 'eqtrd', '( abs ` ( _i x. %s ) ) = ( abs ` %s )' % (SS, SS))],
            'eqtrd', '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (LQ, LP, SS))
    tri = st([s1c, s2c], 'abstrid', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (SS, S1, S2))
    # the two tails
    q4r = cl.mem('( 1 / 4 )', 'RR'); q4n = cl.ne0('( 1 / 4 )')
    nq4r = cl.mem('-u ( 1 / 4 )', 'RR'); nq4n = st([st([q4r], 'recnd', '( 1 / 4 ) e. CC'), q4n], 'negne0d', '-u ( 1 / 4 ) =/= 0')

    def ptw(I, neg):
        Av = '( %s /\\ v e. %s )' % (A, I)
        sv = mkst(w, Av)
        vin = sv([], 'simpr', 'v e. %s' % I)
        vr = sv([vin, w.inst('elioore')], 'syl', 'v e. RR')
        lo, hi = (NQ, NP) if neg else ('P', 'Q')
        lor = lift(w, nqr if neg else pr, Av); hir = lift(w, npr if neg else qr, Av)
        bb = sv([vin, sv([sv([lor], 'rexrd', '%s e. RR*' % lo), sv([hir], 'rexrd', '%s e. RR*' % hi), w.inst('elioo2')], 'syl2anc',
                         '( v e. %s <-> ( v e. RR /\\ %s < v /\\ v < %s ) )' % (I, lo, hi))], 'mpbid', '( v e. RR /\\ %s < v /\\ v < %s )' % (lo, hi))
        vlo = sv([bb], 'simp2d', '%s < v' % lo); vhi = sv([bb], 'simp3d', 'v < %s' % hi)
        clv = Closure(w, Av, {'v': ('RR', vr), 'P': ('RR', lift(w, pr, Av)), 'Q': ('RR', lift(w, qr, Av)), 'Y': ('RR+', lift(w, d['yrp'], Av))})
        if neg:
            vle0 = linarith(w, Av, [vhi, lift(w, ppos, Av)], 'v <_ 0', closure=clv)
            av = sv([vr, vle0], 'absnidd', '( abs ` v ) = -u v')
            yle = linarith(w, Av, [vhi, lift(w, yp, Av)], 'Y <_ -u v', closure=clv)
            K = '( 1 / 4 )'
            ex_eq = lineq(w, Av, '-u ( -u v / 4 )', '( %s x. v )' % K, closure=clv)
            AVT = '-u v'
        else:
            vge0 = linarith(w, Av, [vlo, lift(w, ppos, Av)], '0 <_ v', closure=clv)
            av = sv([vr, vge0], 'absidd', '( abs ` v ) = v')
            yle = linarith(w, Av, [vlo, lift(w, yp, Av)], 'Y <_ v', closure=clv)
            K = '-u ( 1 / 4 )'
            ex_eq = lineq(w, Av, '-u ( v / 4 )', '( %s x. v )' % K, closure=clv)
            AVT = 'v'
        yle2 = sv([yle, av], 'breqtrrd', 'Y <_ ( abs ` v )')
        bv, bform = bndat(w, Av, d, 'v', vr)
        b1 = sv([yle2, bv], 'mpd', '( abs ` %s ) <_ ( M x. %s )' % (GV, E4('( abs ` v )')))
        e1 = sv([sv([sv([av], 'oveq1d', '( ( abs ` v ) / 4 ) = ( %s / 4 )' % AVT)], 'negeqd', '-u ( ( abs ` v ) / 4 ) = -u ( %s / 4 )' % AVT), ex_eq], 'eqtrd',
                '-u ( ( abs ` v ) / 4 ) = ( %s x. v )' % K)
        e2 = sv([sv([e1], 'oveq2d', '%s = ( 2 ^c ( %s x. v ) )' % (E4('( abs ` v )'), K))], 'oveq2d', '( M x. %s ) = ( M x. ( 2 ^c ( %s x. v ) ) )' % (E4('( abs ` v )'), K))
        return sv([b1, e2], 'breqtrd', '( abs ` %s ) <_ ( M x. ( 2 ^c ( %s x. v ) ) )' % (GV, K))
    V1 = '( ( ( 2 ^c ( ( 1 / 4 ) x. %s ) ) - ( 2 ^c ( ( 1 / 4 ) x. %s ) ) ) / ( ( 1 / 4 ) x. %s ) )' % (NP, NQ, L2)
    V2 = '( ( ( 2 ^c ( -u ( 1 / 4 ) x. Q ) ) - ( 2 ^c ( -u ( 1 / 4 ) x. P ) ) ) / ( -u ( 1 / 4 ) x. %s ) )' % L2
    h1 = st([st([st([nqr, npr], 'jca', '( %s e. RR /\\ %s e. RR )' % (NQ, NP)), nqnp], 'jca', '( ( %s e. RR /\\ %s e. RR ) /\\ %s <_ %s )' % (NQ, NP, NQ, NP)),
             st([q4r, q4n], 'jca', '( ( 1 / 4 ) e. RR /\\ ( 1 / 4 ) =/= 0 )'), d['mr'], cc1, ibl1, ptw('( %s (,) %s )' % (NQ, NP), True)], 'z6half',
            '( abs ` %s ) <_ ( M x. %s )' % (S1, V1))
    h2 = st([st([st([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )'), pqle], 'jca', '( ( P e. RR /\\ Q e. RR ) /\\ P <_ Q )'),
             st([nq4r, nq4n], 'jca', '( -u ( 1 / 4 ) e. RR /\\ -u ( 1 / 4 ) =/= 0 )'), d['mr'], cc2, ibl3, ptw('( P (,) Q )', False)], 'z6half',
            '( abs ` %s ) <_ ( M x. %s )' % (S2, V2))
    K8 = '( ( 8 x. M ) / %s )' % L2
    e1 = E4('P'); e2 = E4('Q')
    kal = st([st([d['mr'], st([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )')], 'jca', '( M e. RR /\\ ( P e. RR /\\ Q e. RR ) )'), w.inst('z6kalg')], 'syl',
             '( ( M x. %s ) + ( M x. %s ) ) = ( %s x. ( %s - %s ) )' % (V1, V2, K8, e1, e2))
    lrp = l2rp(w, A)
    e1rp = st([a1c(w, A, '2rp', '2 e. RR+'), cl.mem('-u ( P / 4 )', 'RR')], 'rpcxpcld', '%s e. RR+' % e1)
    e2rp = st([a1c(w, A, '2rp', '2 e. RR+'), cl.mem('-u ( Q / 4 )', 'RR')], 'rpcxpcld', '%s e. RR+' % e2)
    # 0 <_ M from the bound at u = Y
    yr = cl.mem('Y', 'RR')
    by, _ = bndat(w, A, d, 'Y', yr)
    ay = st([yr, st([cl.gt0('Y')], 'ltled' if False else 'ltled', '0 <_ Y') if False else st([cl.mem('0', 'RR'), yr, cl.gt0('Y')], 'ltled', '0 <_ Y')], 'absidd', '( abs ` Y ) = Y')
    yay = st([st([yr], 'leidd', 'Y <_ Y'), ay], 'breqtrrd', 'Y <_ ( abs ` Y )')
    gy = st([yay, by], 'mpd', '( abs ` ( G ` ( C + ( _i x. Y ) ) ) ) <_ ( M x. %s )' % E4('( abs ` Y )'))
    gyc = gcl(w, A, d, 'Y', yr)
    EY = E4('( abs ` Y )')
    eyrp = st([a1c(w, A, '2rp', '2 e. RR+'), st([st([st([st([gyc], 'abscld', '( abs ` ( G ` ( C + ( _i x. Y ) ) ) ) e. RR') and st([yr], 'recnd', 'Y e. CC')], 'abscld', '( abs ` Y ) e. RR') if False else
                                                     st([st([yr], 'recnd', 'Y e. CC')], 'abscld', '( abs ` Y ) e. RR'), a1c(w, A, '4re', '4 e. RR'), a1c(w, A, '4ne0', '4 =/= 0')], 'redivcld', '( ( abs ` Y ) / 4 ) e. RR')],
                                                'renegcld', '-u ( ( abs ` Y ) / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % EY)
    m0a = st([st([st([gyc], 'absge0d', '0 <_ ( abs ` ( G ` ( C + ( _i x. Y ) ) ) )'), gy], 'jca', '( 0 <_ ( abs ` ( G ` ( C + ( _i x. Y ) ) ) ) /\\ ( abs ` ( G ` ( C + ( _i x. Y ) ) ) ) <_ ( M x. %s ) )' % EY)], 'simpld',
             '0 <_ ( abs ` ( G ` ( C + ( _i x. Y ) ) ) )') if False else st([gyc], 'absge0d', '0 <_ ( abs ` ( G ` ( C + ( _i x. Y ) ) ) )')
    m0b = st([cl.mem('0', 'RR'), st([gyc], 'abscld', '( abs ` ( G ` ( C + ( _i x. Y ) ) ) ) e. RR'), st([d['mr'], st([eyrp], 'rpred', '%s e. RR' % EY)], 'remulcld', '( M x. %s ) e. RR' % EY), m0a, gy], 'letrd',
             '0 <_ ( M x. %s )' % EY)
    m0 = st([d['mr'], eyrp, m0b], 'prodge0ld', '0 <_ M')
    k8ge = st([st([cl.mem('8', 'RR'), d['mr']], 'remulcld', '( 8 x. M ) e. RR'), lrp, st([cl.mem('8', 'RR'), d['mr'], cl.ge0('8'), m0], 'mulge0d', '0 <_ ( 8 x. M )')], 'divge0d', '0 <_ %s' % K8)
    k8r = st([st([cl.mem('8', 'RR'), d['mr']], 'remulcld', '( 8 x. M ) e. RR'), lrp], 'rerpdivcld', '%s e. RR' % K8)
    e2r = st([e2rp], 'rpred', '%s e. RR' % e2); e1r = st([e1rp], 'rpred', '%s e. RR' % e1)
    nn = st([k8r, e2r, k8ge, st([e2rp], 'rpge0d', '0 <_ %s' % e2)], 'mulge0d', '0 <_ ( %s x. %s )' % (K8, e2))
    sd = st([st([k8r], 'recnd', '%s e. CC' % K8), st([e1r], 'recnd', '%s e. CC' % e1), st([e2r], 'recnd', '%s e. CC' % e2)], 'subdid',
            '( %s x. ( %s - %s ) ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (K8, e1, e2, K8, e1, K8, e2))
    kal2 = st([kal, sd], 'eqtrd', '( ( M x. %s ) + ( M x. %s ) ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (V1, V2, K8, e1, K8, e2))
    fc = Closure(w, A, {})
    LQP = '( abs ` ( %s - %s ) )' % (LQ, LP)
    lqpc = st([ld2, st([ic, ssc], 'mulcld', '( _i x. %s ) e. CC' % SS)], 'eqeltrd', '( %s - %s ) e. CC' % (LQ, LP))
    fc.leaf(LQP, 'RR', st([lqpc], 'abscld', '%s e. RR' % LQP))
    fc.leaf('( abs ` %s )' % SS, 'RR', st([ssc], 'abscld', '( abs ` %s ) e. RR' % SS))
    fc.leaf('( abs ` %s )' % S1, 'RR', st([s1c], 'abscld', '( abs ` %s ) e. RR' % S1))
    fc.leaf('( abs ` %s )' % S2, 'RR', st([s2c], 'abscld', '( abs ` %s ) e. RR' % S2))

    def rp2(x):
        return st([st([a1c(w, A, '2rp', '2 e. RR+'), cl.mem(x, 'RR')], 'rpcxpcld', '( 2 ^c %s ) e. RR+' % x)], 'rpred', '( 2 ^c %s ) e. RR' % x)

    def vr(V, k, a, b):
        num_ = st([rp2('( %s x. %s )' % (k, a)), rp2('( %s x. %s )' % (k, b))], 'resubcld', '( ( 2 ^c ( %s x. %s ) ) - ( 2 ^c ( %s x. %s ) ) ) e. RR' % (k, a, k, b))
        den = st([cl.mem(k, 'RR'), st([lrp], 'rpred', '%s e. RR' % L2)], 'remulcld', '( %s x. %s ) e. RR' % (k, L2))
        dne = st([cl.mem(k, 'CC'), st([lrp], 'rpcnd', '%s e. CC' % L2), q4n if k == '( 1 / 4 )' else nq4n, st([lrp], 'rpne0d', '%s =/= 0' % L2)], 'mulne0d', '( %s x. %s ) =/= 0' % (k, L2))
        vv = st([num_, den, dne], 'redivcld', '%s e. RR' % V)
        return st([d['mr'], vv], 'remulcld', '( M x. %s ) e. RR' % V)
    fc.leaf('( M x. %s )' % V1, 'RR', vr(V1, '( 1 / 4 )', NP, NQ))
    fc.leaf('( M x. %s )' % V2, 'RR', vr(V2, '-u ( 1 / 4 )', 'Q', 'P'))
    fc.leaf('( %s x. %s )' % (K8, e1), 'RR', st([k8r, e1r], 'remulcld', '( %s x. %s ) e. RR' % (K8, e1)))
    fc.leaf('( %s x. %s )' % (K8, e2), 'RR', st([k8r, e2r], 'remulcld', '( %s x. %s ) e. RR' % (K8, e2)))
    linarith(w, A, [ab, tri, h1, h2, kal2, nn], '%s <_ ( %s x. %s )' % (LQP, K8, e1), closure=fc, name='qed')
    return w


# ---------------------------------------------------------------- z6vlex
K8T = '( ( 8 x. M ) / ( log ` 2 ) )'


def licl(w, A, d, T, trp):
    """( A -> LI ( T ) e. CC ) and the segment inclusion"""
    st = mkst(w, A)
    a, b = segs(T)
    cr = lift(w, d['cr'], A)
    seg = st([st([st([cr, trp], 'jca', '( C e. RR /\\ %s e. RR+ )' % T), lift(w, d['al'], A)], 'jca', '( ( C e. RR /\\ %s e. RR+ ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. D )' % T),
              w.inst('z6segd')], 'syl', '( %s cseg %s ) C_ D' % (a, b))
    cc = st([cr], 'recnd', 'C e. CC'); ic = a1c(w, A, 'ax-icn', '_i e. CC'); tc = st([trp], 'rpcnd', '%s e. CC' % T)
    ac = st([cc, st([ic, st([tc], 'negcld', '-u %s e. CC' % T)], 'mulcld', '( _i x. -u %s ) e. CC' % T)], 'addcld', '%s e. CC' % a)
    bc = st([cc, st([ic, tc], 'mulcld', '( _i x. %s ) e. CC' % T)], 'addcld', '%s e. CC' % b)
    return st([st([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (a, b)), st([lift(w, d['gcn'], A), seg], 'jca', '( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (a, b)), w.inst('lintcl')],
              'syl2anc', '%s e. CC' % LI('G', 'C', T))


def z6vlex():
    w = W('z6vlex', 'The truncated vertical line integrals converge as ` t -> +oo ` : Cauchy ( ~ caucvgr ) by the tail '
          '~ z6vltail and ` 2 ^ ( - t / 4 ) -> 0 ` ( ~ z6e4lim ).')
    A = ante_of('z6vlex')
    st = mkst(w, A)
    d = hvparts(w, A, st([], 'id', A))
    VF = VLF('G', 'C')
    At = '( %s /\\ t e. RR+ )' % A
    lt = licl(w, At, d, 't', w.s([], 'simpr', '( %s -> t e. RR+ )' % At))
    ff = st([lt, w.s([], 'eqid', '%s = %s' % (VF, VF))], 'fmptd', '%s : RR+ --> CC' % VF)
    sup = a1c(w, A, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')
    # the majorant tends to 0
    Ax = '( %s /\\ x e. RR+ )' % A
    sx = mkst(w, Ax)
    cl = Closure(w, Ax, {'M': ('RR', lift(w, d['mr'], Ax)), 'Y': ('RR+', lift(w, d['yrp'], Ax))})
    lrp = l2rp(w, Ax)
    cl.leaf(L2, 'RR+', lrp)
    k8c = cl.mem(K8T, 'CC')
    Axt = '( %s /\\ t e. RR+ )' % Ax
    E4T = E4('t')
    kv = w.s([lift(w, k8c, Axt)], 'elexd', '( %s -> %s e. _V )' % (Axt, K8T))
    ev = w.s([], 'ovexd', '( %s -> %s e. _V )' % (Axt, E4T))
    kc = sx([a1c(w, Ax, 'rpssre', 'RR+ C_ RR'), k8c, w.inst('rlimconst')], 'syl2anc', '( t e. RR+ |-> %s ) ~~>r %s' % (K8T, K8T))
    el = a1(w, Ax, w.s([], 'z6e4lim', STATEMENTS['z6e4lim']), STATEMENTS['z6e4lim'])
    KE = '( %s x. %s )' % (K8T, E4T)
    lm0 = sx([kv, ev, kc, el], 'rlimmul', '( t e. RR+ |-> %s ) ~~>r ( %s x. 0 )' % (KE, K8T))
    lm = sx([lm0, sx([k8c], 'mul01d', '( %s x. 0 ) = 0' % K8T)], 'breqtrd', '( t e. RR+ |-> %s ) ~~>r 0' % KE)
    alv = sx([w.s([], 'ovexd', '( %s -> %s e. _V )' % (Axt, KE))], 'ralrimiva', 'A. t e. RR+ %s e. _V' % KE)
    RB = 'A. t e. RR+ ( y <_ t -> ( abs ` ( %s - 0 ) ) < x )' % KE
    ri = sx([alv, sx([], 'simpr', 'x e. RR+'), lm], 'rlimi', 'E. y e. RR %s' % RB)
    # the Cauchy step
    Ay = '( ( %s /\\ y e. RR ) /\\ %s )' % (Ax, RB)
    sy_ = mkst(w, Ay)
    yr = sy_([], 'simplr', 'y e. RR')
    cly = Closure(w, Ay, {'M': ('RR', lift(w, d['mr'], Ay)), 'Y': ('RR+', lift(w, d['yrp'], Ay)), 'y': ('RR', yr)})
    ay = sy_([st([], 'id', A) and sy_([yr], 'recnd', 'y e. CC')], 'abscld', '( abs ` y ) e. RR')
    cly.leaf('( abs ` y )', 'RR', ay)
    J = '( Y + ( abs ` y ) )'
    jgt = linarith(w, Ay, [cly.gt0('Y'), sy_([sy_([yr], 'recnd', 'y e. CC')], 'absge0d', '0 <_ ( abs ` y )')], '0 < %s' % J, closure=cly)
    jr = cly.mem(J, 'RR')
    jrp = sy_([jr, jgt], 'elrpd', '%s e. RR+' % J)
    yj = linarith(w, Ay, [sy_([yr, w.inst('leabs')], 'syl', 'y <_ ( abs ` y )'), cly.gt0('Y')], 'y <_ %s' % J, closure=cly)
    Yj = linarith(w, Ay, [sy_([sy_([yr], 'recnd', 'y e. CC')], 'absge0d', '0 <_ ( abs ` y )')], 'Y <_ %s' % J, closure=cly)
    # the majorant at J
    body = '( y <_ t -> ( abs ` ( %s - 0 ) ) < x )' % KE
    idk = w.s([], 'id', '( t = %s -> t = %s )' % (J, J))
    sb, new = w.wcongr(body, {'t': J}, 't = %s' % J, {'t': idk})
    rs = w.s([sb], 'rspcv', '( %s e. RR+ -> ( %s -> %s ) )' % (J, RB, new))
    mj = sy_([sy_([jrp, sy_([], 'simpr', RB), rs], 'sylc', new), yj], 'mpd' if False else 'mpd', new.split(' -> ', 1)[1][:-2]) if False else None
    mj0 = sy_([jrp, sy_([], 'simpr', RB), rs], 'sylc', new)
    mjc = new[len('( y <_ %s -> ' % J):-2]
    mj = sy_([yj, mj0], 'mpd', mjc)
    Ak = '( %s /\\ ( k e. RR+ /\\ %s <_ k ) )' % (Ay, J)
    sk = mkst(w, Ak)
    krp = sk([], 'simprl', 'k e. RR+'); jk = sk([], 'simprr', '%s <_ k' % J)
    tl = sk([sk([lift(w, st([], 'id', A), Ak), sk([sk([lift(w, jr, Ak), sk([krp], 'rpred', 'k e. RR')], 'jca', '( %s e. RR /\\ k e. RR )' % J),
                                                     sk([lift(w, Yj, Ak), jk], 'jca', '( Y <_ %s /\\ %s <_ k )' % (J, J))], 'jca',
                                                    '( ( %s e. RR /\\ k e. RR ) /\\ ( Y <_ %s /\\ %s <_ k ) )' % (J, J, J))], 'jca',
                 '( %s /\\ ( ( %s e. RR /\\ k e. RR ) /\\ ( Y <_ %s /\\ %s <_ k ) ) )' % (A, J, J, J)), w.inst('z6vltail')], 'syl',
            '( abs ` ( %s - %s ) ) <_ ( %s x. %s )' % (LI('G', 'C', 'k'), LI('G', 'C', J), K8T, E4(J)))
    clk = Closure(w, Ak, {})
    LKJ = '( abs ` ( %s - %s ) )' % (LI('G', 'C', 'k'), LI('G', 'C', J))
    lkc = licl(w, Ak, d, 'k', krp); ljc = licl(w, Ak, d, J, lift(w, jrp, Ak))
    clk.leaf(LKJ, 'RR', sk([sk([lkc, ljc], 'subcld', '( %s - %s ) e. CC' % (LI('G', 'C', 'k'), LI('G', 'C', J)))], 'abscld', '%s e. RR' % LKJ))
    KEJ = '( %s x. %s )' % (K8T, E4(J))
    clm = Closure(w, Ak, {'M': ('RR', lift(w, d['mr'], Ak)), 'Y': ('RR+', lift(w, d['yrp'], Ak)), 'y': ('RR', lift(w, yr, Ak))})
    clm.leaf(L2, 'RR+', lift(w, lrp, Ak))
    clm.leaf('( abs ` y )', 'RR', lift(w, ay, Ak))
    kejr = clm.mem(KEJ, 'RR')
    clk.leaf(KEJ, 'RR', kejr)
    ABE = '( abs ` ( %s - 0 ) )' % KEJ
    kej0 = sk([kejr, cl.mem('0', 'RR') if False else sk([], '0red', '0 e. RR')], 'resubcld', '( %s - 0 ) e. RR' % KEJ)
    clk.leaf(ABE, 'RR', sk([sk([kej0], 'recnd', '( %s - 0 ) e. CC' % KEJ)], 'abscld', '%s e. RR' % ABE))
    clk.leaf('( %s - 0 )' % KEJ, 'RR', kej0)
    lab = sk([kej0, w.inst('leabs')], 'syl', '( %s - 0 ) <_ %s' % (KEJ, ABE))
    s0 = sk([sk([kejr], 'recnd', '%s e. CC' % KEJ)], 'subid1d', '( %s - 0 ) = %s' % (KEJ, KEJ))
    xr_ = lift(w, sx([], 'simpr', 'x e. RR+'), Ak)
    clk.leaf('x', 'RR+', xr_)
    fin = linarith(w, Ak, [tl, lab, s0, lift(w, mj, Ak)], '%s < x' % LKJ, closure=clk)
    # VLF values
    def vfv(T, mem):
        sub = w.s([], 'id', '( t = %s -> t = %s )' % (T, T))
        sbv, val = w.congr(LI('G', 'C', 't'), {'t': T}, 't = %s' % T, {'t': sub})
        f = w.s([sbv, w.s([], 'eqid', '%s = %s' % (VF, VF)), w.s([], 'ovex', '%s e. _V' % val)], 'fvmpt', '( %s e. RR+ -> ( %s ` %s ) = %s )' % (T, VF, T, val))
        return sk([mem, f], 'syl', '( %s ` %s ) = %s' % (VF, T, val))
    fk = vfv('k', krp); fj = vfv(J, lift(w, jrp, Ak))
    eq = sk([sk([fk, fj], 'oveq12d', '( ( %s ` k ) - ( %s ` %s ) ) = ( %s - %s )' % (VF, VF, J, LI('G', 'C', 'k'), LI('G', 'C', J)))], 'fveq2d',
            '( abs ` ( ( %s ` k ) - ( %s ` %s ) ) ) = %s' % (VF, VF, J, LKJ))
    fin2 = sk([eq, fin], 'eqbrtrd', '( abs ` ( ( %s ` k ) - ( %s ` %s ) ) ) < x' % (VF, VF, J))
    KB = '( %s <_ k -> ( abs ` ( ( %s ` k ) - ( %s ` %s ) ) ) < x )' % (J, VF, VF, J)
    Ak2 = '( %s /\\ k e. RR+ )' % Ay
    imp = w.s([w.s([fin2], 'expr', '( %s -> ( %s <_ k -> ( abs ` ( ( %s ` k ) - ( %s ` %s ) ) ) < x ) )' % (Ak2, J, VF, VF, J))], 'ralrimiva',
              '( %s -> A. k e. RR+ %s )' % (Ay, KB))
    KBj = '( j <_ k -> ( abs ` ( ( %s ` k ) - ( %s ` j ) ) ) < x )' % (VF, VF)
    sbj = w.s([w.s([w.s([], 'breq1', '( j = %s -> ( j <_ k <-> %s <_ k ) )' % (J, J)),
                    w.s([w.s([w.s([w.s([], 'fveq2', '( j = %s -> ( %s ` j ) = ( %s ` %s ) )' % (J, VF, VF, J))], 'oveq2d',
                                  '( j = %s -> ( ( %s ` k ) - ( %s ` j ) ) = ( ( %s ` k ) - ( %s ` %s ) ) )' % (J, VF, VF, VF, VF, J))], 'fveq2d',
                              '( j = %s -> ( abs ` ( ( %s ` k ) - ( %s ` j ) ) ) = ( abs ` ( ( %s ` k ) - ( %s ` %s ) ) ) )' % (J, VF, VF, VF, VF, J))], 'breq1d',
                        '( j = %s -> ( ( abs ` ( ( %s ` k ) - ( %s ` j ) ) ) < x <-> ( abs ` ( ( %s ` k ) - ( %s ` %s ) ) ) < x ) )' % (J, VF, VF, VF, VF, J))], 'imbi12d',
                   '( j = %s -> ( %s <-> %s ) )' % (J, KBj, KB))], 'ralbidv', '( j = %s -> ( A. k e. RR+ %s <-> A. k e. RR+ %s ) )' % (J, KBj, KB))
    ex = w.s([jrp, imp, w.s([sbj], 'rspcev', '( ( %s e. RR+ /\\ A. k e. RR+ %s ) -> E. j e. RR+ A. k e. RR+ %s )' % (J, KB, KBj))], 'syl2anc',
             '( %s -> E. j e. RR+ A. k e. RR+ %s )' % (Ay, KBj))
    ex2 = w.s([w.s([ex], 'ex', '( ( %s /\\ y e. RR ) -> ( %s -> E. j e. RR+ A. k e. RR+ %s ) )' % (Ax, RB, KBj))], 'rexlimdva',
              '( %s -> ( E. y e. RR %s -> E. j e. RR+ A. k e. RR+ %s ) )' % (Ax, RB, KBj))
    cx = w.s([ri, ex2], 'mpd', '( %s -> E. j e. RR+ A. k e. RR+ %s )' % (Ax, KBj))
    cau = st([cx], 'ralrimiva', 'A. x e. RR+ E. j e. RR+ A. k e. RR+ %s' % KBj)
    dm = st([a1c(w, A, 'rpssre', 'RR+ C_ RR'), ff, sup, cau], 'caucvgr', '%s e. dom ~~>r' % VF)
    w.qed([dm, st([ff, sup], 'rlimdm', '( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) )' % (VF, VF, VF))], 'mpbid', STATEMENTS['z6vlex'])
    return w


# ---------------------------------------------------------------- z6vlt
def z6vlt():
    w = W('z6vlt', 'The tail bound in the limit: ` | VL - LI ( R ) | <_ ( 8 M / log 2 ) 2 ^ ( - R / 4 ) ` for ` R >_ Y ` '
          '( ~ z6vlex , ~ z6vltail on ` [ R , +oo ) ` , ~ rlimle ).')
    A = ante_of('z6vlt')
    st = mkst(w, A)
    HVt = split_imp(STATEMENTS['z6vlcvg'])[0]
    hv = st([], 'simpl', HVt)
    d = hvparts(w, A, hv)
    rrp = st([], 'simprl', 'R e. RR+'); yR = st([], 'simprr', 'Y <_ R')
    rr = st([rrp], 'rpred', 'R e. RR')
    VF = VLF('G', 'C'); VLt = VL('G', 'C')
    lim = st([hv, w.inst('z6vlex')], 'syl', '%s ~~>r %s' % (VF, VLt))
    VFs = '( s e. RR+ |-> %s )' % LI('G', 'C', 's')
    idk = w.s([], 'id', '( t = s -> t = s )')
    sb, _ = w.congr(LI('G', 'C', 't'), {'t': 's'}, 't = s', {'t': idk})
    cb = a1(w, A, w.s([sb], 'cbvmptv', '%s = %s' % (VF, VFs)), '%s = %s' % (VF, VFs))
    lims = st([cb, lim], 'eqbrtrrd', '%s ~~>r %s' % (VFs, VLt))
    I = '( R [,) +oo )'
    As = '( %s /\\ s e. %s )' % (A, I)
    ss_ = mkst(w, As)
    sb2 = ss_([ss_([], 'simpr', 's e. %s' % I), ss_([lift(w, rr, As), w.inst('elicopnf')], 'syl', '( s e. %s <-> ( s e. RR /\\ R <_ s ) )' % I)], 'mpbid', '( s e. RR /\\ R <_ s )')
    sr = ss_([sb2], 'simpld', 's e. RR'); Rs = ss_([sb2], 'simprd', 'R <_ s')
    cls = Closure(w, As, {'s': ('RR', sr), 'R': ('RR+', lift(w, rrp, As))})
    srp = ss_([sr, linarith(w, As, [Rs, cls.gt0('R')], '0 < s', closure=cls)], 'elrpd', 's e. RR+')
    iss = st([w.s([srp], 'ex', '( %s -> ( s e. %s -> s e. RR+ ) )' % (A, I))], 'ssrdv', '%s C_ RR+' % I)
    rres = st([lims, w.inst('rlimres')], 'syl', '( %s |` %s ) ~~>r %s' % (VFs, I, VLt))
    rm = st([iss, w.inst('resmpt')], 'syl', '( %s |` %s ) = ( s e. %s |-> %s )' % (VFs, I, I, LI('G', 'C', 's')))
    lI = st([rm, rres], 'eqbrtrrd', '( s e. %s |-> %s ) ~~>r %s' % (I, LI('G', 'C', 's'), VLt))
    lrc = licl(w, A, d, 'R', rrp)
    ire = st([rr, a1c(w, A, 'pnfxr', '+oo e. RR*'), w.inst('icossre')], 'syl2anc', '%s C_ RR' % I)
    lc = st([ire, lrc, w.inst('rlimconst')], 'syl2anc', '( s e. %s |-> %s ) ~~>r %s' % (I, LI('G', 'C', 'R'), LI('G', 'C', 'R')))
    lsc = licl(w, As, d, 's', srp)
    DF = '( %s - %s )' % (LI('G', 'C', 's'), LI('G', 'C', 'R'))
    ls = st([ss_([lsc], 'elexd', '%s e. _V' % LI('G', 'C', 's')), ss_([lift(w, lrc, As)], 'elexd', '%s e. _V' % LI('G', 'C', 'R')), lI, lc], 'rlimsub',
            '( s e. %s |-> %s ) ~~>r ( %s - %s )' % (I, DF, VLt, LI('G', 'C', 'R')))
    dfc = ss_([lsc, lift(w, lrc, As)], 'subcld', '%s e. CC' % DF)
    la = st([ss_([dfc], 'elexd', '%s e. _V' % DF), ls], 'rlimabs', '( s e. %s |-> ( abs ` %s ) ) ~~>r ( abs ` ( %s - %s ) )' % (I, DF, VLt, LI('G', 'C', 'R')))
    cl = Closure(w, A, {'M': ('RR', d['mr']), 'R': ('RR+', rrp)})
    cl.leaf(L2, 'RR+', l2rp(w, A))
    KR = '( %s x. %s )' % (K8T, E4('R'))
    krr = cl.mem(KR, 'RR')
    kc = st([ire, st([krr], 'recnd', '%s e. CC' % KR), w.inst('rlimconst')], 'syl2anc', '( s e. %s |-> %s ) ~~>r %s' % (I, KR, KR))
    sup = st([st([rr], 'rexrd', 'R e. RR*'), st([rr], 'renepnfd', 'R =/= +oo'), w.inst('icopnfsup')], 'syl2anc', 'sup ( %s , RR* , < ) = +oo' % I)
    tl = ss_([ss_([lift(w, hv, As), ss_([ss_([lift(w, rr, As), sr], 'jca', '( R e. RR /\\ s e. RR )'), ss_([lift(w, yR, As), Rs], 'jca', '( Y <_ R /\\ R <_ s )')], 'jca',
                                        '( ( R e. RR /\\ s e. RR ) /\\ ( Y <_ R /\\ R <_ s ) )')], 'jca', '( %s /\\ ( ( R e. RR /\\ s e. RR ) /\\ ( Y <_ R /\\ R <_ s ) ) )' % HVt),
              w.inst('z6vltail')], 'syl', '( abs ` %s ) <_ %s' % (DF, KR))
    w.qed([sup, la, kc, ss_([dfc], 'abscld', '( abs ` %s ) e. RR' % DF), lift(w, krr, As), tl], 'rlimle', STATEMENTS['z6vlt'])
    return w


# ---------------------------------------------------------------- z6vlcvg
def z6vlcvg():
    w = W('z6vlcvg', 'The vertical line integral exists and its truncations converge at the rate of the majorant: '
          'for ` G ` continuous on a domain containing the line ` Re = C ` with ` | G ( C + i u ) | <_ M 2 ^ ( - | u | / 4 ) ` '
          'for ` | u | >_ Y ` , the limit ` VL ` exists and ` | VL - LI ( t ) | <_ ( 8 M / log 2 ) 2 ^ ( - t / 4 ) ` for '
          '` t >_ Y ` ( ~ z6vlex , ~ z6vlt ).')
    A = ante_of('z6vlcvg')
    st = mkst(w, A)
    ex = st([st([], 'id', A), w.inst('z6vlex')], 'syl', '%s ~~>r %s' % (VLF('G', 'C'), VL('G', 'C')))
    Q = '( %s /\\ ( t e. RR+ /\\ Y <_ t ) )' % A
    concl = '( abs ` ( %s - %s ) ) <_ ( %s x. %s )' % (VL('G', 'C'), LI('G', 'C', 't'), K8T, E4('t'))
    vt = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Q, A)), w.s([], 'simpr', '( %s -> ( t e. RR+ /\\ Y <_ t ) )' % Q)], 'jca', '( %s -> %s )' % (Q, Q)) if False else
              w.s([], 'id', '( %s -> %s )' % (Q, Q)), w.inst('z6vlt')], 'syl', '( %s -> %s )' % (Q, concl))
    e = w.s([vt], 'expr', '( ( %s /\\ t e. RR+ ) -> ( Y <_ t -> %s ) )' % (A, concl))
    al = st([e], 'ralrimiva', 'A. t e. RR+ ( Y <_ t -> %s )' % concl)
    w.qed([ex, al], 'jca', STATEMENTS['z6vlcvg'])
    return w


# ---------------------------------------------------------------- z6vleq
def z6vleq():
    w = W('z6vleq', 'The vertical line integral depends only on the values on the line ( ~ linteq on every truncation, '
          '~ z6segd for the set where ` F ` and ` G ` agree).')
    A = ante_of('z6vleq')
    st = mkst(w, A)
    cr = st([], 'simpll', 'C e. RR')
    fv = st([st([st([], 'simplr', '( F e. V /\\ G e. W )')], 'simpld', 'F e. V'), w.inst('elex')], 'syl', 'F e. _V')
    gv = st([st([st([], 'simplr', '( F e. V /\\ G e. W )')], 'simprd', 'G e. W'), w.inst('elex')], 'syl', 'G e. _V')
    WU = '( C + ( _i x. u ) )'
    al = st([], 'simpr', 'A. u e. RR ( F ` %s ) = ( G ` %s )' % (WU, WU))
    D0 = '{ a | ( F ` a ) = ( G ` a ) }'
    ea = w.s([w.s([], 'ovex', '%s e. _V' % WU), w.s([w.s([], 'fveq2', '( a = %s -> ( F ` a ) = ( F ` %s ) )' % (WU, WU)), w.s([], 'fveq2', '( a = %s -> ( G ` a ) = ( G ` %s ) )' % (WU, WU))],
                                                     'eqeq12d', '( a = %s -> ( ( F ` a ) = ( G ` a ) <-> ( F ` %s ) = ( G ` %s ) ) )' % (WU, WU, WU))], 'elab',
             '( %s e. %s <-> ( F ` %s ) = ( G ` %s ) )' % (WU, D0, WU, WU))
    ri = w.s([w.s([ea], 'biimpri', '( ( F ` %s ) = ( G ` %s ) -> %s e. %s )' % (WU, WU, WU, D0))], 'ralimi',
             '( A. u e. RR ( F ` %s ) = ( G ` %s ) -> A. u e. RR %s e. %s )' % (WU, WU, WU, D0))
    al2 = st([al, ri], 'syl', 'A. u e. RR %s e. %s' % (WU, D0))
    At = '( %s /\\ t e. RR+ )' % A
    s2 = mkst(w, At)
    trp = s2([], 'simpr', 't e. RR+')
    a, b = segs('t')
    SEGt = '( %s cseg %s )' % (a, b)
    sd = s2([s2([s2([lift(w, cr, At), trp], 'jca', '( C e. RR /\\ t e. RR+ )'), lift(w, al2, At)], 'jca', '( ( C e. RR /\\ t e. RR+ ) /\\ A. u e. RR %s e. %s )' % (WU, D0)),
             w.inst('z6segd')], 'syl', '%s C_ %s' % (SEGt, D0))
    Az = '( %s /\\ z e. %s )' % (At, SEGt)
    sz = mkst(w, Az)
    zd = sz([lift(w, sd, Az), sz([], 'simpr', 'z e. %s' % SEGt)], 'sseldd', 'z e. %s' % D0)
    ez = w.s([w.s([], 'vex', 'z e. _V'), w.s([w.s([], 'fveq2', '( a = z -> ( F ` a ) = ( F ` z ) )'), w.s([], 'fveq2', '( a = z -> ( G ` a ) = ( G ` z ) )')], 'eqeq12d',
                                            '( a = z -> ( ( F ` a ) = ( G ` a ) <-> ( F ` z ) = ( G ` z ) ) )')], 'elab', '( z e. %s <-> ( F ` z ) = ( G ` z ) )' % D0)
    fz = sz([zd, ez], 'sylib', '( F ` z ) = ( G ` z )')
    alz = s2([fz], 'ralrimiva', 'A. z e. %s ( F ` z ) = ( G ` z )' % SEGt)
    cc = s2([lift(w, cr, At)], 'recnd', 'C e. CC'); ic = a1c(w, At, 'ax-icn', '_i e. CC'); tc = s2([trp], 'rpcnd', 't e. CC')
    ac = s2([cc, s2([ic, s2([tc], 'negcld', '-u t e. CC')], 'mulcld', '( _i x. -u t ) e. CC')], 'addcld', '%s e. CC' % a)
    bc = s2([cc, s2([ic, tc], 'mulcld', '( _i x. t ) e. CC')], 'addcld', '%s e. CC' % b)
    le = s2([s2([s2([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (a, b)), s2([lift(w, fv, At), lift(w, gv, At)], 'jca', '( F e. _V /\\ G e. _V )')], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. _V /\\ G e. _V ) )' % (a, b)), alz, w.inst('linteq')], 'syl2anc', '%s = %s' % (LI('F', 'C'), LI('G', 'C')))
    me = st([le], 'mpteq2dva', '%s = %s' % (VLF('F', 'C'), VLF('G', 'C')))
    w.qed([me], 'fveq2d', STATEMENTS['z6vleq'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6segd, z6e4lim, z6half, z6kalg, z6vltail, z6vlex, z6vlt, z6vlcvg, z6vleq]:
        if want(f.__name__):
            run(f())
