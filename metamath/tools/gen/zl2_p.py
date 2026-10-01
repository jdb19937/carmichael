"""ZL2 section P: Phragmen-Lindeloef with the Gaussian and power normalizers
(zl2hent, zl2plnv, zl2plng, zl2plnh, zl2pln).
`MM_DB=sorties/zl2.mm python3 tools/gen/zl2_p.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl2lib import *
from lin import linarith, nlinarith
from zl1lib import mptv as mptval_
import num

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'

# ---------------------------------------------------------------- zl2hent
if __name__ == '__main__' and (not only or 'zl2hent' in only):
    w = W('zl2hent', 'An entire function restricted to an open set is holomorphic there ( ~ rescncf , ~ dvres , ~ isopn3i ).')
    G = '( z e. CC |-> A )'
    R = '( z e. D |-> A )'
    A0 = '( ( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) ) /\\ D e. %s )' % (G, G, TOP)
    gc = D(w, A0, 'simpll', [], '%s e. ( CC -cn-> CC )' % G)
    gd = D(w, A0, 'simplr', [], 'CC C_ dom ( CC _D %s )' % G)
    do = D(w, A0, 'simpr', [], 'D e. %s' % TOP)
    dss = opnss(w, A0, do, 'D')
    rs = w.s([dss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` D ) = %s )' % (A0, G, R))
    rc = w.s([dss, gc, w.inst('rescncf')], 'sylc', '( %s -> ( %s |` D ) e. ( D -cn-> CC ) )' % (A0, G))
    gf = w.s([gc, w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (A0, G))
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    tt = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    ssc = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
    idv = w.s([e, tt], 'dvres', '( ( ( CC C_ CC /\\ %s : CC --> CC ) /\\ ( CC C_ CC /\\ D C_ CC ) ) -> ( CC _D ( %s |` D ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` D ) ) )'
            % (G, G, G, TOP))
    dv = w.s([w.s([ssc, gf], 'jca', '( %s -> ( CC C_ CC /\\ %s : CC --> CC ) )' % (A0, G)), w.s([ssc, dss], 'jca', '( %s -> ( CC C_ CC /\\ D C_ CC ) )' % A0), idv],
             'syl2anc', '( %s -> ( CC _D ( %s |` D ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` D ) ) )' % (A0, G, G, TOP))
    ct = w.s([w.s([e], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP))
    io = w.s([ct, do, w.inst('isopn3i')], 'syl2anc', '( %s -> ( ( int ` %s ) ` D ) = D )' % (A0, TOP))
    dv2 = w.s([dv, w.s([io], 'reseq2d', '( %s -> ( ( CC _D %s ) |` ( ( int ` %s ) ` D ) ) = ( ( CC _D %s ) |` D ) )' % (A0, G, TOP, G))], 'eqtrd',
              '( %s -> ( CC _D ( %s |` D ) ) = ( ( CC _D %s ) |` D ) )' % (A0, G, G))
    dm1 = w.s([dv2], 'dmeqd', '( %s -> dom ( CC _D ( %s |` D ) ) = dom ( ( CC _D %s ) |` D ) )' % (A0, G, G))
    dm2 = w.s([w.s([], 'dmres', 'dom ( ( CC _D %s ) |` D ) = ( D i^i dom ( CC _D %s ) )' % (G, G))], 'a1i',
              '( %s -> dom ( ( CC _D %s ) |` D ) = ( D i^i dom ( CC _D %s ) ) )' % (A0, G, G))
    sdd = w.s([dss, gd], 'sstrd', '( %s -> D C_ dom ( CC _D %s ) )' % (A0, G))
    sin = w.s([w.s([w.s([], 'ssid', 'D C_ D')], 'a1i', '( %s -> D C_ D )' % A0), sdd], 'ssind', '( %s -> D C_ ( D i^i dom ( CC _D %s ) ) )' % (A0, G))
    dmq = w.s([dm1, dm2], 'eqtrd', '( %s -> dom ( CC _D ( %s |` D ) ) = ( D i^i dom ( CC _D %s ) ) )' % (A0, G, G))
    sd2 = w.s([sin, dmq], 'sseqtrrd', '( %s -> D C_ dom ( CC _D ( %s |` D ) ) )' % (A0, G))
    # rewrite ( G |` D ) as R
    c1 = w.s([rc, w.s([rs], 'eleq1d', '( %s -> ( ( %s |` D ) e. ( D -cn-> CC ) <-> %s e. ( D -cn-> CC ) ) )' % (A0, G, R))], 'mpbid',
             '( %s -> %s e. ( D -cn-> CC ) )' % (A0, R))
    c2 = w.s([sd2, w.s([w.s([w.s([rs], 'oveq2d', '( %s -> ( CC _D ( %s |` D ) ) = ( CC _D %s ) )' % (A0, G, R))], 'dmeqd',
                             '( %s -> dom ( CC _D ( %s |` D ) ) = dom ( CC _D %s ) )' % (A0, G, R))], 'sseq2d',
                       '( %s -> ( D C_ dom ( CC _D ( %s |` D ) ) <-> D C_ dom ( CC _D %s ) ) )' % (A0, G, R))], 'mpbid',
             '( %s -> D C_ dom ( CC _D %s ) )' % (A0, R))
    w.qed([c1, c2], 'jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) )' % (A0, R, R))
    go(w, only)

# ---------------------------------------------------------------- zl2plnv: modulus of the normalized value
if __name__ == '__main__' and (not only or 'zl2plnv' in only):
    w = W('zl2plnv', 'The modulus of a value times the Gaussian and power normalizers '
          '` e ^ ( ( Z - W ) ^ 2 ) e ^ ( ( Z - P ) C ) ` ( ~ zl2ngau , ~ zl2npow ).')
    A = '( ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) /\\ ( Z e. CC /\\ V e. CC ) )'
    wc = D(w, A, 'simpll', [], 'W e. CC')
    pr = D(w, A, 'simplr', [], '( P e. RR /\\ C e. RR )')
    prr = D(w, A, 'simpld', [pr], 'P e. RR')
    cr = D(w, A, 'simprd', [pr], 'C e. RR')
    zc = D(w, A, 'simprl', [], 'Z e. CC')
    vc = D(w, A, 'simprr', [], 'V e. CC')
    pc = D(w, A, 'recnd', [prr], 'P e. CC')
    cc = D(w, A, 'recnd', [cr], 'C e. CC')
    E1 = '( exp ` ( ( Z - W ) ^ 2 ) )'
    E2 = '( exp ` ( ( Z - P ) x. C ) )'
    e1c = D(w, A, 'efcld', [D(w, A, 'sqcld', [D(w, A, 'subcld', [zc, wc], '( Z - W ) e. CC')], '( ( Z - W ) ^ 2 ) e. CC')], '%s e. CC' % E1)
    zp = D(w, A, 'subcld', [zc, pc], '( Z - P ) e. CC')
    e2c = D(w, A, 'efcld', [D(w, A, 'mulcld', [zp, cc], '( ( Z - P ) x. C ) e. CC')], '%s e. CC' % E2)
    RW = '( ( ( ( Re ` Z ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` Z ) - ( Im ` W ) ) ^ 2 ) )'
    RP = '( ( ( Re ` Z ) - P ) x. C )'
    a1_ = D(w, A, 'absmuld', [vc, D(w, A, 'mulcld', [e1c, e2c], '( %s x. %s ) e. CC' % (E1, E2))],
            '( abs ` ( V x. ( %s x. %s ) ) ) = ( ( abs ` V ) x. ( abs ` ( %s x. %s ) ) )' % (E1, E2, E1, E2))
    a2 = D(w, A, 'absmuld', [e1c, e2c], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (E1, E2, E1, E2))
    g1 = w.s([zc, wc, w.inst('zl2ngau')], 'syl2anc', '( %s -> ( abs ` %s ) = ( exp ` %s ) )' % (A, E1, RW))
    g2 = w.s([zp, cr, w.inst('zl2npow')], 'syl2anc', '( %s -> ( abs ` %s ) = ( exp ` ( ( Re ` ( Z - P ) ) x. C ) ) )' % (A, E2))
    r1 = D(w, A, 'resubd', [zc, pc], '( Re ` ( Z - P ) ) = ( ( Re ` Z ) - ( Re ` P ) )')
    r2 = E(w, A, 'oveq2d', [D(w, A, 'rered', [prr], '( Re ` P ) = P')], '( ( Re ` Z ) - ( Re ` P ) )', '( ( Re ` Z ) - P )')
    r3 = w.s([r1, r2], 'eqtrd', '( %s -> ( Re ` ( Z - P ) ) = ( ( Re ` Z ) - P ) )' % A)
    r4 = E(w, A, 'fveq2d', [E(w, A, 'oveq1d', [r3], '( ( Re ` ( Z - P ) ) x. C )', RP)], '( exp ` ( ( Re ` ( Z - P ) ) x. C ) )', '( exp ` %s )' % RP)
    g2b = w.s([g2, r4], 'eqtrd', '( %s -> ( abs ` %s ) = ( exp ` %s ) )' % (A, E2, RP))
    a3 = E(w, A, 'oveq12d', [g1, g2b], '( ( abs ` %s ) x. ( abs ` %s ) )' % (E1, E2), '( ( exp ` %s ) x. ( exp ` %s ) )' % (RW, RP))
    a4 = E(w, A, 'oveq2d', [w.s([a2, a3], 'eqtrd', '( %s -> ( abs ` ( %s x. %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (A, E1, E2, RW, RP))],
           '( ( abs ` V ) x. ( abs ` ( %s x. %s ) ) )' % (E1, E2), '( ( abs ` V ) x. ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (RW, RP))
    av = D(w, A, 'abscld', [vc], '( abs ` V ) e. RR')
    x1 = D(w, A, 'recnd', [av], '( abs ` V ) e. CC')
    zr = D(w, A, 'recld', [zc], '( Re ` Z ) e. RR')
    wr = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    rwr = D(w, A, 'resubcld', [D(w, A, 'resqcld', [D(w, A, 'resubcld', [zr, wr], '( ( Re ` Z ) - ( Re ` W ) ) e. RR')], '( ( ( Re ` Z ) - ( Re ` W ) ) ^ 2 ) e. RR'),
                               D(w, A, 'resqcld', [D(w, A, 'resubcld', [D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR'), D(w, A, 'imcld', [wc], '( Im ` W ) e. RR')],
                                                     '( ( Im ` Z ) - ( Im ` W ) ) e. RR')], '( ( ( Im ` Z ) - ( Im ` W ) ) ^ 2 ) e. RR')], '%s e. RR' % RW)
    rpr = D(w, A, 'remulcld', [D(w, A, 'resubcld', [zr, prr], '( ( Re ` Z ) - P ) e. RR'), cr], '%s e. RR' % RP)
    x2 = D(w, A, 'recnd', [D(w, A, 'reefcld', [rwr], '( exp ` %s ) e. RR' % RW)], '( exp ` %s ) e. CC' % RW)
    x3 = D(w, A, 'recnd', [D(w, A, 'reefcld', [rpr], '( exp ` %s ) e. RR' % RP)], '( exp ` %s ) e. CC' % RP)
    a5 = D(w, A, 'mulassd', [x1, x2, x3], '( ( ( abs ` V ) x. ( exp ` %s ) ) x. ( exp ` %s ) ) = ( ( abs ` V ) x. ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (RW, RP, RW, RP))
    chain(w, A, ['( abs ` ( V x. ( %s x. %s ) ) )' % (E1, E2), '( ( abs ` V ) x. ( abs ` ( %s x. %s ) ) )' % (E1, E2),
                 '( ( abs ` V ) x. ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (RW, RP), '( ( ( abs ` V ) x. ( exp ` %s ) ) x. ( exp ` %s ) )' % (RW, RP)],
          [a1_, a4, ('r', a5)], name='qed')
    go(w, only)


def ebounds(w, A, x, xr):
    """( A -> -u ( abs ` x ) <_ x ) and ( A -> ( abs ` x ) e. RR ), from xr: ( A -> x e. RR )"""
    ax = D(w, A, 'abscld', [D(w, A, 'recnd', [xr], '%s e. CC' % x)], '( abs ` %s ) e. RR' % x)
    le = D(w, A, 'leidd', [ax], '( abs ` %s ) <_ ( abs ` %s )' % (x, x))
    bi = D(w, A, 'absled', [xr, ax], '( ( abs ` %s ) <_ ( abs ` %s ) <-> ( -u ( abs ` %s ) <_ %s /\\ %s <_ ( abs ` %s ) ) )' % (x, x, x, x, x, x))
    both = w.s([le, bi], 'mpbid', '( %s -> ( -u ( abs ` %s ) <_ %s /\\ %s <_ ( abs ` %s ) ) )' % (A, x, x, x, x))
    return D(w, A, 'simpld', [both], '-u ( abs ` %s ) <_ %s' % (x, x)), D(w, A, 'simprd', [both], '%s <_ ( abs ` %s )' % (x, x)), ax


def strip_mem(w, A, Z, zs, xr, yr, X='X', Y='Y'):
    """from zs: ( A -> Z e. STRIP(X,Y) ): Z e. CC, Re Z e. RR, X <_ Re Z, Re Z <_ Y"""
    el = w.s([zs, w.s([], 'elstr', '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( %s [,] %s ) ) )' % (Z, STRIP(X, Y), Z, Z, X, Y))], 'sylib',
             '( %s -> ( %s e. CC /\\ ( Re ` %s ) e. ( %s [,] %s ) ) )' % (A, Z, Z, X, Y))
    zc = D(w, A, 'simpld', [el], '%s e. CC' % Z)
    ri = D(w, A, 'simprd', [el], '( Re ` %s ) e. ( %s [,] %s )' % (Z, X, Y))
    bi = w.s([xr, yr, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Re ` %s ) e. ( %s [,] %s ) <-> ( ( Re ` %s ) e. RR /\\ %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) ) )'
             % (A, Z, X, Y, Z, X, Z, Z, Y))
    t3 = w.s([ri, bi], 'mpbid', '( %s -> ( ( Re ` %s ) e. RR /\\ %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ %s ) )' % (A, Z, X, Z, Z, Y))
    return (zc, D(w, A, 'simp1d', [t3], '( Re ` %s ) e. RR' % Z), D(w, A, 'simp2d', [t3], '%s <_ ( Re ` %s )' % (X, Z)),
            D(w, A, 'simp3d', [t3], '( Re ` %s ) <_ %s' % (Z, Y)))


# ---------------------------------------------------------------- zl2plng: the normalizer is bounded on the strip
if __name__ == '__main__' and (not only or 'zl2plng' in only):
    w = W('zl2plng', 'On the strip ` X <_ Re z <_ Y ` the normalizer ` e ^ ( ( z - W ) ^ 2 ) e ^ ( ( z - P ) C ) ` is bounded by '
          '` e ^ ( ( Y - X ) ^ 2 + ( | X | + | Y | + | P | ) | C | ) ` ( the growth block of Lean`s two Phragmen-Lindeloef applications).')
    S = STRIP('X', 'Y')
    A = '( ( ( X e. RR /\\ Y e. RR ) /\\ ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) ) /\\ Z e. %s )' % (S, S)
    xr = D(w, A, 'simplll', [], 'X e. RR')
    yr = D(w, A, 'simpllr', [], 'Y e. RR')
    ws = D(w, A, 'simplrl', [], 'W e. %s' % S)
    pcr = D(w, A, 'simplrr', [], '( P e. RR /\\ C e. RR )')
    pr = D(w, A, 'simpld', [pcr], 'P e. RR')
    cr = D(w, A, 'simprd', [pcr], 'C e. RR')
    zs = D(w, A, 'simpr', [], 'Z e. %s' % S)
    zc, zr, xz, zy = strip_mem(w, A, 'Z', zs, xr, yr)
    wc, wr, xw, wy = strip_mem(w, A, 'W', ws, xr, yr)
    NZ = NRM('Z')
    RW = '( ( ( ( Re ` Z ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` Z ) - ( Im ` W ) ) ^ 2 ) )'
    RP = '( ( ( Re ` Z ) - P ) x. C )'
    one = a1(w, A, 'ax-1cn', '1 e. CC')
    v = w.s([w.s([wc, pcr], 'jca', '( %s -> ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) )' % A), w.s([zc, one], 'jca', '( %s -> ( Z e. CC /\\ 1 e. CC ) )' % A),
             w.inst('zl2plnv')], 'syl2anc', '( %s -> ( abs ` ( 1 x. %s ) ) = ( ( ( abs ` 1 ) x. ( exp ` %s ) ) x. ( exp ` %s ) ) )' % (A, NZ, RW, RP))
    E1 = '( exp ` ( ( Z - W ) ^ 2 ) )'
    E2 = '( exp ` ( ( Z - P ) x. C ) )'
    pc = D(w, A, 'recnd', [pr], 'P e. CC')
    cc = D(w, A, 'recnd', [cr], 'C e. CC')
    e1c = D(w, A, 'efcld', [D(w, A, 'sqcld', [D(w, A, 'subcld', [zc, wc], '( Z - W ) e. CC')], '( ( Z - W ) ^ 2 ) e. CC')], '%s e. CC' % E1)
    e2c = D(w, A, 'efcld', [D(w, A, 'mulcld', [D(w, A, 'subcld', [zc, pc], '( Z - P ) e. CC'), cc], '( ( Z - P ) x. C ) e. CC')], '%s e. CC' % E2)
    nzc = D(w, A, 'mulcld', [e1c, e2c], '%s e. CC' % NZ)
    u1 = E(w, A, 'fveq2d', [D(w, A, 'mullidd', [nzc], '( 1 x. %s ) = %s' % (NZ, NZ))], '( abs ` ( 1 x. %s ) )' % NZ, '( abs ` %s )' % NZ)
    wr_ = D(w, A, 'recld', [wc], '( Re ` W ) e. RR')
    rwr = D(w, A, 'resubcld', [D(w, A, 'resqcld', [D(w, A, 'resubcld', [zr, wr], '( ( Re ` Z ) - ( Re ` W ) ) e. RR')], '( ( ( Re ` Z ) - ( Re ` W ) ) ^ 2 ) e. RR'),
                               D(w, A, 'resqcld', [D(w, A, 'resubcld', [D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR'), D(w, A, 'imcld', [wc], '( Im ` W ) e. RR')],
                                                     '( ( Im ` Z ) - ( Im ` W ) ) e. RR')], '( ( ( Im ` Z ) - ( Im ` W ) ) ^ 2 ) e. RR')], '%s e. RR' % RW)
    rpr = D(w, A, 'remulcld', [D(w, A, 'resubcld', [zr, pr], '( ( Re ` Z ) - P ) e. RR'), cr], '%s e. RR' % RP)
    erw = D(w, A, 'recnd', [D(w, A, 'reefcld', [rwr], '( exp ` %s ) e. RR' % RW)], '( exp ` %s ) e. CC' % RW)
    u2 = E(w, A, 'oveq1d', [a1(w, A, 'abs1', '( abs ` 1 ) = 1')], '( ( abs ` 1 ) x. ( exp ` %s ) )' % RW, '( 1 x. ( exp ` %s ) )' % RW)
    u3 = D(w, A, 'mullidd', [erw], '( 1 x. ( exp ` %s ) ) = ( exp ` %s )' % (RW, RW))
    u4 = E(w, A, 'oveq1d', [w.s([u2, u3], 'eqtrd', '( %s -> ( ( abs ` 1 ) x. ( exp ` %s ) ) = ( exp ` %s ) )' % (A, RW, RW))],
           '( ( ( abs ` 1 ) x. ( exp ` %s ) ) x. ( exp ` %s ) )' % (RW, RP), '( ( exp ` %s ) x. ( exp ` %s ) )' % (RW, RP))
    u5 = w.s([efadd_(w, A, RW, RP, D(w, A, 'recnd', [rwr], '%s e. CC' % RW), D(w, A, 'recnd', [rpr], '%s e. CC' % RP))], 'eqcomd',
             '( %s -> ( ( exp ` %s ) x. ( exp ` %s ) ) = ( exp ` ( %s + %s ) ) )' % (A, RW, RP, RW, RP))
    val = chain(w, A, ['( abs ` %s )' % NZ, '( abs ` ( 1 x. %s ) )' % NZ, '( ( ( abs ` 1 ) x. ( exp ` %s ) ) x. ( exp ` %s ) )' % (RW, RP),
                       '( ( exp ` %s ) x. ( exp ` %s ) )' % (RW, RP), '( exp ` ( %s + %s ) )' % (RW, RP)], [('r', u1), v, u4, u5])
    # RW <_ ( Y - X ) ^ 2
    a_ = '( Re ` Z )'; b_ = '( Re ` W )'
    f1 = linarith(w, A, [zy, xw], '0 <_ ( ( Y - %s ) + ( %s - X ) )' % (a_, b_), leaves={'X': xr, 'Y': yr, a_: zr, b_: wr})
    f2 = linarith(w, A, [wy, xz], '0 <_ ( ( Y - %s ) + ( %s - X ) )' % (b_, a_), leaves={'X': xr, 'Y': yr, a_: zr, b_: wr})
    g1r = D(w, A, 'readdcld', [D(w, A, 'resubcld', [yr, zr], '( Y - %s ) e. RR' % a_), D(w, A, 'resubcld', [wr, xr], '( %s - X ) e. RR' % b_)],
            '( ( Y - %s ) + ( %s - X ) ) e. RR' % (a_, b_))
    g2r = D(w, A, 'readdcld', [D(w, A, 'resubcld', [yr, wr], '( Y - %s ) e. RR' % b_), D(w, A, 'resubcld', [zr, xr], '( %s - X ) e. RR' % a_)],
            '( ( Y - %s ) + ( %s - X ) ) e. RR' % (b_, a_))
    pp = D(w, A, 'mulge0d', [g1r, g2r, f1, f2], '0 <_ ( ( ( Y - %s ) + ( %s - X ) ) x. ( ( Y - %s ) + ( %s - X ) ) )' % (a_, b_, b_, a_))
    IZW = '( ( Im ` Z ) - ( Im ` W ) )'
    imz = D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR')
    imw = D(w, A, 'imcld', [wc], '( Im ` W ) e. RR')
    izr = D(w, A, 'resubcld', [imz, imw], '%s e. RR' % IZW)
    sq0 = D(w, A, 'sqge0d', [izr], '0 <_ ( %s ^ 2 )' % IZW)
    cl = Closure(w, A, {'X': ('RR', xr), 'Y': ('RR', yr), a_: ('RR', zr), b_: ('RR', wr), '( Im ` Z )': ('RR', imz), '( Im ` W )': ('RR', imw)})
    h1 = nlinarith(w, A, [pp, sq0], '%s <_ ( ( Y - X ) ^ 2 )' % RW, closure=cl)
    # RP <_ ( | X | + ( | Y | + | P | ) ) | C |
    nx, xa, axr = ebounds(w, A, 'X', xr)
    ny, ya, ayr = ebounds(w, A, 'Y', yr)
    np_, pa, apr = ebounds(w, A, 'P', pr)
    BND = '( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` P ) ) )'
    M2 = '( ( abs ` X ) + ( abs ` Y ) )'
    cl2 = Closure(w, A, {'X': ('RR', xr), 'Y': ('RR', yr), a_: ('RR', zr), '( abs ` X )': ('RR', axr), '( abs ` Y )': ('RR', ayr), '( abs ` P )': ('RR', apr)})
    ay0 = D(w, A, 'absge0d', [D(w, A, 'recnd', [yr], 'Y e. CC')], '0 <_ ( abs ` Y )')
    ax0 = D(w, A, 'absge0d', [D(w, A, 'recnd', [xr], 'X e. CC')], '0 <_ ( abs ` X )')
    l1 = linarith(w, A, [nx, xz, ay0], '-u %s <_ %s' % (M2, a_), closure=cl2)
    l2 = linarith(w, A, [zy, ya, ax0], '%s <_ %s' % (a_, M2), closure=cl2)
    m2r = D(w, A, 'readdcld', [axr, ayr], '%s e. RR' % M2)
    az = w.s([w.s([l1, l2], 'jca', '( %s -> ( -u %s <_ %s /\\ %s <_ %s ) )' % (A, M2, a_, a_, M2)), D(w, A, 'absled', [zr, m2r],
              '( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) )' % (a_, M2, M2, a_, a_, M2))], 'mpbird', '( %s -> ( abs ` %s ) <_ %s )' % (A, a_, M2))
    T_ = '( %s - P )' % a_
    tr = D(w, A, 'resubcld', [zr, pr], '%s e. RR' % T_)
    tc = D(w, A, 'recnd', [tr], '%s e. CC' % T_)
    at = D(w, A, 'abscld', [tc], '( abs ` %s ) e. RR' % T_)
    tri = D(w, A, 'abs2dif2d', [D(w, A, 'recnd', [zr], '%s e. CC' % a_), pc], '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` P ) )' % (T_, a_))
    aza = D(w, A, 'abscld', [D(w, A, 'recnd', [zr], '%s e. CC' % a_)], '( abs ` %s ) e. RR' % a_)
    cl2.leaf('( abs ` %s )' % a_, 'RR', aza); cl2.leaf('( abs ` %s )' % T_, 'RR', at)
    tb = linarith(w, A, [tri, az], '( abs ` %s ) <_ %s' % (T_, BND), closure=cl2)
    bndr = D(w, A, 'readdcld', [axr, D(w, A, 'readdcld', [ayr, apr], '( ( abs ` Y ) + ( abs ` P ) ) e. RR')], '%s e. RR' % BND)
    acr = D(w, A, 'abscld', [cc], '( abs ` C ) e. RR')
    ac0 = D(w, A, 'absge0d', [cc], '0 <_ ( abs ` C )')
    mb = D(w, A, 'lemul1ad', [at, bndr, acr, ac0, tb], '( ( abs ` %s ) x. ( abs ` C ) ) <_ ( %s x. ( abs ` C ) )' % (T_, BND))
    ab = D(w, A, 'absmuld', [tc, cc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` C ) )' % (RP, T_))
    lb = D(w, A, 'leabsd', [rpr], '%s <_ ( abs ` %s )' % (RP, RP))
    lb2 = w.s([lb, ab], 'breqtrd', '( %s -> %s <_ ( ( abs ` %s ) x. ( abs ` C ) ) )' % (A, RP, T_))
    h2 = w.s([rpr, D(w, A, 'remulcld', [at, acr], '( ( abs ` %s ) x. ( abs ` C ) ) e. RR' % T_), D(w, A, 'remulcld', [bndr, acr], '( %s x. ( abs ` C ) ) e. RR' % BND),
              lb2, mb], 'letrd', '( %s -> %s <_ ( %s x. ( abs ` C ) ) )' % (A, RP, BND))
    YX = '( ( Y - X ) ^ 2 )'
    yxr = D(w, A, 'resqcld', [D(w, A, 'resubcld', [yr, xr], '( Y - X ) e. RR')], '%s e. RR' % YX)
    s12 = D(w, A, 'le2addd', [rwr, rpr, yxr, D(w, A, 'remulcld', [bndr, acr], '( %s x. ( abs ` C ) ) e. RR' % BND), h1, h2],
            '( %s + %s ) <_ ( %s + ( %s x. ( abs ` C ) ) )' % (RW, RP, YX, BND))
    ef = efle_(w, A, '( %s + %s )' % (RW, RP), '( %s + ( %s x. ( abs ` C ) ) )' % (YX, BND), D(w, A, 'readdcld', [rwr, rpr], '( %s + %s ) e. RR' % (RW, RP)),
               D(w, A, 'readdcld', [yxr, D(w, A, 'remulcld', [bndr, acr], '( %s x. ( abs ` C ) ) e. RR' % BND)], '( %s + ( %s x. ( abs ` C ) ) ) e. RR' % (YX, BND)), s12)
    w.qed([val, ef], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( exp ` ( %s + ( %s x. ( abs ` C ) ) ) ) )' % (A, NZ, YX, BND))
    go(w, only)


def holeq_(w, ante, M1, M2, Dm, hol, eq):
    """( ante -> HOL(M2,Dm) ) from hol: ( ante -> HOL(M1,Dm) ) and eq: ( ante -> M1 = M2 )"""
    b1 = w.s([eq], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (ante, M1, Dm, M2, Dm))
    d1 = w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (ante, M1, M2))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (ante, M1, M2))
    b2 = w.s([d1], 'sseq2d', '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (ante, Dm, M1, Dm, M2))
    bb = w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (ante, HOL(M1, Dm), HOL(M2, Dm)))
    return w.s([hol, bb], 'mpbid', '( %s -> %s )' % (ante, HOL(M2, Dm)))


def mpteq_(w, ante, x, X, b1, b2, pt):
    """( ante -> ( x e. X |-> b1 ) = ( x e. X |-> b2 ) ) from pt: ( ( ante /\\ x e. X ) -> b1 = b2 )"""
    return w.s([pt], 'mpteq2dva', '( %s -> ( %s e. %s |-> %s ) = ( %s e. %s |-> %s ) )' % (ante, x, X, b1, x, X, b2))


def ent_lin(w, A0, V, vc):
    """( A0 -> ( t e. CC |-> ( t - V ) ) entire ) (z6ehdv; derivative ( 1 - 0 ) by dvmptsub)"""
    At = '( %s /\\ t e. CC )' % A0
    tc = D(w, At, 'simpr', [], 't e. CC')
    vct = w.s([vc], 'adantr', '( %s -> %s e. CC )' % (At, V))
    ptc = D(w, At, 'subcld', [tc, vct], '( t - %s ) e. CC' % V)
    ral = w.s([ptc], 'ralrimiva', '( %s -> A. t e. CC ( t - %s ) e. CC )' % (A0, V))
    s = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % At)
    zer = w.s([w.s([], '0cn', '0 e. CC')], 'a1i', '( %s -> 0 e. CC )' % At)
    did = w.s([s], 'dvmptid', '( %s -> ( CC _D ( t e. CC |-> t ) ) = ( t e. CC |-> 1 ) )' % A0)
    dc = w.s([s, vc], 'dvmptc', '( %s -> ( CC _D ( t e. CC |-> %s ) ) = ( t e. CC |-> 0 ) )' % (A0, V))
    dv = w.s([s, tc, one, did, vct, zer, dc], 'dvmptsub', '( %s -> ( CC _D ( t e. CC |-> ( t - %s ) ) ) = ( t e. CC |-> ( 1 - 0 ) ) )' % (A0, V))
    b = w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'subcli', '( 1 - 0 ) e. CC')], 'a1i', '( %s -> ( 1 - 0 ) e. CC )' % At)],
            'ralrimiva', '( %s -> A. t e. CC ( 1 - 0 ) e. CC )' % A0)
    MP = '( t e. CC |-> ( t - %s ) )' % V
    return w.s([ral, dv, b, w.inst('z6ehdv')], 'syl12anc', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) ) )' % (A0, MP, MP))


# ---------------------------------------------------------------- zl2plnh: the normalized function is holomorphic
if __name__ == '__main__' and (not only or 'zl2plnh' in only):
    w = W('zl2plnh', 'The function ` F ( z ) e ^ ( ( z - W ) ^ 2 ) e ^ ( ( z - P ) C ) ` is holomorphic wherever ` F ` is '
          '( ~ z6ehdv , ~ z6ehmul , ~ z6hexp , ~ holmul , ~ zl2hent ; Lean`s ` hdiff ` blocks).')
    A0 = PLNH
    hf = D(w, A0, 'simplr', [], '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D )' % STRIP('X', 'Y'))
    f1 = D(w, A0, 'simp1d', [hf], 'F e. ( D -cn-> CC )')
    f2 = D(w, A0, 'simp2d', [hf], 'D C_ dom ( CC _D F )')
    hol = w.s([f1, f2], 'jca', '( %s -> %s )' % (A0, HOL('F', 'D')))
    do = w.s([hol, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
    wc = D(w, A0, 'simprl', [], 'W e. CC')
    pcr = D(w, A0, 'simprr', [], '( P e. RR /\\ C e. RR )')
    pc = D(w, A0, 'recnd', [D(w, A0, 'simpld', [pcr], 'P e. RR')], 'P e. CC')
    cc = D(w, A0, 'recnd', [D(w, A0, 'simprd', [pcr], 'C e. RR')], 'C e. CC')
    HC = lambda M: HOL(M, 'CC')
    # ( t - W ) ^ 2 and ( t - P ) x. C, entire
    lw = ent_lin(w, A0, 'W', wc)
    lp = ent_lin(w, A0, 'P', pc)
    sqm = w.s([lw, lw], 'z6ehmul', '( %s -> %s )' % (A0, HC('( t e. CC |-> ( ( t - W ) x. ( t - W ) ) )')))
    At = '( %s /\\ t e. CC )' % A0
    twc = D(w, At, 'subcld', [D(w, At, 'simpr', [], 't e. CC'), w.s([wc], 'adantr', '( %s -> W e. CC )' % At)], '( t - W ) e. CC')
    sqe = mpteq_(w, A0, 't', 'CC', '( ( t - W ) x. ( t - W ) )', '( ( t - W ) ^ 2 )',
                 w.s([D(w, At, 'sqvald', [twc], '( ( t - W ) ^ 2 ) = ( ( t - W ) x. ( t - W ) )')], 'eqcomd', '( %s -> ( ( t - W ) x. ( t - W ) ) = ( ( t - W ) ^ 2 ) )' % At))
    P1 = '( t e. CC |-> ( ( t - W ) ^ 2 ) )'
    h1 = holeq_(w, A0, '( t e. CC |-> ( ( t - W ) x. ( t - W ) ) )', P1, 'CC', sqm, sqe)
    cm = w.s([cc], 'z6ehc', '( %s -> %s )' % (A0, HC('( t e. CC |-> C )')))
    P2 = '( t e. CC |-> ( ( t - P ) x. C ) )'
    h2 = w.s([lp, cm], 'z6ehmul', '( %s -> %s )' % (A0, HC(P2)))
    # exp of each (z6hexp at D = CC, binder s)
    As = '( %s /\\ s e. CC )' % A0
    sc = D(w, As, 'simpr', [], 's e. CC')
    def expm(Pm, body_t, hol_):
        e = w.s([hol_, w.inst('z6hexp')], 'syl', '( %s -> %s )' % (A0, HC('( s e. CC |-> ( exp ` ( %s ` s ) ) )' % Pm)))
        v, val = mptval_(w, As, 't', 'CC', body_t, 's', sc)
        eq = mpteq_(w, A0, 's', 'CC', '( exp ` ( %s ` s ) )' % Pm, '( exp ` %s )' % val, w.s([v], 'fveq2d', '( %s -> ( exp ` ( %s ` s ) ) = ( exp ` %s ) )' % (As, Pm, val)))
        M2 = '( s e. CC |-> ( exp ` %s ) )' % val
        return holeq_(w, A0, '( s e. CC |-> ( exp ` ( %s ` s ) ) )' % Pm, M2, 'CC', e, eq), M2, val
    g1, E1m, v1 = expm(P1, '( ( t - W ) ^ 2 )', h1)
    g2, E2m, v2 = expm(P2, '( ( t - P ) x. C )', h2)
    # product on CC, binder y
    pm = w.s([g1, g2, w.inst('holmul')], 'syl2anc', '( %s -> %s )' % (A0, HC('( y e. CC |-> ( ( %s ` y ) x. ( %s ` y ) ) )' % (E1m, E2m))))
    Ay = '( %s /\\ y e. CC )' % A0
    yc = D(w, Ay, 'simpr', [], 'y e. CC')
    va, a_ = mptval_(w, Ay, 's', 'CC', '( exp ` %s )' % v1, 'y', yc)
    vb, b_ = mptval_(w, Ay, 's', 'CC', '( exp ` %s )' % v2, 'y', yc)
    NY = NRM('y')
    assert '( %s x. %s )' % (a_, b_) == NY, (a_, b_, NY)
    pe = mpteq_(w, A0, 'y', 'CC', '( ( %s ` y ) x. ( %s ` y ) )' % (E1m, E2m), NY,
                E(w, Ay, 'oveq12d', [va, vb], '( ( %s ` y ) x. ( %s ` y ) )' % (E1m, E2m), NY))
    NYM = '( y e. CC |-> %s )' % NY
    hn = holeq_(w, A0, '( y e. CC |-> ( ( %s ` y ) x. ( %s ` y ) ) )' % (E1m, E2m), NYM, 'CC', pm, pe)
    # restrict to D
    GD = '( y e. D |-> %s )' % NY
    hd = w.s([hn, do, w.inst('zl2hent')], 'syl2anc', '( %s -> %s )' % (A0, HOL(GD, 'D')))
    # times F
    fm = w.s([hol, hd, w.inst('holmul')], 'syl2anc', '( %s -> %s )' % (A0, HOL('( z e. D |-> ( ( F ` z ) x. ( %s ` z ) ) )' % GD, 'D')))
    Az = '( %s /\\ z e. D )' % A0
    zd = D(w, Az, 'simpr', [], 'z e. D')
    vz, cz = mptval_(w, Az, 'y', 'D', NY, 'z', zd)
    fe = mpteq_(w, A0, 'z', 'D', '( ( F ` z ) x. ( %s ` z ) )' % GD, '( ( F ` z ) x. %s )' % cz,
                E(w, Az, 'oveq2d', [vz], '( ( F ` z ) x. ( %s ` z ) )' % GD, '( ( F ` z ) x. %s )' % cz))
    fin = holeq_(w, A0, '( z e. D |-> ( ( F ` z ) x. ( %s ` z ) ) )' % GD, GN, 'D', fm, fe)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)


def inst_ral(w, ante, ralst, x, S, body, T, mem):
    """( ante -> body[x:=T] ) from ralst: ( ante -> A. x e. S body ) and mem: ( ante -> T e. S ) (closed rspcv)"""
    eq = '%s = %s' % (x, T)
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, val = w.wcongr(body, {x: T}, eq, {x: idx})
    r = w.s([st], 'rspcv', '( %s e. %s -> ( A. %s e. %s %s -> %s ) )' % (T, S, x, S, body, val))
    return w.s([mem, ralst, r], 'sylc', '( %s -> %s )' % (ante, val)), val


# ---------------------------------------------------------------- zl2pln: Phragmen-Lindeloef with normalizers
if __name__ == '__main__' and (not only or 'zl2pln' in only):
    w = W('zl2pln', 'Phragmen-Lindeloef on a vertical strip with the Gaussian and power normalizers: if ` F ` is holomorphic on the strip '
          '` X <_ Re z <_ Y ` with growth ` K e ^ ( B | Im z | ) ` and ` | F ( z ) | e ^ ( ( E - Re W ) ^ 2 - ( Im z - Im W ) ^ 2 ) e ^ ( ( E - P ) C ) <_ Q ` '
          'on both edges ` Re z = E ` , then ` | F ( W ) | e ^ ( ( Re W - P ) C ) <_ Q ` ( ~ rectintpl at ~ zl2plnh ; Lean`s two uses of '
          '` PhragmenLindelof.vertical_strip ` ).')
    A = PLNA
    S = STRIP('X', 'Y')
    xy = D(w, A, 'simplll', [], '( X e. RR /\\ Y e. RR )')
    h3 = D(w, A, 'simpllr', [], '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D )' % S)
    gr = D(w, A, 'simplr', [], GRWB('F', S))
    t3 = D(w, A, 'simprl', [], '( W e. %s /\\ ( P e. RR /\\ C e. RR ) /\\ Q e. RR+ )' % S)
    ll = D(w, A, 'simprr', [], '( %s /\\ %s )' % (PLNL('X'), PLNL('Y')))
    xr = D(w, A, 'simpld', [xy], 'X e. RR'); yr = D(w, A, 'simprd', [xy], 'Y e. RR')
    ws = D(w, A, 'simp1d', [t3], 'W e. %s' % S)
    pc_ = D(w, A, 'simp2d', [t3], '( P e. RR /\\ C e. RR )')
    qrp = D(w, A, 'simp3d', [t3], 'Q e. RR+')
    pr = D(w, A, 'simpld', [pc_], 'P e. RR'); cr = D(w, A, 'simprd', [pc_], 'C e. RR')
    kb = D(w, A, 'simpld', [gr], '( K e. RR+ /\\ B e. RR /\\ 0 <_ B )')
    gral = D(w, A, 'simprd', [gr], 'A. z e. %s ( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) )' % S)
    krp = D(w, A, 'simp1d', [kb], 'K e. RR+'); br = D(w, A, 'simp2d', [kb], 'B e. RR'); b0 = D(w, A, 'simp3d', [kb], '0 <_ B')
    wc, wr, xw, wy = strip_mem(w, A, 'W', ws, xr, yr)
    fcn = D(w, A, 'simp1d', [h3], 'F e. ( D -cn-> CC )')
    sd = D(w, A, 'simp3d', [h3], '%s C_ D' % S)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A)
    # the normalized function is holomorphic
    hh = w.s([w.s([xy, h3], 'jca', '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) ) )' % (A, S)),
              w.s([wc, pc_], 'jca', '( %s -> ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) )' % A)], 'jca', '( %s -> %s )' % (A, PLNH))
    gh = w.s([hh, w.inst('zl2plnh')], 'syl', '( %s -> %s )' % (A, HOL(GN, 'D')))
    g1 = D(w, A, 'simpld', [gh], '%s e. ( D -cn-> CC )' % GN)
    g2 = D(w, A, 'simprd', [gh], 'D C_ dom ( CC _D %s )' % GN)
    # values on the strip
    Ay = '( %s /\\ y e. %s )' % (A, S)
    ys = D(w, Ay, 'simpr', [], 'y e. %s' % S)
    yd = w.s([w.s([sd], 'adantr', '( %s -> %s C_ D )' % (Ay, S)), ys], 'sseldd', '( %s -> y e. D )' % Ay)
    NYt = NRM('y')
    gv, gval = mptval_(w, Ay, 'z', 'D', '( ( F ` z ) x. %s )' % NRM('z'), 'y', yd)
    assert gval == '( ( F ` y ) x. %s )' % NYt, gval
    fyc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Ay), yd], 'ffvelcdmd', '( %s -> ( F ` y ) e. CC )' % Ay)
    xry = w.s([xr], 'adantr', '( %s -> X e. RR )' % Ay); yry = w.s([yr], 'adantr', '( %s -> Y e. RR )' % Ay)
    yc, yre, xyy, yyy = strip_mem(w, Ay, 'y', ys, xry, yry)
    pcy = w.s([wc, pc_], 'jca', '( %s -> ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) )' % A)
    RWy = '( ( ( ( Re ` y ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` y ) - ( Im ` W ) ) ^ 2 ) )'
    RPy = '( ( ( Re ` y ) - P ) x. C )'
    mv = w.s([w.s([pcy], 'adantr', '( %s -> ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) )' % Ay), w.s([yc, fyc], 'jca', '( %s -> ( y e. CC /\\ ( F ` y ) e. CC ) )' % Ay),
              w.inst('zl2plnv')], 'syl2anc',
             '( %s -> ( abs ` ( ( F ` y ) x. %s ) ) = ( ( ( abs ` ( F ` y ) ) x. ( exp ` %s ) ) x. ( exp ` %s ) ) )' % (Ay, NYt, RWy, RPy))
    MOD = '( ( ( abs ` ( F ` y ) ) x. ( exp ` %s ) ) x. ( exp ` %s ) )' % (RWy, RPy)
    gmod = w.s([w.s([gv], 'fveq2d', '( %s -> ( abs ` ( %s ` y ) ) = ( abs ` %s ) )' % (Ay, GN, gval)), mv], 'eqtrd',
               '( %s -> ( abs ` ( %s ` y ) ) = %s )' % (Ay, GN, MOD))
    # the two edges
    def edge(Eb, lst):
        Ae = '( %s /\\ ( Re ` y ) = %s )' % (Ay, Eb)
        re_ = D(w, Ae, 'simpr', [], '( Re ` y ) = %s' % Eb)
        st, new = w.rewrite(MOD, {'( Re ` y )': (Eb, re_)}, Ae)
        lh = w.s([w.s([ll], 'adantr', '( %s -> ( %s /\\ %s ) )' % (Ay, PLNL('X'), PLNL('Y')))], lst, '( %s -> %s )' % (Ay, PLNL(Eb)))
        inst, body = inst_ral(w, Ay, lh, 'z', S, PLNL(Eb)[len('A. z e. %s ' % S):], 'y', ys)
        # body: ( ( Re ` y ) = Eb -> ( new ) <_ Q )
        imp = w.s([w.s([inst], 'adantr', '( %s -> %s )' % (Ae, body)), re_], 'mpd', '( %s -> %s <_ Q )' % (Ae, new))
        le = w.s([w.s([w.s([gmod], 'adantr', '( %s -> ( abs ` ( %s ` y ) ) = %s )' % (Ae, GN, MOD)), st], 'eqtrd',
                      '( %s -> ( abs ` ( %s ` y ) ) = %s )' % (Ae, GN, new)), imp], 'eqbrtrd', '( %s -> ( abs ` ( %s ` y ) ) <_ Q )' % (Ae, GN))
        ex = w.s([le], 'ex', '( %s -> ( ( Re ` y ) = %s -> ( abs ` ( %s ` y ) ) <_ Q ) )' % (Ay, Eb, GN))
        return w.s([ex], 'ralrimiva', '( %s -> A. y e. %s ( ( Re ` y ) = %s -> ( abs ` ( %s ` y ) ) <_ Q ) )' % (A, S, Eb, GN))
    lx = edge('X', 'simpld')
    ly = edge('Y', 'simprd')
    # growth
    BNDE = '( ( ( Y - X ) ^ 2 ) + ( ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` P ) ) ) x. ( abs ` C ) ) )'
    ng = w.s([w.s([w.s([xy, w.s([ws, pc_], 'jca', '( %s -> ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) )' % (A, S))], 'jca',
                       '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) ) )' % (A, S))], 'adantr',
                  '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) ) )' % (Ay, S)), ys, w.inst('zl2plng')], 'syl2anc',
             '( %s -> ( abs ` %s ) <_ ( exp ` %s ) )' % (Ay, NYt, BNDE))
    fb, fbody = inst_ral(w, Ay, w.s([gral], 'adantr', '( %s -> A. z e. %s ( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) ) )' % (Ay, S)),
                         'z', S, '( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) )', 'y', ys)
    KE = '( K x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) )'
    kr = D(w, A, 'rpred', [krp], 'K e. RR')
    kry = w.s([kr], 'adantr', '( %s -> K e. RR )' % Ay)
    bry = w.s([br], 'adantr', '( %s -> B e. RR )' % Ay)
    aim = D(w, Ay, 'abscld', [D(w, Ay, 'recnd', [D(w, Ay, 'imcld', [yc], '( Im ` y ) e. RR')], '( Im ` y ) e. CC')], '( abs ` ( Im ` y ) ) e. RR')
    ebi = D(w, Ay, 'reefcld', [D(w, Ay, 'remulcld', [bry, aim], '( B x. ( abs ` ( Im ` y ) ) ) e. RR')], '( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) e. RR')
    ker = D(w, Ay, 'remulcld', [kry, ebi], '%s e. RR' % KE)
    ax_ = lambda x: D(w, Ay, 'abscld', [D(w, Ay, 'recnd', [w.s([x], 'adantr', '( %s -> %s e. RR )' % (Ay, {xr: 'X', yr: 'Y', pr: 'P', cr: 'C'}[x]))],
                                               '%s e. CC' % {xr: 'X', yr: 'Y', pr: 'P', cr: 'C'}[x])], '( abs ` %s ) e. RR' % {xr: 'X', yr: 'Y', pr: 'P', cr: 'C'}[x])
    bnr = D(w, Ay, 'readdcld', [D(w, Ay, 'resqcld', [D(w, Ay, 'resubcld', [yry, xry], '( Y - X ) e. RR')], '( ( Y - X ) ^ 2 ) e. RR'),
                                D(w, Ay, 'remulcld', [D(w, Ay, 'readdcld', [ax_(xr), D(w, Ay, 'readdcld', [ax_(yr), ax_(pr)], '( ( abs ` Y ) + ( abs ` P ) ) e. RR')],
                                                        '( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` P ) ) ) e. RR'), ax_(cr)],
                                  '( ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` P ) ) ) x. ( abs ` C ) ) e. RR')], '%s e. RR' % BNDE)
    ebn = D(w, Ay, 'reefcld', [bnr], '( exp ` %s ) e. RR' % BNDE)
    ncc = D(w, Ay, 'mulcld', [D(w, Ay, 'efcld', [D(w, Ay, 'sqcld', [D(w, Ay, 'subcld', [yc, w.s([wc], 'adantr', '( %s -> W e. CC )' % Ay)], '( y - W ) e. CC')],
                                                                    '( ( y - W ) ^ 2 ) e. CC')], '( exp ` ( ( y - W ) ^ 2 ) ) e. CC'),
                                  D(w, Ay, 'efcld', [D(w, Ay, 'mulcld', [D(w, Ay, 'subcld', [yc, D(w, Ay, 'recnd', [w.s([pr], 'adantr', '( %s -> P e. RR )' % Ay)], 'P e. CC')],
                                                                          '( y - P ) e. CC'), D(w, Ay, 'recnd', [w.s([cr], 'adantr', '( %s -> C e. RR )' % Ay)], 'C e. CC')],
                                                     '( ( y - P ) x. C ) e. CC')], '( exp ` ( ( y - P ) x. C ) ) e. CC')], '%s e. CC' % NYt)
    am = D(w, Ay, 'absmuld', [fyc, ncc], '( abs ` ( ( F ` y ) x. %s ) ) = ( ( abs ` ( F ` y ) ) x. ( abs ` %s ) )' % (NYt, NYt))
    le12 = D(w, Ay, 'lemul12ad', [D(w, Ay, 'abscld', [fyc], '( abs ` ( F ` y ) ) e. RR'), ker, D(w, Ay, 'abscld', [ncc], '( abs ` %s ) e. RR' % NYt), ebn,
                                  D(w, Ay, 'absge0d', [fyc], '0 <_ ( abs ` ( F ` y ) )'), D(w, Ay, 'absge0d', [ncc], '0 <_ ( abs ` %s )' % NYt), fb, ng],
             '( ( abs ` ( F ` y ) ) x. ( abs ` %s ) ) <_ ( %s x. ( exp ` %s ) )' % (NYt, KE, BNDE))
    KP = '( K x. ( exp ` %s ) )' % BNDE
    rr = D(w, Ay, 'mul32d', [D(w, Ay, 'recnd', [kry], 'K e. CC'), D(w, Ay, 'recnd', [ebi], '( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) e. CC'),
                             D(w, Ay, 'recnd', [ebn], '( exp ` %s ) e. CC' % BNDE)],
           '( %s x. ( exp ` %s ) ) = ( %s x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) )' % (KE, BNDE, KP))
    gy = w.s([w.s([w.s([w.s([gv], 'fveq2d', '( %s -> ( abs ` ( %s ` y ) ) = ( abs ` %s ) )' % (Ay, GN, gval)), am], 'eqtrd',
                        '( %s -> ( abs ` ( %s ` y ) ) = ( ( abs ` ( F ` y ) ) x. ( abs ` %s ) ) )' % (Ay, GN, NYt)), le12], 'eqbrtrd',
                  '( %s -> ( abs ` ( %s ` y ) ) <_ ( %s x. ( exp ` %s ) ) )' % (Ay, GN, KE, BNDE)), rr], 'breqtrd',
             '( %s -> ( abs ` ( %s ` y ) ) <_ ( %s x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) ) )' % (Ay, GN, KP))
    gall = w.s([gy], 'ralrimiva', '( %s -> A. y e. %s ( abs ` ( %s ` y ) ) <_ ( %s x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) ) )' % (A, S, GN, KP))
    # K' e. RR+
    bnA = w.s([w.s([w.s([xy, w.s([ws, pc_], 'jca', '( %s -> ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) )' % (A, S))], 'jca',
                        '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) ) )' % (A, S))], 'idi',
                  '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) ) )' % (A, S))], 'idi',
              '( %s -> ( ( X e. RR /\\ Y e. RR ) /\\ ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) ) )' % (A, S))
    bnrA = D(w, A, 'readdcld', [D(w, A, 'resqcld', [D(w, A, 'resubcld', [yr, xr], '( Y - X ) e. RR')], '( ( Y - X ) ^ 2 ) e. RR'),
                                D(w, A, 'remulcld', [D(w, A, 'readdcld', [D(w, A, 'abscld', [D(w, A, 'recnd', [xr], 'X e. CC')], '( abs ` X ) e. RR'),
                                                                          D(w, A, 'readdcld', [D(w, A, 'abscld', [D(w, A, 'recnd', [yr], 'Y e. CC')], '( abs ` Y ) e. RR'),
                                                                                               D(w, A, 'abscld', [D(w, A, 'recnd', [pr], 'P e. CC')], '( abs ` P ) e. RR')],
                                                                            '( ( abs ` Y ) + ( abs ` P ) ) e. RR')], '( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` P ) ) ) e. RR'),
                                                     D(w, A, 'abscld', [D(w, A, 'recnd', [cr], 'C e. CC')], '( abs ` C ) e. RR')],
                                  '( ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` P ) ) ) x. ( abs ` C ) ) e. RR')], '%s e. RR' % BNDE)
    kpr = D(w, A, 'rpmulcld', [krp, D(w, A, 'rpefcld', [bnrA], '( exp ` %s ) e. RR+' % BNDE)], '%s e. RR+' % KP)
    # rectintpl
    Sx = '( ( X e. RR /\\ Y e. RR ) /\\ ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) /\\ %s C_ D ) /\\ ( Q e. RR+ /\\ A. y e. %s ( ( Re ` y ) = X -> ( abs ` ( %s ` y ) ) <_ Q ) /\\ A. y e. %s ( ( Re ` y ) = Y -> ( abs ` ( %s ` y ) ) <_ Q ) ) )' % (GN, GN, S, S, GN, S, GN)
    c1 = w.s([xy, w.s([g1, g2, sd], '3jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) /\\ %s C_ D ) )' % (A, GN, GN, S)),
              w.s([qrp, lx, ly], '3jca', '( %s -> ( Q e. RR+ /\\ A. y e. %s ( ( Re ` y ) = X -> ( abs ` ( %s ` y ) ) <_ Q ) /\\ A. y e. %s ( ( Re ` y ) = Y -> ( abs ` ( %s ` y ) ) <_ Q ) ) )' % (A, S, GN, S, GN))],
             '3jca', '( %s -> %s )' % (A, Sx))
    Gx = '( ( ( %s e. RR+ /\\ B e. RR /\\ 0 <_ B ) /\\ A. y e. %s ( abs ` ( %s ` y ) ) <_ ( %s x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) ) ) /\\ W e. %s )' % (KP, S, GN, KP, S)
    c2 = w.s([w.s([w.s([kpr, br, b0], '3jca', '( %s -> ( %s e. RR+ /\\ B e. RR /\\ 0 <_ B ) )' % (A, KP)), gall], 'jca',
                  '( %s -> ( ( %s e. RR+ /\\ B e. RR /\\ 0 <_ B ) /\\ A. y e. %s ( abs ` ( %s ` y ) ) <_ ( %s x. ( exp ` ( B x. ( abs ` ( Im ` y ) ) ) ) ) ) )' % (A, KP, S, GN, KP)), ws],
             'jca', '( %s -> %s )' % (A, Gx))
    pl = w.s([c1, c2, w.inst('rectintpl')], 'syl2anc', '( %s -> ( abs ` ( %s ` W ) ) <_ Q )' % (A, GN))
    # | G ( W ) | = | F ( W ) | e ^ ( ( Re W - P ) C )
    wd = w.s([sd, ws], 'sseldd', '( %s -> W e. D )' % A)
    gw, gwv = mptval_(w, A, 'z', 'D', '( ( F ` z ) x. %s )' % NRM('z'), 'W', wd)
    fwc = w.s([ff, wd], 'ffvelcdmd', '( %s -> ( F ` W ) e. CC )' % A)
    mw = w.s([w.s([wc, pc_], 'jca', '( %s -> ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) )' % A), w.s([wc, fwc], 'jca', '( %s -> ( W e. CC /\\ ( F ` W ) e. CC ) )' % A),
              w.inst('zl2plnv')], 'syl2anc',
             '( %s -> ( abs ` %s ) = ( ( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) ) ) x. ( exp ` ( ( ( Re ` W ) - P ) x. C ) ) ) )' % (A, gwv))
    rwc = D(w, A, 'recnd', [wr], '( Re ` W ) e. CC')
    iwc = D(w, A, 'recnd', [D(w, A, 'imcld', [wc], '( Im ` W ) e. RR')], '( Im ` W ) e. CC')
    z1 = D(w, A, 'subidd', [rwc], '( ( Re ` W ) - ( Re ` W ) ) = 0')
    z2 = D(w, A, 'subidd', [iwc], '( ( Im ` W ) - ( Im ` W ) ) = 0')
    sq0 = w.s([w.s([], 'sq0', '( 0 ^ 2 ) = 0')], 'a1i', '( %s -> ( 0 ^ 2 ) = 0 )' % A)
    q1 = w.s([E(w, A, 'oveq1d', [z1], '( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 )', '( 0 ^ 2 )'), sq0], 'eqtrd', '( %s -> ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) = 0 )' % A)
    q2 = w.s([E(w, A, 'oveq1d', [z2], '( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 )', '( 0 ^ 2 )'), sq0], 'eqtrd', '( %s -> ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) = 0 )' % A)
    q3 = E(w, A, 'oveq12d', [q1, q2], '( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) )', '( 0 - 0 )')
    q4 = w.s([q3, w.s([w.s([w.s([], '0cn', '0 e. CC')], 'subidi', '( 0 - 0 ) = 0')], 'a1i', '( %s -> ( 0 - 0 ) = 0 )' % A)], 'eqtrd',
             '( %s -> ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) = 0 )' % A)
    q5 = w.s([E(w, A, 'fveq2d', [q4], '( exp ` ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) )', '( exp ` 0 )'),
              w.s([w.s([], 'ef0', '( exp ` 0 ) = 1')], 'a1i', '( %s -> ( exp ` 0 ) = 1 )' % A)], 'eqtrd',
             '( %s -> ( exp ` ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) ) = 1 )' % A)
    q6 = E(w, A, 'oveq2d', [q5], '( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) ) )',
           '( ( abs ` ( F ` W ) ) x. 1 )')
    q7 = w.s([q6, D(w, A, 'mulridd', [D(w, A, 'recnd', [D(w, A, 'abscld', [fwc], '( abs ` ( F ` W ) ) e. RR')], '( abs ` ( F ` W ) ) e. CC')],
                    '( ( abs ` ( F ` W ) ) x. 1 ) = ( abs ` ( F ` W ) )')], 'eqtrd',
             '( %s -> ( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) ) ) = ( abs ` ( F ` W ) ) )' % A)
    q8 = E(w, A, 'oveq1d', [q7], '( ( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) ) ) x. ( exp ` ( ( ( Re ` W ) - P ) x. C ) ) )',
           '( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( Re ` W ) - P ) x. C ) ) )')
    FIN = '( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( Re ` W ) - P ) x. C ) ) )'
    ev = chain(w, A, ['( abs ` ( %s ` W ) )' % GN, '( abs ` %s )' % gwv,
                      '( ( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( ( Re ` W ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` W ) - ( Im ` W ) ) ^ 2 ) ) ) ) x. ( exp ` ( ( ( Re ` W ) - P ) x. C ) ) )', FIN],
               [w.s([gw], 'fveq2d', '( %s -> ( abs ` ( %s ` W ) ) = ( abs ` %s ) )' % (A, GN, gwv)), mw, q8])
    w.qed([ev, pl], 'eqbrtrrd', '( %s -> %s <_ Q )' % (A, FIN))
    go(w, only)
