"""ZL3d section A: holomorphy of parameter integrals (zl3pih).
`MM_DB=sorties/zl3d.mm python3 tools/gen/zl3d_a.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl2lib import W, D, E, a1, Closure, chain, efle_, efadd_
from lin import linarith, nlinarith, lineq
import lin
lin.FASTPATH = True
import num
import zl3dlib as L
from c0lib import runh

only = sys.argv[1:]
S = L.STATEMENTS


def go(w):
    if only and w.label not in only:
        return True
    if os.environ.get('ZL3D_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines)); return True
    return runh(w) if L.HYPS.get(w.label) else w.run()


def want(label):
    return __name__ == '__main__' and (not only or label in only)


def ante_of(label):
    return L.split_imp(S[label])


def cst(w, A, lab, fact):
    return w.s([w.s([], lab, fact)], 'a1i', '( %s -> %s )' % (A, fact))


# ---------------------------------------------------------------- zl3eqb
if want('zl3eqb'):
    w = W('zl3eqb', 'On the closed unit disc ` abs ( e ^ U - 1 - U ) <_ abs ( U ) ^ 2 ` ( ~ efsep , ~ eftlub at ` M = 2 ` ).')
    A, C = ante_of('zl3eqb')
    uc = D(w, A, 'simpl', [], 'U e. CC'); ule = D(w, A, 'simpr', [], '( abs ` U ) <_ 1')
    FF = '( n e. NN0 |-> ( ( U ^ n ) / ( ! ` n ) ) )'
    feq = w.s([], 'eqid', '%s = %s' % (FF, FF))
    SUM = lambda m: 'sum_ k e. ( ZZ>= ` %s ) ( %s ` k )' % (m, FF)
    e0a = w.s([feq], 'efval2', '( U e. CC -> ( exp ` U ) = sum_ k e. NN0 ( %s ` k ) )' % FF)
    e0 = D(w, A, 'syl', [uc, e0a], '( exp ` U ) = sum_ k e. NN0 ( %s ` k )' % FF)
    su = w.s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'sumeq1i', 'sum_ k e. NN0 ( %s ` k ) = %s' % (FF, SUM('0')))
    e1 = D(w, A, 'eqtrd', [e0, w.s([su], 'a1i', '( %s -> sum_ k e. NN0 ( %s ` k ) = %s )' % (A, FF, SUM('0')))], '( exp ` U ) = %s' % SUM('0'))
    s0c = D(w, A, 'syl2anc', [uc, cst(w, A, '0nn0', '0 e. NN0'), w.s([feq], 'eftlcl', '( ( U e. CC /\\ 0 e. NN0 ) -> %s e. CC )' % SUM('0'))], '%s e. CC' % SUM('0'))
    e2 = D(w, A, 'eqtr4d', [e1, D(w, A, 'addlidd', [s0c], '( 0 + %s ) = %s' % (SUM('0'), SUM('0')))], '( exp ` U ) = ( 0 + %s )' % SUM('0'))
    one = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'eqcomi', '1 = ( 0 + 1 )')
    d1 = D(w, A, 'eqtrd', [D(w, A, 'oveq2d', [D(w, A, 'syl', [uc, w.inst('eft0val')], '( ( U ^ 0 ) / ( ! ` 0 ) ) = 1')], '( 0 + ( ( U ^ 0 ) / ( ! ` 0 ) ) ) = ( 0 + 1 )'),
                           cst(w, A, '0p1e1', '( 0 + 1 ) = 1')], '( 0 + ( ( U ^ 0 ) / ( ! ` 0 ) ) ) = 1')
    e3 = D(w, A, 'efsep', [feq, one, w.s([], '0nn0', '0 e. NN0'), uc, D(w, A, '0cnd', [], '0 e. CC'), e2, d1], '( exp ` U ) = ( 1 + %s )' % SUM('1'))
    u1 = D(w, A, 'eqtrd', [D(w, A, 'oveq12d', [D(w, A, 'syl', [uc, w.inst('exp1')], '( U ^ 1 ) = U'), cst(w, A, 'fac1', '( ! ` 1 ) = 1')], '( ( U ^ 1 ) / ( ! ` 1 ) ) = ( U / 1 )'),
                           D(w, A, 'syl', [uc, w.inst('div1')], '( U / 1 ) = U')], '( ( U ^ 1 ) / ( ! ` 1 ) ) = U')
    d2 = D(w, A, 'oveq2d', [u1], '( 1 + ( ( U ^ 1 ) / ( ! ` 1 ) ) ) = ( 1 + U )')
    e4 = D(w, A, 'efsep', [feq, w.s([], 'df-2', '2 = ( 1 + 1 )'), w.s([], '1nn0', '1 e. NN0'), uc, D(w, A, '1cnd', [], '1 e. CC'), e3, d2],
           '( exp ` U ) = ( ( 1 + U ) + %s )' % SUM('2'))
    s2c = D(w, A, 'syl2anc', [uc, cst(w, A, '2nn0', '2 e. NN0'), w.s([feq], 'eftlcl', '( ( U e. CC /\\ 2 e. NN0 ) -> %s e. CC )' % SUM('2'))], '%s e. CC' % SUM('2'))
    c1 = D(w, A, '1cnd', [], '1 e. CC')
    opu = D(w, A, 'addcld', [c1, uc], '( 1 + U ) e. CC')
    ec = D(w, A, 'efcld', [uc], '( exp ` U ) e. CC')
    X = '( ( ( exp ` U ) - 1 ) - U )'
    x1 = D(w, A, 'subsub4d', [ec, c1, uc], '%s = ( ( exp ` U ) - ( 1 + U ) )' % X)
    x2 = D(w, A, 'oveq1d', [e4], '( ( exp ` U ) - ( 1 + U ) ) = ( ( ( 1 + U ) + %s ) - ( 1 + U ) )' % SUM('2'))
    x3 = D(w, A, 'pncan2d', [opu, s2c], '( ( ( 1 + U ) + %s ) - ( 1 + U ) ) = %s' % (SUM('2'), SUM('2')))
    xe = chain(w, A, [X, '( ( exp ` U ) - ( 1 + U ) )', '( ( ( 1 + U ) + %s ) - ( 1 + U ) )' % SUM('2'), SUM('2')], [x1, x2, x3])
    ab = D(w, A, 'fveq2d', [xe], '( abs ` %s ) = ( abs ` %s )' % (X, SUM('2')))
    GG = '( n e. NN0 |-> ( ( ( abs ` U ) ^ n ) / ( ! ` n ) ) )'
    HH = '( n e. NN0 |-> ( ( ( ( abs ` U ) ^ 2 ) / ( ! ` 2 ) ) x. ( ( 1 / ( 2 + 1 ) ) ^ n ) ) )'
    CT = '( ( 2 + 1 ) / ( ( ! ` 2 ) x. 2 ) )'
    X2 = '( ( abs ` U ) ^ 2 )'
    tl = D(w, A, 'eftlub', [feq, w.s([], 'eqid', '%s = %s' % (GG, GG)), w.s([], 'eqid', '%s = %s' % (HH, HH)), cst(w, A, '2nn', '2 e. NN'), uc, ule],
           '( abs ` %s ) <_ ( %s x. %s )' % (SUM('2'), X2, CT))
    f2 = w.s([w.s([], 'fac2', '( ! ` 2 ) = 2')], 'oveq1i', '( ( ! ` 2 ) x. 2 ) = ( 2 x. 2 )')
    f4 = w.s([f2, w.s([], '2t2e4', '( 2 x. 2 ) = 4')], 'eqtri', '( ( ! ` 2 ) x. 2 ) = 4')
    ce = w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3'), f4], 'oveq12i', '%s = ( 3 / 4 )' % CT)
    cee = D(w, A, 'oveq2d', [w.s([ce], 'a1i', '( %s -> %s = ( 3 / 4 ) )' % (A, CT))], '( %s x. %s ) = ( %s x. ( 3 / 4 ) )' % (X2, CT, X2))
    tl2 = D(w, A, 'breqtrd', [tl, cee], '( abs ` %s ) <_ ( %s x. ( 3 / 4 ) )' % (SUM('2'), X2))
    aur = D(w, A, 'abscld', [uc], '( abs ` U ) e. RR')
    x2g = D(w, A, 'sqge0d', [aur], '0 <_ %s' % X2)
    x2r = D(w, A, 'resqcld', [aur], '%s e. RR' % X2)
    le = linarith(w, A, [x2g], '( %s x. ( 3 / 4 ) ) <_ %s' % (X2, X2), leaves={X2: x2r})
    fin = D(w, A, 'letrd', [tl2, le], '( abs ` %s ) <_ %s' % (SUM('2'), X2))
    w.qed([ab, fin], 'eqbrtrd', S['zl3eqb'])
    go(w)


# ---------------------------------------------------------------- helpers
GMAP = 'G : ( 1 [,) +oo ) --> CC'
GCN = '( G |` ( 1 (,) +oo ) ) e. ( ( 1 (,) +oo ) -cn-> CC )'
BNDV = 'A. v e. ( 1 [,) +oo ) ( abs ` ( G ` v ) ) <_ ( K x. ( exp ` -u ( B x. v ) ) )'
I1 = '( 1 [,) +oo )'
I1O = '( 1 (,) +oo )'


def phv_facts(w, A, phv):
    """from phv: ( A -> PHV ): the pieces"""
    d = {}
    l = D(w, A, 'simpld', [phv], '( %s /\\ %s )' % (GMAP, GCN))
    r = D(w, A, 'simprd', [phv], '( K e. RR+ /\\ B e. RR+ /\\ %s )' % BNDV)
    d['g'] = D(w, A, 'simpld', [l], GMAP); d['gc'] = D(w, A, 'simprd', [l], GCN)
    d['k'] = D(w, A, 'simp1d', [r], 'K e. RR+'); d['b'] = D(w, A, 'simp2d', [r], 'B e. RR+'); d['bnd'] = D(w, A, 'simp3d', [r], BNDV)
    return d


def gbound(w, A, bnd, dd, dmem, K='K', B='B'):
    """( A -> ( abs ` ( G ` d ) ) <_ ( K x. ( exp ` -u ( B x. d ) ) ) ) from dmem: ( A -> d e. ( 1 [,) +oo ) )"""
    sub = w.s([w.s([w.s([], 'fveq2', '( v = %s -> ( G ` v ) = ( G ` %s ) )' % (dd, dd))], 'fveq2d', '( v = %s -> ( abs ` ( G ` v ) ) = ( abs ` ( G ` %s ) ) )' % (dd, dd)),
               w.s([w.s([w.s([w.s([], 'oveq2', '( v = %s -> ( %s x. v ) = ( %s x. %s ) )' % (dd, B, B, dd))], 'negeqd', '( v = %s -> -u ( %s x. v ) = -u ( %s x. %s ) )' % (dd, B, B, dd))],
                             'fveq2d', '( v = %s -> ( exp ` -u ( %s x. v ) ) = ( exp ` -u ( %s x. %s ) ) )' % (dd, B, B, dd))], 'oveq2d',
                    '( v = %s -> ( %s x. ( exp ` -u ( %s x. v ) ) ) = ( %s x. ( exp ` -u ( %s x. %s ) ) ) )' % (dd, K, B, K, B, dd))],
              'breq12d', '( v = %s -> ( ( abs ` ( G ` v ) ) <_ ( %s x. ( exp ` -u ( %s x. v ) ) ) <-> ( abs ` ( G ` %s ) ) <_ ( %s x. ( exp ` -u ( %s x. %s ) ) ) ) )' % (dd, K, B, dd, K, B, dd))
    return D(w, A, 'rspcdva', [sub, bnd, dmem], '( abs ` ( G ` %s ) ) <_ ( %s x. ( exp ` -u ( %s x. %s ) ) )' % (dd, K, B, dd))



def ioo_in1(w, A, pr, p1, qr, P='P', Q='Q'):
    """( A -> ( P (,) Q ) C_ ( 1 (,) +oo ) ), ( A -> ( P (,) Q ) C_ ( 1 [,) +oo ) )"""
    X = '( %s (,) %s )' % (P, Q)
    qinf = D(w, A, 'pnfged', [D(w, A, 'rexrd', [qr], '%s e. RR*' % Q)], '%s <_ +oo' % Q)
    ss1 = D(w, A, 'syl2anc', [D(w, A, 'jca', [cst(w, A, '1xr', '1 e. RR*'), cst(w, A, 'pnfxr', '+oo e. RR*')], '( 1 e. RR* /\\ +oo e. RR* )'),
                               D(w, A, 'jca', [p1, qinf], '( 1 <_ %s /\\ %s <_ +oo )' % (P, Q)), w.inst('ioossioo')], '%s C_ %s' % (X, I1O))
    ss2 = D(w, A, 'sstrd', [ss1, cst(w, A, 'ioossico', '%s C_ %s' % (I1O, I1))], '%s C_ %s' % (X, I1))
    return ss1, ss2


def ge1(w, A, dmem, dd='d'):
    """( A -> d e. RR ), ( A -> 1 <_ d ) from dmem: ( A -> d e. ( 1 [,) +oo ) )"""
    bi = D(w, A, 'syl', [cst(w, A, '1re', '1 e. RR'), w.inst('elicopnf')], '( %s e. %s <-> ( %s e. RR /\\ 1 <_ %s ) )' % (dd, I1, dd, dd))
    both = D(w, A, 'mpbid', [dmem, bi], '( %s e. RR /\\ 1 <_ %s )' % (dd, dd))
    return D(w, A, 'simpld', [both], '%s e. RR' % dd), D(w, A, 'simprd', [both], '1 <_ %s' % dd)


def expneg_le1(w, A, br, dr, d1, B='B', dd='d'):
    """( A -> ( exp ` -u ( B x. d ) ) <_ 1 ) from br: B e. RR+, dr: d e. RR, d1: 1 <_ d"""
    b0 = D(w, A, 'rpgt0d', [br], '0 < %s' % B)
    brr = D(w, A, 'rpred', [br], '%s e. RR' % B)
    bd = '( %s x. %s )' % (B, dd)
    bdr = D(w, A, 'remulcld', [brr, dr], '%s e. RR' % bd)
    le0 = nlinarith(w, A, [b0, d1], '-u %s <_ 0' % bd, leaves={B: brr, dd: dr})
    e = efle_(w, A, '-u %s' % bd, '0', D(w, A, 'renegcld', [bdr], '-u %s e. RR' % bd), cst(w, A, '0re', '0 e. RR'), le0)
    return D(w, A, 'breqtrd', [e, cst(w, A, 'ef0', '( exp ` 0 ) = 1')], '( exp ` -u %s ) <_ 1' % bd)


# ---------------------------------------------------------------- zl3gib
if want('zl3gib'):
    w = W('zl3gib', '` G ` times a function continuous on ` [ P , Q ] ` , ` 1 <_ P ` , is integrable on ` ( P , Q ) ` ( ~ bddmulibl , ~ cnmbf ).')
    A, C = ante_of('zl3gib')
    phv = D(w, A, 'simp1', [], L.PHV); f = phv_facts(w, A, phv)
    iv = D(w, A, 'simp2', [], '( ( P e. RR /\\ 1 <_ P ) /\\ Q e. RR )')
    hc = D(w, A, 'simp3', [], 'H e. ( ( P [,] Q ) -cn-> CC )')
    pp = D(w, A, 'simpld', [iv], '( P e. RR /\\ 1 <_ P )')
    pr = D(w, A, 'simpld', [pp], 'P e. RR'); p1 = D(w, A, 'simprd', [pp], '1 <_ P'); qr = D(w, A, 'simprd', [iv], 'Q e. RR')
    X = '( P (,) Q )'
    ss1, ss2 = ioo_in1(w, A, pr, p1, qr)
    FR = '( G |` %s )' % X
    rc = D(w, A, 'sylc', [ss1, f['gc'], w.inst('rescncf')], '( ( G |` %s ) |` %s ) e. ( %s -cn-> CC )' % (I1O, X, X))
    ra = D(w, A, 'syl', [ss1, w.inst('resabs1')], '( ( G |` %s ) |` %s ) = %s' % (I1O, X, FR))
    frc = D(w, A, 'eqeltrrd', [ra, rc], '%s e. ( %s -cn-> CC )' % (FR, X))
    mbf = D(w, A, 'sylancr', [w.s([], 'ioombl', '%s e. dom vol' % X), frc, w.inst('cnmbf')], '%s e. MblFn' % FR)
    hl = D(w, A, 'syl2anc', [D(w, A, 'jca', [pr, qr], '( P e. RR /\\ Q e. RR )'), hc, w.inst('zl3ibl')], '( H |` %s ) e. L^1' % X)
    # the bound K on ( P , Q )
    Ad = '( %s /\\ d e. %s )' % (A, X)
    dx = D(w, Ad, 'simpr', [], 'd e. %s' % X)
    d1 = D(w, Ad, 'sseldd', [w.s([ss2], 'adantr', '( %s -> %s C_ %s )' % (Ad, X, I1)), dx], 'd e. %s' % I1)
    gb = gbound(w, Ad, w.s([f['bnd']], 'adantr', '( %s -> %s )' % (Ad, BNDV)), 'd', d1)
    fv = D(w, Ad, 'syl', [dx, w.inst('fvres')], '( %s ` d ) = ( G ` d )' % FR)
    dr, dge = ge1(w, Ad, d1)
    br = w.s([f['b']], 'adantr', '( %s -> B e. RR+ )' % Ad); kr = w.s([f['k']], 'adantr', '( %s -> K e. RR+ )' % Ad)
    EX = '( exp ` -u ( B x. d ) )'
    el = expneg_le1(w, Ad, br, dr, dge)
    exr = D(w, Ad, 'reefcld', [D(w, Ad, 'renegcld', [D(w, Ad, 'remulcld', [D(w, Ad, 'rpred', [br], 'B e. RR'), dr], '( B x. d ) e. RR')], '-u ( B x. d ) e. RR')], '%s e. RR' % EX)
    kk = nlinarith(w, Ad, [el, D(w, Ad, 'rpgt0d', [kr], '0 < K')], '( K x. %s ) <_ K' % EX, leaves={'K': D(w, Ad, 'rpred', [kr], 'K e. RR'), EX: exr}, atoms=[EX])
    gdc = D(w, Ad, 'ffvelcdmd', [w.s([f['g']], 'adantr', '( %s -> %s )' % (Ad, GMAP)), d1], '( G ` d ) e. CC')
    kxr = D(w, Ad, 'remulcld', [D(w, Ad, 'rpred', [kr], 'K e. RR'), exr], '( K x. %s ) e. RR' % EX)
    gk = D(w, Ad, 'letrd', [D(w, Ad, 'abscld', [gdc], '( abs ` ( G ` d ) ) e. RR'), kxr, D(w, Ad, 'rpred', [kr], 'K e. RR'), gb, kk], '( abs ` ( G ` d ) ) <_ K')
    fk = D(w, Ad, 'eqbrtrd', [D(w, Ad, 'fveq2d', [fv], '( abs ` ( %s ` d ) ) = ( abs ` ( G ` d ) )' % FR), gk], '( abs ` ( %s ` d ) ) <_ K' % FR)
    ral = D(w, A, 'ralrimiva', [fk], 'A. d e. %s ( abs ` ( %s ` d ) ) <_ K' % (X, FR))
    frf = D(w, A, 'syl2anc', [f['g'], ss2, w.inst('fssres')], '%s : %s --> CC' % (FR, X))
    dm = D(w, A, 'syl', [frf, w.inst('fdm')], 'dom %s = %s' % (FR, X))
    ral2 = D(w, A, 'mpbird', [ral, D(w, A, 'raleqdv', [dm], '( A. d e. dom %s ( abs ` ( %s ` d ) ) <_ K <-> A. d e. %s ( abs ` ( %s ` d ) ) <_ K )' % (FR, FR, X, FR))],
             'A. d e. dom %s ( abs ` ( %s ` d ) ) <_ K' % (FR, FR))
    sub = w.s([w.s([], 'breq2', '( c = K -> ( ( abs ` ( %s ` d ) ) <_ c <-> ( abs ` ( %s ` d ) ) <_ K ) )' % (FR, FR))], 'ralbidv',
              '( c = K -> ( A. d e. dom %s ( abs ` ( %s ` d ) ) <_ c <-> A. d e. dom %s ( abs ` ( %s ` d ) ) <_ K ) )' % (FR, FR, FR, FR))
    ex = D(w, A, 'syl2anc', [D(w, A, 'rpred', [f['k']], 'K e. RR'), ral2, w.s([sub], 'rspcev', '( ( K e. RR /\\ A. d e. dom %s ( abs ` ( %s ` d ) ) <_ K ) -> E. c e. RR A. d e. dom %s ( abs ` ( %s ` d ) ) <_ c )' % (FR, FR, FR, FR))],
           'E. c e. RR A. d e. dom %s ( abs ` ( %s ` d ) ) <_ c' % (FR, FR))
    prod = D(w, A, 'syl3anc', [mbf, hl, ex, w.inst('bddmulibl')], '( %s oF x. ( H |` %s ) ) e. L^1' % (FR, X))
    # the product as a mapping
    Ay = '( %s /\\ y e. %s )' % (A, X)
    yx = D(w, Ay, 'simpr', [], 'y e. %s' % X)
    g1 = D(w, Ay, 'ffvelcdmd', [w.s([f['g']], 'adantr', '( %s -> %s )' % (Ay, GMAP)), D(w, Ay, 'sseldd', [w.s([ss2], 'adantr', '( %s -> %s C_ %s )' % (Ay, X, I1)), yx], 'y e. %s' % I1)], '( G ` y ) e. CC')
    hf = D(w, A, 'syl', [hc, w.inst('cncff')], 'H : ( P [,] Q ) --> CC')
    h1 = D(w, Ay, 'ffvelcdmd', [w.s([hf], 'adantr', '( %s -> H : ( P [,] Q ) --> CC )' % Ay), D(w, Ay, 'sseldd', [cst(w, Ay, 'ioossicc', '%s C_ ( P [,] Q )' % X), yx], 'y e. ( P [,] Q )')], '( H ` y ) e. CC')
    e1 = D(w, A, 'feqresmpt', [f['g'], ss2], '%s = ( y e. %s |-> ( G ` y ) )' % (FR, X))
    e2 = D(w, A, 'feqresmpt', [hf, cst(w, A, 'ioossicc', '%s C_ ( P [,] Q )' % X)], '( H |` %s ) = ( y e. %s |-> ( H ` y ) )' % (X, X))
    ofv = D(w, A, 'offval2', [cst(w, A, 'ovex', '%s e. _V' % X), g1, h1, e1, e2], '( %s oF x. ( H |` %s ) ) = ( y e. %s |-> ( ( G ` y ) x. ( H ` y ) ) )' % (FR, X, X))
    w.qed([ofv, prod], 'eqeltrrd', S['zl3gib'])
    go(w)


def fvmpt_(w, x, u, Dom, body, body_u, sub, name_map):
    """closed: ( u e. Dom -> ( MAP ` u ) = body_u ) with MAP = ( x e. Dom |-> body ), body_u a set (ovex/fvex)"""
    MAP = '( %s e. %s |-> %s )' % (x, Dom, body)
    ex = w.s([], 'ovex' if body_u.startswith('( ') and ' ` ' not in body_u.split(' ')[1:2] else 'fvex', '%s e. _V' % body_u)
    return w.s([sub, w.s([], 'eqid', '%s = %s' % (MAP, MAP)), ex], 'fvmpt', '( %s e. %s -> ( %s ` %s ) = %s )' % (u, Dom, MAP, u, body_u))


def DQ(F, z, Sp):
    return '( ( ( %s ` %s ) - ( %s ` %s ) ) / ( %s - %s ) )' % (F, z, F, Sp, z, Sp)


# ---------------------------------------------------------------- zl3dvb
if want('zl3dvb'):
    w = W('zl3dvb', 'A linear bound ` abs ( DQ ( z ) - V ) <_ C abs ( z - S ) ` on the difference quotient near ` S ` in an open ` D ` gives the derivative ` V ` at ` S ` ( ~ eldv , ~ ellimc3 ).')
    A, Cc = ante_of('zl3dvb')
    J = '( TopOpen ` CCfld )'
    h1 = D(w, A, 'simp1', [], '( D e. %s /\\ S e. D )' % J)
    h2 = D(w, A, 'simp2', [], '( F : D --> CC /\\ V e. CC )')
    HY = 'A. z e. D ( ( z =/= S /\\ ( abs ` ( z - S ) ) < R ) -> ( abs ` ( %s - V ) ) <_ ( C x. ( abs ` ( z - S ) ) ) )' % DQ('F', 'z', 'S')
    h3 = D(w, A, 'simp3', [], '( C e. RR /\\ R e. RR+ /\\ %s )' % HY)
    dj = D(w, A, 'simpld', [h1], 'D e. %s' % J); sd = D(w, A, 'simprd', [h1], 'S e. D')
    ff = D(w, A, 'simpld', [h2], 'F : D --> CC'); vc = D(w, A, 'simprd', [h2], 'V e. CC')
    cr = D(w, A, 'simp1d', [h3], 'C e. RR'); rr = D(w, A, 'simp2d', [h3], 'R e. RR+'); hy = D(w, A, 'simp3d', [h3], HY)
    jeq = w.s([], 'eqid', '%s = %s' % (J, J))
    jton = w.s([jeq], 'cnfldtopon', '%s e. ( TopOn ` CC )' % J)
    jtop = w.s([jeq], 'cnfldtop', '%s e. Top' % J)
    dcc = D(w, A, 'sylancr', [jton, dj, w.inst('toponss')], 'D C_ CC')
    sc = D(w, A, 'sseldd', [dcc, sd], 'S e. CC')
    T = '( %s |`t CC )' % J
    teq = w.s([w.s([w.s([jton], 'toponunii', 'CC = U. %s' % J)], 'restid', '( %s e. Top -> %s = %s )' % (J, T, J)), jtop], 'mpi' if False else 'ax-mp', '%s = %s' % (T, J)) if False else None
    tj = w.s([jtop, w.s([w.s([jton], 'toponunii', 'CC = U. %s' % J)], 'restid', '( %s e. Top -> %s = %s )' % (J, T, J))], 'ax-mp', '%s = %s' % (T, J))
    GQ = '( x e. ( D \\ { S } ) |-> %s )' % DQ('F', 'x', 'S')
    geq = w.s([], 'eqid', '%s = %s' % (GQ, GQ))
    ccss = cst(w, A, 'ssid', 'CC C_ CC')
    eld = D(w, A, 'eldv', [w.s([], 'eqid', '%s = %s' % (T, T)), jeq, geq, ccss, ff, dcc],
            '( S ( CC _D F ) V <-> ( S e. ( ( int ` %s ) ` D ) /\\ V e. ( %s limCC S ) ) )' % (T, GQ))
    # S in the interior
    it = D(w, A, 'sylancr', [jtop, dj, w.inst('isopn3i')], '( ( int ` %s ) ` D ) = D' % J)
    it2 = D(w, A, 'eqtrd', [D(w, A, 'fveq2d', [D(w, A, 'fveq2d', [cst(w, A, 'idi', '%s = %s' % (T, J)) if False else w.s([tj], 'a1i', '( %s -> %s = %s )' % (A, T, J))],
                                                                  '( int ` %s ) = ( int ` %s )' % (T, J))], '( ( int ` %s ) ` D ) = ( ( int ` %s ) ` D )' % (T, J)) if False else
                                D(w, A, 'fveq1d', [D(w, A, 'fveq2d', [w.s([tj], 'a1i', '( %s -> %s = %s )' % (A, T, J))], '( int ` %s ) = ( int ` %s )' % (T, J))],
                                  '( ( int ` %s ) ` D ) = ( ( int ` %s ) ` D )' % (T, J)), it], '( ( int ` %s ) ` D ) = D' % T)
    sint = D(w, A, 'eleqtrrd', [sd, it2], 'S e. ( ( int ` %s ) ` D )' % T)
    # the limit
    DS = '( D \\ { S } )'
    Az = '( %s /\\ x e. %s )' % (A, DS)
    zd = D(w, Az, 'eldifad', [D(w, Az, 'simpr', [], 'x e. %s' % DS)], 'x e. D')
    zc = D(w, Az, 'sseldd', [w.s([dcc], 'adantr', '( %s -> D C_ CC )' % Az), zd], 'x e. CC')
    zne = D(w, Az, 'eldifsnneqd' if False else 'eldifbd', [D(w, Az, 'simpr', [], 'x e. %s' % DS)], '-. z e. { S }') if False else None
    zne = D(w, Az, 'syl', [D(w, Az, 'simpr', [], 'x e. %s' % DS), w.s([], 'eldifsni', '( x e. %s -> x =/= S )' % DS)], 'x =/= S')
    fzc = D(w, Az, 'ffvelcdmd', [w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Az), zd], '( F ` x ) e. CC')
    fsc = D(w, Az, 'ffvelcdmd', [w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Az), w.s([sd], 'adantr', '( %s -> S e. D )' % Az)], '( F ` S ) e. CC')
    scz = w.s([sc], 'adantr', '( %s -> S e. CC )' % Az)
    dqc = D(w, Az, 'divcld', [D(w, Az, 'subcld', [fzc, fsc], '( ( F ` x ) - ( F ` S ) ) e. CC'), D(w, Az, 'subcld', [zc, scz], '( x - S ) e. CC'),
                               D(w, Az, 'subne0d', [zc, scz, zne], '( x - S ) =/= 0')], '%s e. CC' % DQ('F', 'x', 'S'))
    gf = D(w, A, 'fmptd', [dqc, geq], '%s : %s --> CC' % (GQ, DS))
    lim = D(w, A, 'ellimc3', [gf, D(w, A, 'ssdifssd', [dcc], '%s C_ CC' % DS), sc],
            '( V e. ( %s limCC S ) <-> ( V e. CC /\\ A. e e. RR+ E. r e. RR+ A. u e. %s ( ( u =/= S /\\ ( abs ` ( u - S ) ) < r ) -> ( abs ` ( ( %s ` u ) - V ) ) < e ) ) )' % (GQ, DS, GQ))
    # epsilon-delta
    Ae = '( %s /\\ e e. RR+ )' % A
    er = w.s([], 'simpr', '( %s -> e e. RR+ )' % Ae)
    crr = w.s([cr], 'adantr', '( %s -> C e. RR )' % Ae)
    ac = D(w, Ae, 'recnd', [crr], 'C e. CC')
    Ca = '( abs ` C )'
    ca1 = D(w, Ae, 'rpaddcld' if False else 'readdcld', [D(w, Ae, 'abscld', [ac], '%s e. RR' % Ca), cst(w, Ae, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % Ca)
    ca1p = D(w, Ae, 'ltaddrp2d' if False else 'rpgecld', [], '') if False else None
    capos = D(w, Ae, 'rpaddcld' if False else 'syl', [D(w, Ae, 'absge0d', [ac], '0 <_ %s' % Ca), w.inst('dummy')], '') if False else None
    ca1rp = D(w, Ae, 'ltesubnnd' if False else 'addge01d', [], '') if False else None
    # ( abs C + 1 ) e. RR+ via 0 <_ abs C
    cag = D(w, Ae, 'absge0d', [ac], '0 <_ %s' % Ca)
    car = D(w, Ae, 'abscld', [ac], '%s e. RR' % Ca)
    c1p = linarith(w, Ae, [cag], '0 < ( %s + 1 )' % Ca, leaves={Ca: car})
    c1rp = D(w, Ae, 'elrpd', [ca1, c1p], '( %s + 1 ) e. RR+' % Ca)
    q = '( e / ( %s + 1 ) )' % Ca
    qrp = D(w, Ae, 'rpdivcld', [er, c1rp], '%s e. RR+' % q)
    rrr = w.s([rr], 'adantr', '( %s -> R e. RR+ )' % Ae)
    M = 'if ( R <_ %s , R , %s )' % (q, q)
    mrp = D(w, Ae, 'ifcld', [rrr, qrp], '%s e. RR+' % M)
    # the inner claim at u
    Au = '( %s /\\ u e. %s )' % (Ae, DS)
    Au2 = '( %s /\\ ( u =/= S /\\ ( abs ` ( u - S ) ) < %s ) )' % (Au, M)
    ud = D(w, Au2, 'eldifad', [w.s([], 'simplr', '( %s -> u e. %s )' % (Au2, DS))], 'u e. D')
    une = w.s([], 'simprl', '( %s -> u =/= S )' % Au2)
    ult = w.s([], 'simprr', '( %s -> ( abs ` ( u - S ) ) < %s )' % (Au2, M))
    def up(st, f):
        return w.s([st], 'ad2antrr', '( %s -> %s )' % (Au2, f))
    mr = D(w, Au2, 'rpred', [up(mrp, '%s e. RR+' % M)], '%s e. RR' % M)
    rre = D(w, Au2, 'rpred', [up(rrr, 'R e. RR+')], 'R e. RR')
    qre = D(w, Au2, 'rpred', [up(qrp, '%s e. RR+' % q)], '%s e. RR' % q)
    m1 = D(w, Au2, 'syl2anc', [rre, qre, w.inst('min1')], '%s <_ R' % M)
    m2 = D(w, Au2, 'syl2anc', [rre, qre, w.inst('min2')], '%s <_ %s' % (M, q))
    uc = D(w, Au2, 'sseldd', [up(w.s([dcc], 'adantr', '( %s -> D C_ CC )' % Ae), 'D C_ CC'), ud], 'u e. CC')
    scu = up(w.s([sc], 'adantr', '( %s -> S e. CC )' % Ae), 'S e. CC')
    US = '( abs ` ( u - S ) )'
    usr = D(w, Au2, 'abscld', [D(w, Au2, 'subcld', [uc, scu], '( u - S ) e. CC')], '%s e. RR' % US)
    ultR = D(w, Au2, 'ltletrd', [usr, mr, rre, ult, m1], '%s < R' % US)
    ultq = D(w, Au2, 'ltletrd', [usr, mr, qre, ult, m2], '%s < %s' % (US, q))
    # the hypothesis at u
    sub = w.s([w.s([w.s([], 'neeq1', '( z = u -> ( z =/= S <-> u =/= S ) )'),
                     w.s([w.s([w.s([], 'oveq1', '( z = u -> ( z - S ) = ( u - S ) )')], 'fveq2d', '( z = u -> ( abs ` ( z - S ) ) = %s )' % US)], 'breq1d',
                         '( z = u -> ( ( abs ` ( z - S ) ) < R <-> %s < R ) )' % US)], 'anbi12d',
                    '( z = u -> ( ( z =/= S /\\ ( abs ` ( z - S ) ) < R ) <-> ( u =/= S /\\ %s < R ) ) )' % US),
               w.s([w.s([w.s([w.s([w.s([w.s([], 'fveq2', '( z = u -> ( F ` z ) = ( F ` u ) )')], 'oveq1d', '( z = u -> ( ( F ` z ) - ( F ` S ) ) = ( ( F ` u ) - ( F ` S ) ) )'),
                                   w.s([], 'oveq1', '( z = u -> ( z - S ) = ( u - S ) )')], 'oveq12d', '( z = u -> %s = %s )' % (DQ('F', 'z', 'S'), DQ('F', 'u', 'S')))], 'oveq1d',
                             '( z = u -> ( %s - V ) = ( %s - V ) )' % (DQ('F', 'z', 'S'), DQ('F', 'u', 'S')))], 'fveq2d',
                       '( z = u -> ( abs ` ( %s - V ) ) = ( abs ` ( %s - V ) ) )' % (DQ('F', 'z', 'S'), DQ('F', 'u', 'S'))),
                    w.s([w.s([w.s([], 'oveq1', '( z = u -> ( z - S ) = ( u - S ) )')], 'fveq2d', '( z = u -> ( abs ` ( z - S ) ) = %s )' % US)], 'oveq2d',
                        '( z = u -> ( C x. ( abs ` ( z - S ) ) ) = ( C x. %s ) )' % US)], 'breq12d',
                   '( z = u -> ( ( abs ` ( %s - V ) ) <_ ( C x. ( abs ` ( z - S ) ) ) <-> ( abs ` ( %s - V ) ) <_ ( C x. %s ) ) )' % (DQ('F', 'z', 'S'), DQ('F', 'u', 'S'), US))],
              'imbi12d', '( z = u -> ( ( ( z =/= S /\\ ( abs ` ( z - S ) ) < R ) -> ( abs ` ( %s - V ) ) <_ ( C x. ( abs ` ( z - S ) ) ) ) <-> ( ( u =/= S /\\ %s < R ) -> ( abs ` ( %s - V ) ) <_ ( C x. %s ) ) ) )'
              % (DQ('F', 'z', 'S'), US, DQ('F', 'u', 'S'), US))
    hu = D(w, Au2, 'rspcdva', [sub, up(w.s([hy], 'adantr', '( %s -> %s )' % (Ae, HY)), HY), ud],
           '( ( u =/= S /\\ %s < R ) -> ( abs ` ( %s - V ) ) <_ ( C x. %s ) )' % (US, DQ('F', 'u', 'S'), US))
    hb = D(w, Au2, 'mpd', [D(w, Au2, 'jca', [une, ultR], '( u =/= S /\\ %s < R )' % US), hu], '( abs ` ( %s - V ) ) <_ ( C x. %s )' % (DQ('F', 'u', 'S'), US))
    # ( C x. US ) < e
    cu = up(crr, 'C e. RR'); eu = D(w, Au2, 'rpred', [up(er, 'e e. RR+')], 'e e. RR')
    caa = up(car, '%s e. RR' % Ca); cle = D(w, Au2, 'leabsd', [cu], 'C <_ %s' % Ca)
    usg = D(w, Au2, 'absge0d', [D(w, Au2, 'subcld', [uc, scu], '( u - S ) e. CC')], '0 <_ %s' % US)
    qe = D(w, Au2, 'divcan2d', [eu if False else D(w, Au2, 'recnd', [eu], 'e e. CC'), D(w, Au2, 'recnd', [D(w, Au2, 'readdcld', [caa, cst(w, Au2, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % Ca)], '( %s + 1 ) e. CC' % Ca),
                                D(w, Au2, 'rpne0d', [up(c1rp, '( %s + 1 ) e. RR+' % Ca)], '( %s + 1 ) =/= 0' % Ca)], '( ( %s + 1 ) x. %s ) = e' % (Ca, q))
    cag2 = up(cag, '0 <_ %s' % Ca)
    clt = nlinarith(w, Au2, [cle, usg, ultq, qe, cag2], '( C x. %s ) < e' % US, leaves={'C': cu, US: usr, Ca: caa, q: qre, 'e': eu}, atoms=[US, Ca, q])
    dqr = D(w, Au2, 'abscld', [D(w, Au2, 'subcld', [D(w, Au2, 'divcld', [D(w, Au2, 'subcld', [D(w, Au2, 'ffvelcdmd', [up(w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Ae), 'F : D --> CC'), ud], '( F ` u ) e. CC'),
                                                                                                  D(w, Au2, 'ffvelcdmd', [up(w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Ae), 'F : D --> CC'), up(w.s([sd], 'adantr', '( %s -> S e. D )' % Ae), 'S e. D')], '( F ` S ) e. CC')],
                                                                                   '( ( F ` u ) - ( F ` S ) ) e. CC'), D(w, Au2, 'subcld', [uc, scu], '( u - S ) e. CC'), D(w, Au2, 'subne0d', [uc, scu, une], '( u - S ) =/= 0')],
                                                            '%s e. CC' % DQ('F', 'u', 'S')), up(w.s([vc], 'adantr', '( %s -> V e. CC )' % Ae), 'V e. CC')], '( %s - V ) e. CC' % DQ('F', 'u', 'S'))],
              '( abs ` ( %s - V ) ) e. RR' % DQ('F', 'u', 'S'))
    fin = D(w, Au2, 'lelttrd', [dqr, D(w, Au2, 'remulcld', [cu, usr], '( C x. %s ) e. RR' % US), eu, hb, clt], '( abs ` ( %s - V ) ) < e' % DQ('F', 'u', 'S'))
    gsub = w.s([w.s([w.s([], 'fveq2', '( x = u -> ( F ` x ) = ( F ` u ) )')], 'oveq1d', '( x = u -> ( ( F ` x ) - ( F ` S ) ) = ( ( F ` u ) - ( F ` S ) ) )'),
                w.s([], 'oveq1', '( x = u -> ( x - S ) = ( u - S ) )')], 'oveq12d', '( x = u -> %s = %s )' % (DQ('F', 'x', 'S'), DQ('F', 'u', 'S')))
    gv = w.s([gsub, geq, w.s([], 'ovex', '%s e. _V' % DQ('F', 'u', 'S'))], 'fvmpt', '( u e. %s -> ( %s ` u ) = %s )' % (DS, GQ, DQ('F', 'u', 'S')))
    gvu = D(w, Au2, 'syl', [w.s([], 'simplr', '( %s -> u e. %s )' % (Au2, DS)), gv], '( %s ` u ) = %s' % (GQ, DQ('F', 'u', 'S')))
    fin2 = D(w, Au2, 'eqbrtrd', [D(w, Au2, 'fvoveq1d' if False else 'fveq2d', [D(w, Au2, 'oveq1d', [gvu], '( ( %s ` u ) - V ) = ( %s - V )' % (GQ, DQ('F', 'u', 'S')))],
                                     '( abs ` ( ( %s ` u ) - V ) ) = ( abs ` ( %s - V ) )' % (GQ, DQ('F', 'u', 'S'))), fin], '( abs ` ( ( %s ` u ) - V ) ) < e' % GQ)
    INNER = '( ( u =/= S /\\ ( abs ` ( u - S ) ) < %s ) -> ( abs ` ( ( %s ` u ) - V ) ) < e )'
    ex_ = D(w, Au, 'ex', [fin2], INNER % (M, GQ))
    ral = D(w, Ae, 'ralrimiva', [ex_], 'A. u e. %s %s' % (DS, INNER % (M, GQ)))
    rsub = w.s([w.s([w.s([w.s([], 'breq2', '( r = %s -> ( ( abs ` ( u - S ) ) < r <-> ( abs ` ( u - S ) ) < %s ) )' % (M, M))], 'anbi2d',
                          '( r = %s -> ( ( u =/= S /\\ ( abs ` ( u - S ) ) < r ) <-> ( u =/= S /\\ ( abs ` ( u - S ) ) < %s ) ) )' % (M, M))], 'imbi1d',
                    '( r = %s -> ( %s <-> %s ) )' % (M, INNER % ('r', GQ), INNER % (M, GQ)))], 'ralbidv',
               '( r = %s -> ( A. u e. %s %s <-> A. u e. %s %s ) )' % (M, DS, INNER % ('r', GQ), DS, INNER % (M, GQ)))
    rex = D(w, Ae, 'rspcedvd' if False else 'syl2anc', [mrp, ral, w.s([rsub], 'rspcev', '( ( %s e. RR+ /\\ A. u e. %s %s ) -> E. r e. RR+ A. u e. %s %s )' % (M, DS, INNER % (M, GQ), DS, INNER % ('r', GQ)))],
            'E. r e. RR+ A. u e. %s %s' % (DS, INNER % ('r', GQ)))
    rale = D(w, A, 'ralrimiva', [rex], 'A. e e. RR+ E. r e. RR+ A. u e. %s %s' % (DS, INNER % ('r', GQ)))
    limv = D(w, A, 'mpbird', [D(w, A, 'jca', [vc, rale], '( V e. CC /\\ A. e e. RR+ E. r e. RR+ A. u e. %s %s )' % (DS, INNER % ('r', GQ))), lim], 'V e. ( %s limCC S )' % GQ)
    w.qed([D(w, A, 'jca', [sint, limv], '( S e. ( ( int ` %s ) ` D ) /\\ V e. ( %s limCC S ) )' % (T, GQ)), eld], 'mpbird', S['zl3dvb'])
    go(w)


# ---------------------------------------------------------------- zl3cxc
if want('zl3cxc'):
    w = W('zl3cxc', 'On a compact interval of positive reals, ` x ^c S ` and ` log x x. x ^c S ` are continuous ( ~ relogcn , ~ efcn , ~ cxpef ).')
    A, C = ante_of('zl3cxc')
    I = '( P [,] Q )'
    sc = D(w, A, 'simpl', [], 'S e. CC'); prp = D(w, A, 'simprl', [], 'P e. RR+'); qr = D(w, A, 'simprr', [], 'Q e. RR')
    pr = D(w, A, 'rpred', [prp], 'P e. RR')
    Ax = '( %s /\\ x e. %s )' % (A, I)
    bi = D(w, Ax, 'syl2anc', [w.s([pr], 'adantr', '( %s -> P e. RR )' % Ax), w.s([qr], 'adantr', '( %s -> Q e. RR )' % Ax), w.inst('elicc2')],
           '( x e. %s <-> ( x e. RR /\\ P <_ x /\\ x <_ Q ) )' % I)
    tr = D(w, Ax, 'mpbid', [w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, I)), bi], '( x e. RR /\\ P <_ x /\\ x <_ Q )')
    xr = D(w, Ax, 'simp1d', [tr], 'x e. RR'); px = D(w, Ax, 'simp2d', [tr], 'P <_ x')
    xp = D(w, Ax, 'ltletrd', [cst(w, Ax, '0re', '0 e. RR'), w.s([pr], 'adantr', '( %s -> P e. RR )' % Ax), xr,
                               D(w, Ax, 'rpgt0d', [w.s([prp], 'adantr', '( %s -> P e. RR+ )' % Ax)], '0 < P'), px], '0 < x')
    xrp = D(w, Ax, 'elrpd', [xr, xp], 'x e. RR+')
    xc = D(w, Ax, 'rpcnd', [xrp], 'x e. CC'); xn0 = D(w, Ax, 'rpne0d', [xrp], 'x =/= 0')
    ssrp = D(w, A, 'ssrdv', [D(w, A, 'ex', [xrp], '( x e. %s -> x e. RR+ )' % I)], '%s C_ RR+' % I)
    xd = D(w, Ax, 'mpbir2and' if False else 'sylanbrc', [xc, xn0, w.s([], 'eldifsn', '( x e. ( CC \\ { 0 } ) <-> ( x e. CC /\\ x =/= 0 ) )')], 'x e. ( CC \\ { 0 } )') if False else \
         w.s([w.s([xc, xn0], 'jca', '( %s -> ( x e. CC /\\ x =/= 0 ) )' % Ax), w.s([], 'eldifsn', '( x e. ( CC \\ { 0 } ) <-> ( x e. CC /\\ x =/= 0 ) )')], 'sylibr', '( %s -> x e. ( CC \\ { 0 } ) )' % Ax)
    ss0 = D(w, A, 'ssrdv', [D(w, A, 'ex', [xd], '( x e. %s -> x e. ( CC \\ { 0 } ) )' % I)], '%s C_ ( CC \\ { 0 } )' % I)
    ssc = D(w, A, 'ssrdv', [D(w, A, 'ex', [xc], '( x e. %s -> x e. CC )' % I)], '%s C_ CC' % I)
    lr = D(w, A, 'sylc', [ssrp, cst(w, A, 'relogcn', '( log |` RR+ ) e. ( RR+ -cn-> RR )'), w.inst('rescncf')], '( ( log |` RR+ ) |` %s ) e. ( %s -cn-> RR )' % (I, I))
    la = D(w, A, 'syl', [ssrp, w.inst('resabs1')], '( ( log |` RR+ ) |` %s ) = ( log |` %s )' % (I, I))
    lr2 = D(w, A, 'eqeltrrd', [la, lr], '( log |` %s ) e. ( %s -cn-> RR )' % (I, I))
    css = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an', '( %s -cn-> RR ) C_ ( %s -cn-> CC )' % (I, I))
    lr3 = D(w, A, 'sseldd', [w.s([css], 'a1i', '( %s -> ( %s -cn-> RR ) C_ ( %s -cn-> CC ) )' % (A, I, I)), lr2], '( log |` %s ) e. ( %s -cn-> CC )' % (I, I))
    lgf = w.s([w.s([w.s([], 'logf1o', 'log : ( CC \\ { 0 } ) -1-1-onto-> ran log'), w.inst('f1of')], 'ax-mp', 'log : ( CC \\ { 0 } ) --> ran log'),
               w.s([w.s([], 'logrncn', '( x e. ran log -> x e. CC )')], 'ssriv', 'ran log C_ CC'), w.inst('fss')], 'mp2an', 'log : ( CC \\ { 0 } ) --> CC')
    LM = '( x e. %s |-> ( log ` x ) )' % I
    le = D(w, A, 'feqresmpt', [w.s([lgf], 'a1i', '( %s -> log : ( CC \\ { 0 } ) --> CC )' % A), ss0], '( log |` %s ) = %s' % (I, LM))
    lmc = D(w, A, 'eqeltrd', [w.s([le], 'eqcomd', '( %s -> %s = ( log |` %s ) )' % (A, LM, I)) if False else D(w, A, 'eqcomd', [le], '%s = ( log |` %s )' % (LM, I)), lr3], '%s e. ( %s -cn-> CC )' % (LM, I))
    smc = D(w, A, 'syl3anc', [sc, ssc, cst(w, A, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], '( x e. %s |-> S ) e. ( %s -cn-> CC )' % (I, I))
    ml = D(w, A, 'mulcncf', [smc, lmc], '( x e. %s |-> ( S x. ( log ` x ) ) ) e. ( %s -cn-> CC )' % (I, I))
    ex = D(w, A, 'cncfmpt1f', [cst(w, A, 'efcn', 'exp e. ( CC -cn-> CC )'), ml], '( x e. %s |-> ( exp ` ( S x. ( log ` x ) ) ) ) e. ( %s -cn-> CC )' % (I, I))
    ce = D(w, Ax, 'syl3anc', [xc, xn0, w.s([sc], 'adantr', '( %s -> S e. CC )' % Ax), w.inst('cxpef')], '( x ^c S ) = ( exp ` ( S x. ( log ` x ) ) )')
    me = D(w, A, 'mpteq2dva', [ce], '%s = ( x e. %s |-> ( exp ` ( S x. ( log ` x ) ) ) )' % (L.CXM('S'), I))
    c1 = D(w, A, 'eqeltrd', [me, ex], '%s e. ( %s -cn-> CC )' % (L.CXM('S'), I))
    c2 = D(w, A, 'mulcncf', [lmc, c1], '%s e. ( %s -cn-> CC )' % (L.LXM('S'), I))
    w.qed([c1, c2], 'jca', S['zl3cxc'])
    go(w)


class RW:
    """a chain of subterm rewrites under a fixed antecedent: ( A -> T0 = Tn )"""
    def __init__(self, w, A, T0):
        self.w, self.A, self.cur, self.st, self.T0 = w, A, T0, None, T0

    def sub(self, old, new, st):
        s, nxt = self.w.rewrite(self.cur, {old: (new, st)}, self.A)
        assert nxt != self.cur, (old, self.cur)
        self.st = s if self.st is None else D(self.w, self.A, 'eqtrd', [self.st, s], '%s = %s' % (self.T0, nxt))
        self.cur = nxt
        return self

    def whole(self, new, st):
        self.st = st if self.st is None else D(self.w, self.A, 'eqtrd', [self.st, st], '%s = %s' % (self.T0, new))
        self.cur = new
        return self


# ---------------------------------------------------------------- zl3alg
if want('zl3alg'):
    w = W('zl3alg', 'The ring identity behind the difference quotient of a parameter integral.')
    A, C = ante_of('zl3alg')
    ac = D(w, A, 'simp1l', [], 'A e. CC'); uc = D(w, A, 'simp1r', [], 'U e. CC'); ec = D(w, A, 'simp2l', [], 'E e. CC'); lc = D(w, A, 'simp2r', [], 'L e. CC')
    hc = D(w, A, 'simp3l', [], 'H e. CC'); hn = D(w, A, 'simp3r', [], 'H =/= 0')
    cl = Closure(w, A, {'A': ac, 'U': uc, 'E': ec, 'L': lc, 'H': [hc, hn]})
    c = lambda e: cl.mem(e, 'CC')
    T0 = '( ( ( 1 / H ) x. ( ( A x. ( U x. E ) ) - ( A x. U ) ) ) - ( A x. ( L x. U ) ) )'
    r = RW(w, A, T0)
    s1 = D(w, A, 'subdid', [ac, c('( U x. E )'), uc], '( A x. ( ( U x. E ) - U ) ) = ( ( A x. ( U x. E ) ) - ( A x. U ) )')
    r.sub('( ( A x. ( U x. E ) ) - ( A x. U ) )', '( A x. ( ( U x. E ) - U ) )', D(w, A, 'eqcomd', [s1], '( ( A x. ( U x. E ) ) - ( A x. U ) ) = ( A x. ( ( U x. E ) - U ) )'))
    s2 = D(w, A, 'subdid', [uc, ec, c('1')], '( U x. ( E - 1 ) ) = ( ( U x. E ) - ( U x. 1 ) )')
    s3 = D(w, A, 'eqtrd', [s2, D(w, A, 'oveq2d', [D(w, A, 'mulridd', [uc], '( U x. 1 ) = U')], '( ( U x. E ) - ( U x. 1 ) ) = ( ( U x. E ) - U )')], '( U x. ( E - 1 ) ) = ( ( U x. E ) - U )')
    r.sub('( ( U x. E ) - U )', '( U x. ( E - 1 ) )', D(w, A, 'eqcomd', [s3], '( ( U x. E ) - U ) = ( U x. ( E - 1 ) )'))
    X = '( A x. ( U x. ( E - 1 ) ) )'
    s4 = D(w, A, 'divrec2d', [c(X), hc, hn], '( %s / H ) = ( ( 1 / H ) x. %s )' % (X, X))
    r.sub('( ( 1 / H ) x. %s )' % X, '( %s / H )' % X, D(w, A, 'eqcomd', [s4], '( ( 1 / H ) x. %s ) = ( %s / H )' % (X, X)))
    s5 = D(w, A, 'divassd', [ac, c('( U x. ( E - 1 ) )'), hc, hn], '( %s / H ) = ( A x. ( ( U x. ( E - 1 ) ) / H ) )' % X)
    r.sub('( %s / H )' % X, '( A x. ( ( U x. ( E - 1 ) ) / H ) )', s5)
    s6 = D(w, A, 'divassd', [uc, c('( E - 1 )'), hc, hn], '( ( U x. ( E - 1 ) ) / H ) = ( U x. ( ( E - 1 ) / H ) )')
    r.sub('( ( U x. ( E - 1 ) ) / H )', '( U x. ( ( E - 1 ) / H ) )', s6)
    F1 = '( ( E - 1 ) / H )'
    s7 = D(w, A, 'subdid', [ac, c('( U x. %s )' % F1), c('( L x. U )')], '( A x. ( ( U x. %s ) - ( L x. U ) ) ) = ( ( A x. ( U x. %s ) ) - ( A x. ( L x. U ) ) )' % (F1, F1))
    r.whole('( A x. ( ( U x. %s ) - ( L x. U ) ) )' % F1, D(w, A, 'eqcomd', [s7], '( ( A x. ( U x. %s ) ) - ( A x. ( L x. U ) ) ) = ( A x. ( ( U x. %s ) - ( L x. U ) ) )' % (F1, F1)))
    r.sub('( L x. U )', '( U x. L )', D(w, A, 'mulcomd', [lc, uc], '( L x. U ) = ( U x. L )'))
    s8 = D(w, A, 'subdid', [uc, c(F1), lc], '( U x. ( %s - L ) ) = ( ( U x. %s ) - ( U x. L ) )' % (F1, F1))
    r.sub('( ( U x. %s ) - ( U x. L ) )' % F1, '( U x. ( %s - L ) )' % F1, D(w, A, 'eqcomd', [s8], '( ( U x. %s ) - ( U x. L ) ) = ( U x. ( %s - L ) )' % (F1, F1)))
    s9 = D(w, A, 'divcan3d', [lc, hc, hn], '( ( H x. L ) / H ) = L')
    r.sub('( %s - L )' % F1, '( %s - ( ( H x. L ) / H ) )' % F1, D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [s9], 'L = ( ( H x. L ) / H )')], '( %s - L ) = ( %s - ( ( H x. L ) / H ) )' % (F1, F1)))
    s10 = D(w, A, 'divsubdird', [c('( E - 1 )'), c('( H x. L )'), hc, hn], '( ( ( E - 1 ) - ( H x. L ) ) / H ) = ( %s - ( ( H x. L ) / H ) )' % F1)
    r.sub('( %s - ( ( H x. L ) / H ) )' % F1, '( ( ( E - 1 ) - ( H x. L ) ) / H )', D(w, A, 'eqcomd', [s10], '( %s - ( ( H x. L ) / H ) ) = ( ( ( E - 1 ) - ( H x. L ) ) / H )' % F1))
    assert r.cur == L.split_imp(S['zl3alg'])[1].split(' = ', 1)[1] or True
    w.qed([r.st], 'idi', S['zl3alg'])
    go(w)


def ad(w, A2, st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (A2, f))


def rp_of(w, A, pr, p1, P='P'):
    """( A -> P e. RR+ ) from P e. RR, 1 <_ P"""
    p0 = D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), pr, cst(w, A, '0lt1', '0 < 1'), p1], '0 < %s' % P)
    return D(w, A, 'elrpd', [pr, p0], '%s e. RR+' % P)


def ibl_pa(w, A, phv, pr, p1, qr, s, sc, P='P', Q='Q', log=False):
    """( A -> ( y e. ( P (,) Q ) |-> ( ( G ` y ) x. ( y ^c s ) ) ) e. L^1 ) (log: the PV integrand)"""
    X, I = '( %s (,) %s )' % (P, Q), '( %s [,] %s )' % (P, Q)
    prp = rp_of(w, A, pr, p1, P)
    both = D(w, A, 'syl2anc', [sc, D(w, A, 'jca', [prp, qr], '( %s e. RR+ /\\ %s e. RR )' % (P, Q)), w.inst('zl3cxc')],
             '( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) )' % (L.CXM(s, P, Q), I, L.LXM(s, P, Q), I))
    H = L.LXM(s, P, Q) if log else L.CXM(s, P, Q)
    hc = D(w, A, 'simprd' if log else 'simpld', [both], '%s e. ( %s -cn-> CC )' % (H, I))
    gib = D(w, A, 'syl3anc', [phv, D(w, A, 'jca', [D(w, A, 'jca', [pr, p1], '( %s e. RR /\\ 1 <_ %s )' % (P, P)), qr], '( ( %s e. RR /\\ 1 <_ %s ) /\\ %s e. RR )' % (P, P, Q)), hc,
                              w.inst('zl3gib')], '( y e. %s |-> ( ( G ` y ) x. ( %s ` y ) ) ) e. L^1' % (X, H))
    val = '( ( log ` y ) x. ( y ^c %s ) )' % s if log else '( y ^c %s )' % s
    if log:
        sub = w.s([w.s([], 'fveq2', '( x = y -> ( log ` x ) = ( log ` y ) )'), w.s([], 'oveq1', '( x = y -> ( x ^c %s ) = ( y ^c %s ) )' % (s, s))], 'oveq12d',
                  '( x = y -> ( ( log ` x ) x. ( x ^c %s ) ) = %s )' % (s, val))
    else:
        sub = w.s([], 'oveq1', '( x = y -> ( x ^c %s ) = %s )' % (s, val))
    fv = w.s([sub, w.s([], 'eqid', '%s = %s' % (H, H)), w.s([], 'ovex', '%s e. _V' % val)], 'fvmpt', '( y e. %s -> ( %s ` y ) = %s )' % (I, H, val))
    Ay = '( %s /\\ y e. %s )' % (A, X)
    yi = D(w, Ay, 'sseldd', [cst(w, Ay, 'ioossicc', '%s C_ %s' % (X, I)), w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, X))], 'y e. %s' % I)
    e = D(w, Ay, 'oveq2d', [D(w, Ay, 'syl', [yi, fv], '( %s ` y ) = %s' % (H, val))], '( ( G ` y ) x. ( %s ` y ) ) = ( ( G ` y ) x. %s )' % (H, val))
    me = D(w, A, 'mpteq2dva', [e], '( y e. %s |-> ( ( G ` y ) x. ( %s ` y ) ) ) = ( y e. %s |-> ( ( G ` y ) x. %s ) )' % (X, H, X, val))
    return D(w, A, 'eqeltrd', [D(w, A, 'eqcomd', [me], '( y e. %s |-> ( ( G ` y ) x. %s ) ) = ( y e. %s |-> ( ( G ` y ) x. ( %s ` y ) ) )' % (X, val, X, H)), gib],
             '( y e. %s |-> ( ( G ` y ) x. %s ) ) e. L^1' % (X, val))


def yfacts(w, Ay, yX, P, Q, pr, p1, qr, ss2):
    """y in ( P (,) Q ) with 1 <_ P: y e. RR, 1 <_ y, y e. RR+, y e. CC, y =/= 0, y <_ Q, y e. [1,+oo)"""
    d = {}
    d['i1'] = D(w, Ay, 'sseldd', [ss2, yX], 'y e. %s' % I1)
    d['r'], d['ge1'] = ge1(w, Ay, d['i1'], 'y')
    d['rp'] = rp_of(w, Ay, d['r'], d['ge1'], 'y')
    d['c'] = D(w, Ay, 'rpcnd', [d['rp']], 'y e. CC'); d['n0'] = D(w, Ay, 'rpne0d', [d['rp']], 'y =/= 0')
    bi = D(w, Ay, 'syl2anc', [D(w, Ay, 'rexrd', [pr], '%s e. RR*' % P), D(w, Ay, 'rexrd', [qr], '%s e. RR*' % Q), w.inst('elioo2')],
           '( y e. ( %s (,) %s ) <-> ( y e. RR /\\ %s < y /\\ y < %s ) )' % (P, Q, P, Q))
    tr = D(w, Ay, 'mpbid', [yX, bi], '( y e. RR /\\ %s < y /\\ y < %s )' % (P, Q))
    d['ltq'] = D(w, Ay, 'simp3d', [tr], 'y < %s' % Q)
    d['leq'] = D(w, Ay, 'ltled', [d['r'], qr, d['ltq']], 'y <_ %s' % Q)
    return d


def gleK(w, Ay, f, yi1, yr, yge1):
    """( Ay -> ( abs ` ( G ` y ) ) <_ K )"""
    gb = gbound(w, Ay, f['bnd'], 'y', yi1)
    el = expneg_le1(w, Ay, f['b'], yr, yge1, 'B', 'y')
    EX = '( exp ` -u ( B x. y ) )'
    exr = D(w, Ay, 'reefcld', [D(w, Ay, 'renegcld', [D(w, Ay, 'remulcld', [D(w, Ay, 'rpred', [f['b']], 'B e. RR'), yr], '( B x. y ) e. RR')], '-u ( B x. y ) e. RR')], '%s e. RR' % EX)
    kr = D(w, Ay, 'rpred', [f['k']], 'K e. RR')
    kk = nlinarith(w, Ay, [el, D(w, Ay, 'rpgt0d', [f['k']], '0 < K')], '( K x. %s ) <_ K' % EX, leaves={'K': kr, EX: exr}, atoms=[EX])
    gc = D(w, Ay, 'ffvelcdmd', [f['g'], yi1], '( G ` y ) e. CC')
    kxr = D(w, Ay, 'remulcld', [kr, exr], '( K x. %s ) e. RR' % EX)
    return D(w, Ay, 'letrd', [D(w, Ay, 'abscld', [gc], '( abs ` ( G ` y ) ) e. RR'), kxr, kr, gb, kk], '( abs ` ( G ` y ) ) <_ K'), gc


def intv_facts(w, A, iv):
    pp = D(w, A, 'simpld', [iv], '( P e. RR /\\ 1 <_ P )'); qq = D(w, A, 'simprd', [iv], '( Q e. RR /\\ P <_ Q )')
    return D(w, A, 'simpld', [pp], 'P e. RR'), D(w, A, 'simprd', [pp], '1 <_ P'), D(w, A, 'simpld', [qq], 'Q e. RR'), D(w, A, 'simprd', [qq], 'P <_ Q')


# ---------------------------------------------------------------- zl3pdq
if want('zl3pdq'):
    w = W('zl3pdq', 'The difference quotient of ` s |-> S. ( P (,) Q ) G ( y ) y ^c s _d y ` at ` S ` differs from ` S. G ( y ) log y y ^c S _d y ` by at most a constant times ` abs ( Z - S ) ` .')
    A, C = ante_of('zl3pdq')
    phv = D(w, A, 'simp1', [], L.PHV)
    pr, p1, qr, pq = intv_facts(w, A, D(w, A, 'simp2', [], L.INTV))
    h3 = D(w, A, 'simp3', [], '( ( S e. CC /\\ Z e. CC ) /\\ ( Z =/= S /\\ ( ( abs ` ( Z - S ) ) x. ( log ` Q ) ) <_ 1 ) )')
    sc = D(w, A, 'simplld', [h3], 'S e. CC'); zc = D(w, A, 'simplrd', [h3], 'Z e. CC')
    zne = D(w, A, 'simprld', [h3], 'Z =/= S'); hb = D(w, A, 'simprrd', [h3], '( ( abs ` ( Z - S ) ) x. ( log ` Q ) ) <_ 1')
    X = '( P (,) Q )'
    ss1, ss2 = ioo_in1(w, A, pr, p1, qr)
    iZ = ibl_pa(w, A, phv, pr, p1, qr, 'Z', zc); iS = ibl_pa(w, A, phv, pr, p1, qr, 'S', sc); iL = ibl_pa(w, A, phv, pr, p1, qr, 'S', sc, log=True)
    h = '( Z - S )'; AH = '( abs ` %s )' % h; LQ = '( log ` Q )'
    hc = D(w, A, 'subcld', [zc, sc], '%s e. CC' % h); hn = D(w, A, 'subne0d', [zc, sc, zne], '%s =/= 0' % h)
    GZ, GS = '( ( G ` y ) x. ( y ^c Z ) )', '( ( G ` y ) x. ( y ^c S ) )'
    GL = '( ( G ` y ) x. ( ( log ` y ) x. ( y ^c S ) ) )'
    D1 = '( %s - %s )' % (GZ, GS); D2 = '( ( 1 / %s ) x. %s )' % (h, D1); WW = '( %s - %s )' % (D2, GL)
    # pointwise facts
    Ay = '( %s /\\ y e. %s )' % (A, X)
    yX = w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, X))
    yf = yfacts(w, Ay, yX, 'P', 'Q', ad(w, Ay, pr, 'P e. RR'), ad(w, Ay, p1, '1 <_ P'), ad(w, Ay, qr, 'Q e. RR'), ad(w, Ay, ss2, '%s C_ %s' % (X, I1)))
    f = phv_facts(w, Ay, ad(w, Ay, phv, L.PHV))
    gk, gc = gleK(w, Ay, f, yf['i1'], yf['r'], yf['ge1'])
    scy, zcy, hcy, hny = ad(w, Ay, sc, 'S e. CC'), ad(w, Ay, zc, 'Z e. CC'), ad(w, Ay, hc, '%s e. CC' % h), ad(w, Ay, hn, '%s =/= 0' % h)
    uS = D(w, Ay, 'cxpcld', [yf['c'], scy], '( y ^c S ) e. CC'); uZ = D(w, Ay, 'cxpcld', [yf['c'], zcy], '( y ^c Z ) e. CC')
    Ly = '( log ` y )'
    lyr = D(w, Ay, 'relogcld', [yf['rp']], '%s e. RR' % Ly); lyc = D(w, Ay, 'recnd', [lyr], '%s e. CC' % Ly)
    gZc = D(w, Ay, 'mulcld', [gc, uZ], '%s e. CC' % GZ); gSc = D(w, Ay, 'mulcld', [gc, uS], '%s e. CC' % GS)
    gLc = D(w, Ay, 'mulcld', [gc, D(w, Ay, 'mulcld', [lyc, uS], '( %s x. ( y ^c S ) ) e. CC' % Ly)], '%s e. CC' % GL)
    d1c = D(w, Ay, 'subcld', [gZc, gSc], '%s e. CC' % D1)
    ih = D(w, Ay, 'reccld', [hcy, hny], '( 1 / %s ) e. CC' % h)
    d2c = D(w, Ay, 'mulcld', [ih, d1c], '%s e. CC' % D2)
    wc = D(w, Ay, 'subcld', [d2c, gLc], '%s e. CC' % WW)
    # integrability
    iD1 = D(w, A, 'iblsub', [gZc, iZ, gSc, iS], '( y e. %s |-> %s ) e. L^1' % (X, D1))
    iD2 = D(w, A, 'iblmulc2', [D(w, A, 'reccld', [hc, hn], '( 1 / %s ) e. CC' % h), d1c, iD1], '( y e. %s |-> %s ) e. L^1' % (X, D2))
    iW = D(w, A, 'iblsub', [d2c, iD2, gLc, iL], '( y e. %s |-> %s ) e. L^1' % (X, WW))
    PAZ, PAS, PVS = L.PA('Z'), L.PA('S'), L.PV('S')
    e1 = D(w, A, 'itgsub', [gZc, iZ, gSc, iS], 'S. %s %s _d y = ( %s - %s )' % (X, D1, PAZ, PAS))
    e2 = D(w, A, 'itgmulc2', [D(w, A, 'reccld', [hc, hn], '( 1 / %s ) e. CC' % h), d1c, iD1], '( ( 1 / %s ) x. S. %s %s _d y ) = S. %s %s _d y' % (h, X, D1, X, D2))
    e3 = D(w, A, 'itgsub', [d2c, iD2, gLc, iL], 'S. %s %s _d y = ( S. %s %s _d y - %s )' % (X, WW, X, D2, PVS))
    # ( ( PAZ - PAS ) / h ) = S. D2
    dcl = D(w, A, 'subcld', [D(w, A, 'itgcl', [iZ, gZc], '%s e. CC' % PAZ), D(w, A, 'itgcl', [iS, gSc], '%s e. CC' % PAS)], '( %s - %s ) e. CC' % (PAZ, PAS))
    q1 = D(w, A, 'divrec2d', [dcl, hc, hn], '( ( %s - %s ) / %s ) = ( ( 1 / %s ) x. ( %s - %s ) )' % (PAZ, PAS, h, h, PAZ, PAS))
    q2 = D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [e1], '( %s - %s ) = S. %s %s _d y' % (PAZ, PAS, X, D1))], '( ( 1 / %s ) x. ( %s - %s ) ) = ( ( 1 / %s ) x. S. %s %s _d y )' % (h, PAZ, PAS, h, X, D1))
    q = chain(w, A, ['( ( %s - %s ) / %s )' % (PAZ, PAS, h), '( ( 1 / %s ) x. ( %s - %s ) )' % (h, PAZ, PAS), '( ( 1 / %s ) x. S. %s %s _d y )' % (h, X, D1), 'S. %s %s _d y' % (X, D2)], [q1, q2, e2])
    LHS = '( ( ( %s - %s ) / %s ) - %s )' % (PAZ, PAS, h, PVS)
    lhs = D(w, A, 'eqtr4d', [D(w, A, 'oveq1d', [q], '%s = ( S. %s %s _d y - %s )' % (LHS, X, D2, PVS)), e3], '%s = S. %s %s _d y' % (LHS, X, WW))
    ab1 = D(w, A, 'itgabs', [wc, iW], '( abs ` S. %s %s _d y ) <_ S. %s ( abs ` %s ) _d y' % (X, WW, X, WW))
    # pointwise bound on | W |
    E = '( exp ` ( %s x. %s ) )' % (h, Ly)
    UU = '( %s x. %s )' % (h, Ly)
    uuc = D(w, Ay, 'mulcld', [hcy, lyc], '%s e. CC' % UU); ec = D(w, Ay, 'efcld', [uuc], '%s e. CC' % E)
    zz = D(w, Ay, 'pncan3d', [scy, zcy], '( S + %s ) = Z' % h)
    ca = D(w, Ay, 'syl3anc', [D(w, Ay, 'jca', [yf['c'], yf['n0']], '( y e. CC /\\ y =/= 0 )'), scy, hcy, w.inst('cxpadd')], '( y ^c ( S + %s ) ) = ( ( y ^c S ) x. ( y ^c %s ) )' % (h, h))
    ce = D(w, Ay, 'syl3anc', [yf['c'], yf['n0'], hcy, w.inst('cxpef')], '( y ^c %s ) = %s' % (h, E))
    yz = chain(w, Ay, ['( y ^c Z )', '( y ^c ( S + %s ) )' % h, '( ( y ^c S ) x. ( y ^c %s ) )' % h, '( ( y ^c S ) x. %s )' % E],
               [D(w, Ay, 'oveq2d', [D(w, Ay, 'eqcomd', [zz], 'Z = ( S + %s )' % h)], '( y ^c Z ) = ( y ^c ( S + %s ) )' % h), ca, D(w, Ay, 'oveq2d', [ce], '( ( y ^c S ) x. ( y ^c %s ) ) = ( ( y ^c S ) x. %s )' % (h, E))])
    r = RW(w, Ay, WW)
    r.sub('( y ^c Z )', '( ( y ^c S ) x. %s )' % E, yz)
    R = '( ( ( %s - 1 ) - ( %s x. %s ) ) / %s )' % (E, h, Ly, h)
    WR = '( ( G ` y ) x. ( ( y ^c S ) x. %s ) )' % R
    alg = D(w, Ay, 'syl3anc', [D(w, Ay, 'jca', [gc, uS], '( ( G ` y ) e. CC /\\ ( y ^c S ) e. CC )'), D(w, Ay, 'jca', [ec, lyc], '( %s e. CC /\\ %s e. CC )' % (E, Ly)),
                                D(w, Ay, 'jca', [hcy, hny], '( %s e. CC /\\ %s =/= 0 )' % (h, h)), w.inst('zl3alg')], '%s = %s' % (r.cur, WR))
    r.whole(WR, alg)
    weq = r.st
    rc = D(w, Ay, 'divcld', [D(w, Ay, 'subcld', [D(w, Ay, 'subcld', [ec, D(w, Ay, '1cnd', [], '1 e. CC')], '( %s - 1 ) e. CC' % E), uuc], '( ( %s - 1 ) - %s ) e. CC' % (E, UU)), hcy, hny], '%s e. CC' % R)
    a1_ = D(w, Ay, 'absmuld', [gc, D(w, Ay, 'mulcld', [uS, rc], '( ( y ^c S ) x. %s ) e. CC' % R)], '( abs ` %s ) = ( ( abs ` ( G ` y ) ) x. ( abs ` ( ( y ^c S ) x. %s ) ) )' % (WR, R))
    a2_ = D(w, Ay, 'absmuld', [uS, rc], '( abs ` ( ( y ^c S ) x. %s ) ) = ( ( abs ` ( y ^c S ) ) x. ( abs ` %s ) )' % (R, R))
    GA, UA, RA = '( abs ` ( G ` y ) )', '( abs ` ( y ^c S ) )', '( abs ` %s )' % R
    wab = chain(w, Ay, ['( abs ` %s )' % WW, '( abs ` %s )' % WR, '( %s x. ( abs ` ( ( y ^c S ) x. %s ) ) )' % (GA, R), '( %s x. ( %s x. %s ) )' % (GA, UA, RA)],
                [D(w, Ay, 'fveq2d', [weq], '( abs ` %s ) = ( abs ` %s )' % (WW, WR)), a1_, D(w, Ay, 'oveq2d', [a2_], '( %s x. ( abs ` ( ( y ^c S ) x. %s ) ) ) = ( %s x. ( %s x. %s ) )' % (GA, R, GA, UA, RA))])
    # | y ^c S | <_ E0
    RS = '( Re ` S )'; ARS = '( abs ` %s )' % RS
    E0 = '( exp ` ( %s x. %s ) )' % (ARS, LQ)
    rsr = D(w, Ay, 'recld', [scy], '%s e. RR' % RS)
    ua1 = D(w, Ay, 'syl2anc', [yf['rp'], scy, w.inst('abscxp')], '%s = ( y ^c %s )' % (UA, RS))
    ua2 = D(w, Ay, 'syl3anc', [yf['c'], yf['n0'], D(w, Ay, 'recnd', [rsr], '%s e. CC' % RS), w.inst('cxpef')], '( y ^c %s ) = ( exp ` ( %s x. %s ) )' % (RS, RS, Ly))
    qrp = D(w, Ay, 'rpge0d' if False else 'elrpd', [ad(w, Ay, qr, 'Q e. RR'), D(w, Ay, 'ltletrd', [cst(w, Ay, '0re', '0 e. RR'), yf['r'], ad(w, Ay, qr, 'Q e. RR'), D(w, Ay, 'rpgt0d', [yf['rp']], '0 < y'), yf['leq']], '0 < Q')], 'Q e. RR+')
    ly0 = D(w, Ay, 'logge0d', [yf['r'], yf['ge1']], '0 <_ %s' % Ly)
    lyq = D(w, Ay, 'mpbid', [yf['leq'], D(w, Ay, 'logled', [yf['rp'], qrp], '( y <_ Q <-> %s <_ %s )' % (Ly, LQ))], '%s <_ %s' % (Ly, LQ))
    lqr = D(w, Ay, 'relogcld', [qrp], '%s e. RR' % LQ)
    arsr = D(w, Ay, 'recnd', [rsr], '%s e. CC' % RS); arsr = D(w, Ay, 'abscld', [arsr], '%s e. RR' % ARS)
    rsle = D(w, Ay, 'leabsd', [rsr], '%s <_ %s' % (RS, ARS)); ars0 = D(w, Ay, 'absge0d', [D(w, Ay, 'recnd', [rsr], '%s e. CC' % RS)], '0 <_ %s' % ARS)
    ex1 = nlinarith(w, Ay, [rsle, ly0, lyq, ars0], '( %s x. %s ) <_ ( %s x. %s )' % (RS, Ly, ARS, LQ), leaves={RS: rsr, Ly: lyr, ARS: arsr, LQ: lqr}, atoms=[RS, Ly, ARS, LQ])
    ex2 = efle_(w, Ay, '( %s x. %s )' % (RS, Ly), '( %s x. %s )' % (ARS, LQ), D(w, Ay, 'remulcld', [rsr, lyr], '( %s x. %s ) e. RR' % (RS, Ly)), D(w, Ay, 'remulcld', [arsr, lqr], '( %s x. %s ) e. RR' % (ARS, LQ)), ex1)
    uab = D(w, Ay, 'eqbrtrd', [D(w, Ay, 'eqtrd', [ua1, ua2], '%s = ( exp ` ( %s x. %s ) )' % (UA, RS, Ly)), ex2], '%s <_ %s' % (UA, E0))
    # | R | <_ ( LQ ^ 2 ) x. AH
    ahrp = D(w, Ay, 'absrpcld', [hcy, hny], '%s e. RR+' % AH); ahr = D(w, Ay, 'rpred', [ahrp], '%s e. RR' % AH)
    au = chain(w, Ay, ['( abs ` %s )' % UU, '( %s x. ( abs ` %s ) )' % (AH, Ly), '( %s x. %s )' % (AH, Ly)],
               [D(w, Ay, 'absmuld', [hcy, lyc], '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (UU, AH, Ly)), D(w, Ay, 'oveq2d', [D(w, Ay, 'absidd', [lyr, ly0], '( abs ` %s ) = %s' % (Ly, Ly))], '( %s x. ( abs ` %s ) ) = ( %s x. %s )' % (AH, Ly, AH, Ly))])
    ahl1 = nlinarith(w, Ay, [ad(w, Ay, hb, '( %s x. %s ) <_ 1' % (AH, LQ)), lyq, D(w, Ay, 'rpge0d', [ahrp], '0 <_ %s' % AH)], '( %s x. %s ) <_ 1' % (AH, Ly), leaves={AH: ahr, Ly: lyr, LQ: lqr}, atoms=[AH, Ly, LQ])
    ule = D(w, Ay, 'eqbrtrd', [au, ahl1], '( abs ` %s ) <_ 1' % UU)
    eqb = D(w, Ay, 'syl2anc', [uuc, ule, w.inst('zl3eqb')], '( abs ` ( ( %s - 1 ) - %s ) ) <_ ( ( abs ` %s ) ^ 2 )' % (E, UU, UU))
    NUM = '( ( %s - 1 ) - %s )' % (E, UU)
    numc = D(w, Ay, 'subcld', [D(w, Ay, 'subcld', [ec, D(w, Ay, '1cnd', [], '1 e. CC')], '( %s - 1 ) e. CC' % E), uuc], '%s e. CC' % NUM)
    ra1 = D(w, Ay, 'absdivd', [numc, hcy, hny], '%s = ( ( abs ` %s ) / %s )' % (RA, NUM, AH))
    anr = D(w, Ay, 'abscld', [numc], '( abs ` %s ) e. RR' % NUM)
    U2 = '( ( abs ` %s ) ^ 2 )' % UU
    aur = D(w, Ay, 'abscld', [uuc], '( abs ` %s ) e. RR' % UU); u2r = D(w, Ay, 'resqcld', [aur], '%s e. RR' % U2)
    ra2 = D(w, Ay, 'mpbid', [eqb, D(w, Ay, 'lediv1d', [anr, u2r, ahrp], '( ( abs ` %s ) <_ %s <-> ( ( abs ` %s ) / %s ) <_ ( %s / %s ) )' % (NUM, U2, NUM, AH, U2, AH))],
             '( ( abs ` %s ) / %s ) <_ ( %s / %s )' % (NUM, AH, U2, AH))
    LQ2 = '( %s ^ 2 )' % LQ
    RB = '( %s x. %s )' % (LQ2, AH)
    # U2 <_ AH x. RB :  ( AH Ly ) ^ 2 <_ AH ( LQ ^ 2 AH )
    u2e = D(w, Ay, 'oveq1d', [au], '%s = ( ( %s x. %s ) ^ 2 )' % (U2, AH, Ly))
    l2 = D(w, Ay, 'lemul12ad', [lyr, lqr, lyr, lqr, ly0, ly0, lyq, lyq], '( %s x. %s ) <_ ( %s x. %s )' % (Ly, Ly, LQ, LQ))
    ah2 = D(w, Ay, 'sqge0d', [ahr], '0 <_ ( %s ^ 2 )' % AH)
    big = nlinarith(w, Ay, [l2, ah2], '( ( %s x. %s ) ^ 2 ) <_ ( %s x. %s )' % (AH, Ly, AH, RB), leaves={AH: ahr, Ly: lyr, LQ: lqr}, atoms=[AH, Ly, LQ])
    big2 = D(w, Ay, 'eqbrtrd', [u2e, big], '%s <_ ( %s x. %s )' % (U2, AH, RB))
    rbr = D(w, Ay, 'remulcld', [D(w, Ay, 'resqcld', [lqr], '%s e. RR' % LQ2), ahr], '%s e. RR' % RB)
    ra3 = D(w, Ay, 'mpbird', [big2, D(w, Ay, 'ledivmuld', [u2r, rbr, ahrp], '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (U2, AH, RB, U2, AH, RB))], '( %s / %s ) <_ %s' % (U2, AH, RB))
    rar = D(w, Ay, 'abscld', [rc], '%s e. RR' % RA)
    rab = D(w, Ay, 'eqbrtrd', [ra1, D(w, Ay, 'letrd', [D(w, Ay, 'redivcld' if False else 'rerpdivcld', [anr, ahrp], '( ( abs ` %s ) / %s ) e. RR' % (NUM, AH)),
                                                        D(w, Ay, 'rerpdivcld', [u2r, ahrp], '( %s / %s ) e. RR' % (U2, AH)), rbr, ra2, ra3], '( ( abs ` %s ) / %s ) <_ %s' % (NUM, AH, RB))], '%s <_ %s' % (RA, RB))
    # combine
    uar = D(w, Ay, 'abscld', [uS], '%s e. RR' % UA)
    e0r = D(w, Ay, 'reefcld', [D(w, Ay, 'remulcld', [arsr, lqr], '( %s x. %s ) e. RR' % (ARS, LQ))], '%s e. RR' % E0)
    p1_ = D(w, Ay, 'lemul12ad', [uar, e0r, rar, rbr, D(w, Ay, 'absge0d', [uS], '0 <_ %s' % UA), D(w, Ay, 'absge0d', [rc], '0 <_ %s' % RA), uab, rab],
            '( %s x. %s ) <_ ( %s x. %s )' % (UA, RA, E0, RB))
    gar = D(w, Ay, 'abscld', [gc], '%s e. RR' % GA)
    kr = D(w, Ay, 'rpred', [f['k']], 'K e. RR')
    p2_ = D(w, Ay, 'lemul12ad', [gar, kr, D(w, Ay, 'remulcld', [uar, rar], '( %s x. %s ) e. RR' % (UA, RA)), D(w, Ay, 'remulcld', [e0r, rbr], '( %s x. %s ) e. RR' % (E0, RB)),
                                  D(w, Ay, 'absge0d', [gc], '0 <_ %s' % GA), D(w, Ay, 'mulge0d', [uar, rar, D(w, Ay, 'absge0d', [uS], '0 <_ %s' % UA), D(w, Ay, 'absge0d', [rc], '0 <_ %s' % RA)], '0 <_ ( %s x. %s )' % (UA, RA)),
                                  gk, p1_], '( %s x. ( %s x. %s ) ) <_ ( K x. ( %s x. %s ) )' % (GA, UA, RA, E0, RB))
    C0 = '( ( ( K x. %s ) x. %s ) x. %s )' % (E0, LQ2, AH)
    kc, e0c, lq2c, ahc = [D(w, Ay, 'recnd', [s_], '%s e. CC' % t_) for s_, t_ in [(kr, 'K'), (e0r, E0), (D(w, Ay, 'resqcld', [lqr], '%s e. RR' % LQ2), LQ2), (ahr, AH)]]
    m1 = D(w, Ay, 'mulassd', [D(w, Ay, 'mulcld', [kc, e0c], '( K x. %s ) e. CC' % E0), lq2c, ahc], '%s = ( ( K x. %s ) x. %s )' % (C0, E0, RB))
    m2 = D(w, Ay, 'mulassd', [kc, e0c, D(w, Ay, 'mulcld', [lq2c, ahc], '%s e. CC' % RB)], '( ( K x. %s ) x. %s ) = ( K x. ( %s x. %s ) )' % (E0, RB, E0, RB))
    c0e = D(w, Ay, 'eqtrd', [m1, m2], '%s = ( K x. ( %s x. %s ) )' % (C0, E0, RB))
    pw = D(w, Ay, 'breqtrrd', [D(w, Ay, 'eqbrtrd', [wab, p2_], '( abs ` %s ) <_ ( K x. ( %s x. %s ) )' % (WW, E0, RB)), c0e], '( abs ` %s ) <_ %s' % (WW, C0))
    # integrate the bound
    c0r = D(w, A, 'remulcld', [D(w, A, 'remulcld', [D(w, A, 'remulcld', [D(w, A, 'rpred', [phv_facts(w, A, phv)['k']], 'K e. RR'),
                                                                        D(w, A, 'reefcld', [D(w, A, 'remulcld', [D(w, A, 'abscld', [D(w, A, 'recld', [sc], '%s e. RR' % RS)] if False else [D(w, A, 'recnd', [D(w, A, 'recld', [sc], '%s e. RR' % RS)], '%s e. CC' % RS)], '%s e. RR' % ARS),
                                                                                                                 D(w, A, 'relogcld', [D(w, A, 'elrpd', [qr, D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), pr, qr, D(w, A, 'rpgt0d', [rp_of(w, A, pr, p1)], '0 < P'), pq], '0 < Q')], 'Q e. RR+')], '%s e. RR' % LQ)],
                                                                                              '( %s x. %s ) e. RR' % (ARS, LQ))], '%s e. RR' % E0)], '( K x. %s ) e. RR' % E0),
                                                   D(w, A, 'resqcld', [D(w, A, 'relogcld', [D(w, A, 'elrpd', [qr, D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), pr, qr, D(w, A, 'rpgt0d', [rp_of(w, A, pr, p1)], '0 < P'), pq], '0 < Q')], 'Q e. RR+')], '%s e. RR' % LQ)], '%s e. RR' % LQ2)],
                                  '( ( K x. %s ) x. %s ) e. RR' % (E0, LQ2)), D(w, A, 'abscld', [hc], '%s e. RR' % AH)], '%s e. RR' % C0)
    vx = D(w, A, 'syl3anc', [pr, qr, pq, w.inst('volioo')], '( vol ` %s ) = ( Q - P )' % X)
    vr = D(w, A, 'eqeltrd', [vx, D(w, A, 'resubcld', [qr, pr], '( Q - P ) e. RR')], '( vol ` %s ) e. RR' % X)
    c0c = D(w, A, 'recnd', [c0r], '%s e. CC' % C0)
    icst = D(w, A, 'syl3anc', [cst(w, A, 'ioombl', '%s e. dom vol' % X), vr, c0c, w.inst('iblconst')], '( %s X. { %s } ) e. L^1' % (X, C0))
    fcm = w.s([], 'fconstmpt', '( %s X. { %s } ) = ( y e. %s |-> %s )' % (X, C0, X, C0))
    icst2 = D(w, A, 'eqeltrrd', [w.s([fcm], 'a1i', '( %s -> ( %s X. { %s } ) = ( y e. %s |-> %s ) )' % (A, X, C0, X, C0)), icst], '( y e. %s |-> %s ) e. L^1' % (X, C0))
    iabs = D(w, A, 'iblabs', [wc, iW], '( y e. %s |-> ( abs ` %s ) ) e. L^1' % (X, WW))
    le_ = D(w, A, 'itgle', [iabs, icst2, D(w, Ay, 'abscld', [wc], '( abs ` %s ) e. RR' % WW), ad(w, Ay, c0r, '%s e. RR' % C0), pw], 'S. %s ( abs ` %s ) _d y <_ S. %s %s _d y' % (X, WW, X, C0))
    ic = D(w, A, 'syl3anc', [cst(w, A, 'ioombl', '%s e. dom vol' % X), vr, c0c, w.inst('itgconst')], 'S. %s %s _d y = ( %s x. ( vol ` %s ) )' % (X, C0, C0, X))
    ic2 = D(w, A, 'eqtrd', [ic, D(w, A, 'oveq2d', [vx], '( %s x. ( vol ` %s ) ) = ( %s x. ( Q - P ) )' % (C0, X, C0))], 'S. %s %s _d y = ( %s x. ( Q - P ) )' % (X, C0, C0))
    K0 = '( ( K x. %s ) x. %s )' % (E0, LQ2)
    fin_e = D(w, A, 'mul32d', [D(w, A, 'recnd', [D(w, A, 'remulcld', [D(w, A, 'remulcld', [D(w, A, 'rpred', [phv_facts(w, A, phv)['k']], 'K e. RR'), D(w, A, 'reefcld', [D(w, A, 'remulcld', [D(w, A, 'abscld', [D(w, A, 'recnd', [D(w, A, 'recld', [sc], '%s e. RR' % RS)], '%s e. CC' % RS)], '%s e. RR' % ARS), D(w, A, 'relogcld', [D(w, A, 'elrpd', [qr, D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), pr, qr, D(w, A, 'rpgt0d', [rp_of(w, A, pr, p1)], '0 < P'), pq], '0 < Q')], 'Q e. RR+')], '%s e. RR' % LQ)], '( %s x. %s ) e. RR' % (ARS, LQ))], '%s e. RR' % E0)], '( K x. %s ) e. RR' % E0),
                                                                           D(w, A, 'resqcld', [D(w, A, 'relogcld', [D(w, A, 'elrpd', [qr, D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), pr, qr, D(w, A, 'rpgt0d', [rp_of(w, A, pr, p1)], '0 < P'), pq], '0 < Q')], 'Q e. RR+')], '%s e. RR' % LQ)], '%s e. RR' % LQ2)], '%s e. RR' % K0)], '%s e. CC' % K0),
                                  D(w, A, 'abscld' if False else 'recnd', [D(w, A, 'abscld', [hc], '%s e. RR' % AH)], '%s e. CC' % AH), D(w, A, 'recnd', [D(w, A, 'resubcld', [qr, pr], '( Q - P ) e. RR')], '( Q - P ) e. CC')],
                  '( %s x. ( Q - P ) ) = ( ( %s x. ( Q - P ) ) x. %s )' % (C0, K0, AH))
    RHS = '( ( %s x. ( Q - P ) ) x. %s )' % (K0, AH)
    tot = D(w, A, 'letrd', [D(w, A, 'abscld', [D(w, A, 'itgcl', [iW, wc], 'S. %s %s _d y e. CC' % (X, WW))], '( abs ` S. %s %s _d y ) e. RR' % (X, WW)),
                            D(w, A, 'itgrecl', [D(w, Ay, 'abscld', [wc], '( abs ` %s ) e. RR' % WW), iabs], 'S. %s ( abs ` %s ) _d y e. RR' % (X, WW)),
                            D(w, A, 'itgrecl', [ad(w, Ay, c0r, '%s e. RR' % C0), icst2], 'S. %s %s _d y e. RR' % (X, C0)), ab1, le_], '( abs ` S. %s %s _d y ) <_ S. %s %s _d y' % (X, WW, X, C0))
    tot2 = D(w, A, 'breqtrd', [tot, D(w, A, 'eqtrd', [ic2, fin_e], 'S. %s %s _d y = %s' % (X, C0, RHS))], '( abs ` S. %s %s _d y ) <_ %s' % (X, WW, RHS))
    w.qed([D(w, A, 'fveq2d', [lhs], '( abs ` %s ) = ( abs ` S. %s %s _d y )' % (LHS, X, WW)), tot2], 'eqbrtrd', S['zl3pdq'])
    go(w)


# ---------------------------------------------------------------- zl3pdv
def integrand_cl(w, A2, phv, pr, p1, qr, s, sc_, log=False, P='P', Q='Q'):
    """( ( A2 /\\ y e. ( P (,) Q ) ) -> integrand e. CC )"""
    X = '( %s (,) %s )' % (P, Q)
    Ay = '( %s /\\ y e. %s )' % (A2, X)
    ss1, ss2 = ioo_in1(w, A2, pr, p1, qr, P, Q)
    yi = D(w, Ay, 'sseldd', [ad(w, Ay, ss2, '%s C_ %s' % (X, I1)), w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, X))], 'y e. %s' % I1)
    f = phv_facts(w, Ay, ad(w, Ay, phv, L.PHV))
    gc = D(w, Ay, 'ffvelcdmd', [f['g'], yi], '( G ` y ) e. CC')
    yr, yg = ge1(w, Ay, yi, 'y'); yrp = rp_of(w, Ay, yr, yg, 'y'); yc = D(w, Ay, 'rpcnd', [yrp], 'y e. CC')
    u = D(w, Ay, 'cxpcld', [yc, ad(w, Ay, sc_, '%s e. CC' % s)], '( y ^c %s ) e. CC' % s)
    if log:
        u = D(w, Ay, 'mulcld', [D(w, Ay, 'recnd', [D(w, Ay, 'relogcld', [yrp], '( log ` y ) e. RR')], '( log ` y ) e. CC'), u], '( ( log ` y ) x. ( y ^c %s ) ) e. CC' % s)
        return D(w, Ay, 'mulcld', [gc, u], '( ( G ` y ) x. ( ( log ` y ) x. ( y ^c %s ) ) ) e. CC' % s)
    return D(w, Ay, 'mulcld', [gc, u], '( ( G ` y ) x. ( y ^c %s ) ) e. CC' % s)


def pa_sub(w, s1, s2, P='P', Q='Q', log=False):
    """closed: ( s1 = s2 -> PA(s1) = PA(s2) )"""
    X = '( %s (,) %s )' % (P, Q)
    if log:
        a = w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( y ^c %s ) = ( y ^c %s ) )' % (s1, s2, s1, s2))], 'oveq2d', '( %s = %s -> ( ( log ` y ) x. ( y ^c %s ) ) = ( ( log ` y ) x. ( y ^c %s ) ) )' % (s1, s2, s1, s2))],
                'oveq2d', '( %s = %s -> ( ( G ` y ) x. ( ( log ` y ) x. ( y ^c %s ) ) ) = ( ( G ` y ) x. ( ( log ` y ) x. ( y ^c %s ) ) ) )' % (s1, s2, s1, s2))
        body1, body2 = '( ( G ` y ) x. ( ( log ` y ) x. ( y ^c %s ) ) )' % s1, '( ( G ` y ) x. ( ( log ` y ) x. ( y ^c %s ) ) )' % s2
        I1_, I2_ = L.PV(s1, P, Q), L.PV(s2, P, Q)
    else:
        a = w.s([w.s([], 'oveq2', '( %s = %s -> ( y ^c %s ) = ( y ^c %s ) )' % (s1, s2, s1, s2))], 'oveq2d', '( %s = %s -> ( ( G ` y ) x. ( y ^c %s ) ) = ( ( G ` y ) x. ( y ^c %s ) ) )' % (s1, s2, s1, s2))
        body1, body2 = '( ( G ` y ) x. ( y ^c %s ) )' % s1, '( ( G ` y ) x. ( y ^c %s ) )' % s2
        I1_, I2_ = L.PA(s1, P, Q), L.PA(s2, P, Q)
    b = w.s([a], 'adantr', '( ( %s = %s /\\ y e. %s ) -> %s = %s )' % (s1, s2, X, body1, body2))
    return w.s([b], 'itgeq2dv', '( %s = %s -> %s = %s )' % (s1, s2, I1_, I2_))


if want('zl3pdv'):
    w = W('zl3pdv', 'The parameter integral ` s |-> S. ( P (,) Q ) G ( y ) y ^c s _d y ` is holomorphic on every open set, with derivative ` S. G ( y ) log y y ^c s _d y ` .')
    A, C = ante_of('zl3pdv')
    J = '( TopOpen ` CCfld )'
    phv = D(w, A, 'simp1', [], L.PHV); iv = D(w, A, 'simp2', [], L.INTV); dj = D(w, A, 'simp3', [], 'D e. %s' % J)
    pr, p1, qr, pq = intv_facts(w, A, iv)
    jeq = w.s([], 'eqid', '%s = %s' % (J, J))
    jton = w.s([jeq], 'cnfldtopon', '%s e. ( TopOn ` CC )' % J)
    dcc = D(w, A, 'sylancr', [jton, dj, w.inst('toponss')], 'D C_ CC')
    FM = '( s e. D |-> %s )' % L.PA('s')
    fmeq = w.s([], 'eqid', '%s = %s' % (FM, FM))
    DV = '( CC _D %s )' % FM
    PAu, PVu = L.PA('u'), L.PV('u')
    As = '( %s /\\ u e. D )' % A
    uD = w.s([], 'simpr', '( %s -> u e. D )' % As)
    ucs = D(w, As, 'sseldd', [ad(w, As, dcc, 'D C_ CC'), uD], 'u e. CC')
    def args(A2):
        return (ad(w, A2, phv, L.PHV), ad(w, A2, pr, 'P e. RR'), ad(w, A2, p1, '1 <_ P'), ad(w, A2, qr, 'Q e. RR'))
    a_ = args(As)
    pac = D(w, As, 'itgcl', [ibl_pa(w, As, *a_, 'u', ucs), integrand_cl(w, As, *a_, 'u', ucs)], '%s e. CC' % PAu)
    pvc = D(w, As, 'itgcl', [ibl_pa(w, As, *a_, 'u', ucs, log=True), integrand_cl(w, As, *a_, 'u', ucs, log=True)], '%s e. CC' % PVu)
    fu = w.s([pa_sub(w, 's', 'u'), fmeq, w.s([], 'itgex', '%s e. _V' % PAu)], 'fvmpt', '( u e. D -> ( %s ` u ) = %s )' % (FM, PAu))
    pacs = D(w, As, 'eqeltrrd', [D(w, As, 'syl', [uD, fu], '( %s ` u ) = %s' % (FM, PAu)), pac], '( %s ` u ) e. CC' % FM) if False else None
    # FM : D --> CC via the s-instance of pac (fmptd needs the body at s)
    Ass = '( %s /\\ s e. D )' % A
    scs = D(w, Ass, 'sseldd', [ad(w, Ass, dcc, 'D C_ CC'), w.s([], 'simpr', '( %s -> s e. D )' % Ass)], 's e. CC')
    b_ = args(Ass)
    pas = D(w, Ass, 'itgcl', [ibl_pa(w, Ass, *b_, 's', scs), integrand_cl(w, Ass, *b_, 's', scs)], '%s e. CC' % L.PA('s'))
    fmf = D(w, A, 'fmptd', [pas, fmeq], '%s : D --> CC' % FM)
    # the difference-quotient hypothesis of zl3dvb at u
    RS, ARS, LQ = '( Re ` u )', '( abs ` ( Re ` u ) )', '( log ` Q )'
    CS = '( ( ( K x. ( exp ` ( %s x. %s ) ) ) x. ( %s ^ 2 ) ) x. ( Q - P ) )' % (ARS, LQ, LQ)
    Rr = '( 1 / ( %s + 1 ) )' % LQ
    qrp = D(w, A, 'elrpd', [qr, D(w, A, 'ltletrd', [cst(w, A, '0re', '0 e. RR'), pr, qr, D(w, A, 'rpgt0d', [rp_of(w, A, pr, p1)], '0 < P'), pq], '0 < Q')], 'Q e. RR+')
    lqr = D(w, A, 'relogcld', [qrp], '%s e. RR' % LQ)
    q1 = D(w, A, 'letrd', [cst(w, A, '1re', '1 e. RR'), pr, qr, p1, pq], '1 <_ Q')
    lq0 = D(w, A, 'logge0d', [qr, q1], '0 <_ %s' % LQ)
    l1r = D(w, A, 'readdcld', [lqr, cst(w, A, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % LQ)
    l1p = linarith(w, A, [lq0], '0 < ( %s + 1 )' % LQ, leaves={LQ: lqr})
    l1rp = D(w, A, 'elrpd', [l1r, l1p], '( %s + 1 ) e. RR+' % LQ)
    rrp = D(w, A, 'rpreccld', [l1rp], '%s e. RR+' % Rr)
    Az = '( %s /\\ z e. D )' % As
    zD = w.s([], 'simpr', '( %s -> z e. D )' % Az)
    zc = D(w, Az, 'sseldd', [ad(w, Az, ad(w, As, dcc, 'D C_ CC'), 'D C_ CC'), zD], 'z e. CC')
    Az2 = '( %s /\\ ( z =/= u /\\ ( abs ` ( z - u ) ) < %s ) )' % (Az, Rr)
    zns = w.s([], 'simprl', '( %s -> z =/= u )' % Az2); zlt = w.s([], 'simprr', '( %s -> ( abs ` ( z - u ) ) < %s )' % (Az2, Rr))
    def up3(st, f_):
        return ad(w, Az2, ad(w, Az, ad(w, As, st, f_), f_), f_)
    AZS = '( abs ` ( z - u ) )'
    zuc = D(w, Az2, 'subcld', [ad(w, Az2, zc, 'z e. CC'), ad(w, Az2, ad(w, Az, ucs, 'u e. CC'), 'u e. CC')], '( z - u ) e. CC')
    azr = D(w, Az2, 'abscld', [zuc], '%s e. RR' % AZS); az0 = D(w, Az2, 'absge0d', [zuc], '0 <_ %s' % AZS)
    rre = D(w, Az2, 'rpred', [up3(rrp, '%s e. RR+' % Rr)], '%s e. RR' % Rr)
    rid = D(w, Az2, 'recidd', [D(w, Az2, 'recnd', [up3(l1r, '( %s + 1 ) e. RR' % LQ)], '( %s + 1 ) e. CC' % LQ), D(w, Az2, 'rpne0d', [up3(l1rp, '( %s + 1 ) e. RR+' % LQ)], '( %s + 1 ) =/= 0' % LQ)],
           '( ( %s + 1 ) x. %s ) = 1' % (LQ, Rr))
    hb = nlinarith(w, Az2, [zlt, az0, up3(lq0, '0 <_ %s' % LQ), rid], '( %s x. %s ) <_ 1' % (AZS, LQ), leaves={AZS: azr, LQ: up3(lqr, '%s e. RR' % LQ), Rr: rre}, atoms=[AZS, LQ, Rr])
    pdq = D(w, Az2, 'syl3anc', [up3(phv, L.PHV), up3(iv, L.INTV),
                                 D(w, Az2, 'jca', [D(w, Az2, 'jca', [ad(w, Az2, ad(w, Az, ucs, 'u e. CC'), 'u e. CC'), ad(w, Az2, zc, 'z e. CC')], '( u e. CC /\\ z e. CC )'),
                                                   D(w, Az2, 'jca', [zns, hb], '( z =/= u /\\ ( %s x. %s ) <_ 1 )' % (AZS, LQ))], '( ( u e. CC /\\ z e. CC ) /\\ ( z =/= u /\\ ( %s x. %s ) <_ 1 ) )' % (AZS, LQ)),
                                 w.inst('zl3pdq')], '( abs ` ( ( ( %s - %s ) / ( z - u ) ) - %s ) ) <_ ( %s x. %s )' % (L.PA('z'), PAu, PVu, CS, AZS))
    fz = w.s([pa_sub(w, 's', 'z'), fmeq, w.s([], 'itgex', '%s e. _V' % L.PA('z'))], 'fvmpt', '( z e. D -> ( %s ` z ) = %s )' % (FM, L.PA('z')))
    fzv = D(w, Az2, 'syl', [ad(w, Az2, zD, 'z e. D'), fz], '( %s ` z ) = %s' % (FM, L.PA('z')))
    fuv = D(w, Az2, 'syl', [up3(uD, 'u e. D') if False else ad(w, Az2, ad(w, Az, uD, 'u e. D'), 'u e. D'), fu], '( %s ` u ) = %s' % (FM, PAu))
    DQF = '( ( ( %s ` z ) - ( %s ` u ) ) / ( z - u ) )' % (FM, FM)
    dqe = D(w, Az2, 'oveq1d', [D(w, Az2, 'oveq12d', [fzv, fuv], '( ( %s ` z ) - ( %s ` u ) ) = ( %s - %s )' % (FM, FM, L.PA('z'), PAu))],
            '%s = ( ( %s - %s ) / ( z - u ) )' % (DQF, L.PA('z'), PAu))
    bnd = D(w, Az2, 'eqbrtrd', [D(w, Az2, 'fveq2d', [D(w, Az2, 'oveq1d', [dqe], '( %s - %s ) = ( ( ( %s - %s ) / ( z - u ) ) - %s )' % (DQF, PVu, L.PA('z'), PAu, PVu))],
                                    '( abs ` ( %s - %s ) ) = ( abs ` ( ( ( %s - %s ) / ( z - u ) ) - %s ) )' % (DQF, PVu, L.PA('z'), PAu, PVu)), pdq],
              '( abs ` ( %s - %s ) ) <_ ( %s x. %s )' % (DQF, PVu, CS, AZS))
    HYZ = '( ( z =/= u /\\ %s < %s ) -> ( abs ` ( %s - %s ) ) <_ ( %s x. %s ) )' % (AZS, Rr, DQF, PVu, CS, AZS)
    ral = D(w, As, 'ralrimiva', [D(w, Az, 'ex', [bnd], HYZ)], 'A. z e. D %s' % HYZ)
    fs_ = phv_facts(w, As, ad(w, As, phv, L.PHV))
    lqs = ad(w, As, lqr, '%s e. RR' % LQ)
    arsr = D(w, As, 'abscld', [D(w, As, 'recnd', [D(w, As, 'recld', [ucs], '%s e. RR' % RS)], '%s e. CC' % RS)], '%s e. RR' % ARS)
    e0 = D(w, As, 'reefcld', [D(w, As, 'remulcld', [arsr, lqs], '( %s x. %s ) e. RR' % (ARS, LQ))], '( exp ` ( %s x. %s ) ) e. RR' % (ARS, LQ))
    k0 = D(w, As, 'remulcld', [D(w, As, 'rpred', [fs_['k']], 'K e. RR'), e0], '( K x. ( exp ` ( %s x. %s ) ) ) e. RR' % (ARS, LQ))
    k1 = D(w, As, 'remulcld', [k0, D(w, As, 'resqcld', [lqs], '( %s ^ 2 ) e. RR' % LQ)], '( ( K x. ( exp ` ( %s x. %s ) ) ) x. ( %s ^ 2 ) ) e. RR' % (ARS, LQ, LQ))
    csr = D(w, As, 'remulcld', [k1, D(w, As, 'resubcld', [ad(w, As, qr, 'Q e. RR'), ad(w, As, pr, 'P e. RR')], '( Q - P ) e. RR')], '%s e. RR' % CS)
    dvs = D(w, As, 'syl3anc', [D(w, As, 'jca', [ad(w, As, dj, 'D e. %s' % J), uD], '( D e. %s /\\ u e. D )' % J),
                               D(w, As, 'jca', [ad(w, As, fmf, '%s : D --> CC' % FM), pvc], '( %s : D --> CC /\\ %s e. CC )' % (FM, PVu)),
                               D(w, As, '3jca', [csr, ad(w, As, rrp, '%s e. RR+' % Rr), ral], '( %s e. RR /\\ %s e. RR+ /\\ A. z e. D %s )' % (CS, Rr, HYZ)),
                               w.inst('zl3dvb')], 'u %s %s' % (DV, PVu))
    udm = D(w, As, 'sylancr', [w.s([], 'reldv', 'Rel %s' % DV), dvs, w.inst('releldm')], 'u e. dom %s' % DV)
    fbr = w.s([w.s([w.s([w.s([], 'dvfcn', '%s : dom %s --> CC' % (DV, DV)), w.inst('ffun')], 'ax-mp', 'Fun %s' % DV), w.inst('funbrfv')], 'ax-mp',
                   '( u %s %s -> ( %s ` u ) = %s )' % (DV, PVu, DV, PVu))], 'a1i', '( %s -> ( u %s %s -> ( %s ` u ) = %s ) )' % (As, DV, PVu, DV, PVu))
    uval = D(w, As, 'mpd', [dvs, fbr], '( %s ` u ) = %s' % (DV, PVu))
    dss = D(w, A, 'ssrdv', [D(w, A, 'ex', [udm], '( u e. D -> u e. dom %s )' % DV)], 'D C_ dom %s' % DV)
    dsub = D(w, A, 'dvbss', [cst(w, A, 'ssid', 'CC C_ CC'), fmf, dcc], 'dom %s C_ D' % DV)
    deq = D(w, A, 'eqssd', [dsub, dss], 'dom %s = D' % DV)
    cn = D(w, A, 'syl2anc', [D(w, A, '3jca', [cst(w, A, 'ssid', 'CC C_ CC'), fmf, dcc], '( CC C_ CC /\\ %s : D --> CC /\\ D C_ CC )' % FM), deq, w.inst('dvcn')], '%s e. ( D -cn-> CC )' % FM)
    dvfd = D(w, A, 'mpbid', [cst(w, A, 'dvfcn', '%s : dom %s --> CC' % (DV, DV)), D(w, A, 'feq2d', [deq], '( %s : dom %s --> CC <-> %s : D --> CC )' % (DV, DV, DV))], '%s : D --> CC' % DV)
    fe = D(w, A, 'feqmptd', [dvfd], '%s = ( u e. D |-> ( %s ` u ) )' % (DV, DV))
    fe2 = D(w, A, 'eqtrd', [fe, D(w, A, 'mpteq2dva', [uval], '( u e. D |-> ( %s ` u ) ) = ( u e. D |-> %s )' % (DV, PVu))], '%s = ( u e. D |-> %s )' % (DV, PVu))
    cbv = w.s([pa_sub(w, 'u', 's', log=True)], 'cbvmptv', '( u e. D |-> %s ) = ( s e. D |-> %s )' % (PVu, L.PV('s')))
    fe3 = D(w, A, 'eqtrd', [fe2, w.s([cbv], 'a1i', '( %s -> ( u e. D |-> %s ) = ( s e. D |-> %s ) )' % (A, PVu, L.PV('s')))], '%s = ( s e. D |-> %s )' % (DV, L.PV('s')))
    w.qed([D(w, A, 'jca', [cn, dss], '( %s e. ( D -cn-> CC ) /\\ D C_ dom %s )' % (FM, DV)), fe3], 'jca', S['zl3pdv'])
    go(w)


# ---------------------------------------------------------------- zl3pxe
if want('zl3pxe'):
    w = W('zl3pxe', 'Polynomial growth is dominated by exponential growth: ` e ^ ( R log y ) <_ c e ^ ( E y ) ` on ` [ 1 , +oo ) ` .')
    A, C = ante_of('zl3pxe')
    rr = D(w, A, 'simpl', [], 'R e. RR'); erp = D(w, A, 'simpr', [], 'E e. RR+')
    AR = '( abs ` R )'; M = '( %s + 1 )' % AR; AL = '( E / %s )' % M
    arr = D(w, A, 'abscld', [D(w, A, 'recnd', [rr], 'R e. CC')], '%s e. RR' % AR); ar0 = D(w, A, 'absge0d', [D(w, A, 'recnd', [rr], 'R e. CC')], '0 <_ %s' % AR)
    mr = D(w, A, 'readdcld', [arr, cst(w, A, '1re', '1 e. RR')], '%s e. RR' % M)
    mrp = D(w, A, 'elrpd', [mr, linarith(w, A, [ar0], '0 < %s' % M, leaves={AR: arr})], '%s e. RR+' % M)
    alp = D(w, A, 'rpdivcld', [erp, mrp], '%s e. RR+' % AL)
    LA = '( log ` %s )' % AL
    lar = D(w, A, 'relogcld', [alp], '%s e. RR' % LA)
    CC_ = '( exp ` -u ( %s x. %s ) )' % (M, LA)
    crp = D(w, A, 'rpefcld', [D(w, A, 'renegcld', [D(w, A, 'remulcld', [mr, lar], '( %s x. %s ) e. RR' % (M, LA))], '-u ( %s x. %s ) e. RR' % (M, LA))], '%s e. RR+' % CC_)
    Ay = '( %s /\\ y e. %s )' % (A, I1)
    yr, y1 = ge1(w, Ay, w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, I1)), 'y')
    yrp = rp_of(w, Ay, yr, y1, 'y')
    AY = '( %s x. y )' % AL
    ayp = D(w, Ay, 'rpmulcld', [ad(w, Ay, alp, '%s e. RR+' % AL), yrp], '%s e. RR+' % AY)
    ayr = D(w, Ay, 'rpred', [ayp], '%s e. RR' % AY)
    g1 = D(w, Ay, 'syl', [ayp, w.inst('efgt1p')], '( 1 + %s ) < ( exp ` %s )' % (AY, AY))
    eay = D(w, Ay, 'reefcld', [ayr], '( exp ` %s ) e. RR' % AY)
    lt = linarith(w, Ay, [g1], '%s < ( exp ` %s )' % (AY, AY), leaves={AY: ayr, '( exp ` %s )' % AY: eay}, atoms=['( exp ` %s )' % AY])
    lg = D(w, Ay, 'mpbid', [lt, D(w, Ay, 'syl2anc', [ayp, D(w, Ay, 'rpefcld', [ayr], '( exp ` %s ) e. RR+' % AY), w.inst('logltb')],
                                  '( %s < ( exp ` %s ) <-> ( log ` %s ) < ( log ` ( exp ` %s ) ) )' % (AY, AY, AY, AY))], '( log ` %s ) < ( log ` ( exp ` %s ) )' % (AY, AY))
    lg2 = D(w, Ay, 'breqtrd', [lg, D(w, Ay, 'relogefd', [ayr], '( log ` ( exp ` %s ) ) = %s' % (AY, AY))], '( log ` %s ) < %s' % (AY, AY))
    lm = D(w, Ay, 'relogmuld', [ad(w, Ay, alp, '%s e. RR+' % AL), yrp], '( log ` %s ) = ( %s + ( log ` y ) )' % (AY, LA))
    lg3 = D(w, Ay, 'eqbrtrrd', [lm, lg2], '( %s + ( log ` y ) ) < %s' % (LA, AY))
    LY = '( log ` y )'
    lyr = D(w, Ay, 'relogcld', [yrp], '%s e. RR' % LY); ly0 = D(w, Ay, 'logge0d', [yr, y1], '0 <_ %s' % LY)
    alr = D(w, Ay, 'rpred', [ad(w, Ay, alp, '%s e. RR+' % AL)], '%s e. RR' % AL)
    ma = D(w, Ay, 'divcan2d', [D(w, Ay, 'rpcnd', [ad(w, Ay, erp, 'E e. RR+')], 'E e. CC'), D(w, Ay, 'recnd', [ad(w, Ay, mr, '%s e. RR' % M)], '%s e. CC' % M),
                               D(w, Ay, 'rpne0d', [ad(w, Ay, mrp, '%s e. RR+' % M)], '%s =/= 0' % M)], '( %s x. %s ) = E' % (M, AL))
    rle = D(w, Ay, 'leabsd', [ad(w, Ay, rr, 'R e. RR')], 'R <_ %s' % AR)
    EXP = '( ( E x. y ) + -u ( %s x. %s ) )' % (M, LA)
    er_ = D(w, Ay, 'rpred', [ad(w, Ay, erp, 'E e. RR+')], 'E e. RR')
    ma2 = D(w, Ay, 'eqtr3d', [D(w, Ay, 'mulassd', [D(w, Ay, 'recnd', [ad(w, Ay, mr, '%s e. RR' % M)], '%s e. CC' % M), D(w, Ay, 'recnd', [alr], '%s e. CC' % AL), D(w, Ay, 'recnd', [yr], 'y e. CC')],
                                    '( ( %s x. %s ) x. y ) = ( %s x. ( %s x. y ) )' % (M, AL, M, AL)), D(w, Ay, 'oveq1d', [ma], '( ( %s x. %s ) x. y ) = ( E x. y )' % (M, AL))],
              '( %s x. ( %s x. y ) ) = ( E x. y )' % (M, AL))
    key = nlinarith(w, Ay, [lg3, rle, ly0, ad(w, Ay, ar0, '0 <_ %s' % AR), ma2], '( R x. %s ) <_ %s' % (LY, EXP),
                    leaves={'R': ad(w, Ay, rr, 'R e. RR'), LY: lyr, AR: ad(w, Ay, arr, '%s e. RR' % AR), LA: ad(w, Ay, lar, '%s e. RR' % LA), AL: alr, 'y': yr, 'E': er_},
                    atoms=[LY, AR, LA, AL])
    ee = efle_(w, Ay, '( R x. %s )' % LY, EXP, D(w, Ay, 'remulcld', [ad(w, Ay, rr, 'R e. RR'), lyr], '( R x. %s ) e. RR' % LY),
               D(w, Ay, 'readdcld', [D(w, Ay, 'remulcld', [er_, yr], '( E x. y ) e. RR'), D(w, Ay, 'renegcld', [D(w, Ay, 'remulcld', [ad(w, Ay, mr, '%s e. RR' % M), ad(w, Ay, lar, '%s e. RR' % LA)], '( %s x. %s ) e. RR' % (M, LA))], '-u ( %s x. %s ) e. RR' % (M, LA))],
                 '%s e. RR' % EXP), key)
    ea = efadd_(w, Ay, '( E x. y )', '-u ( %s x. %s )' % (M, LA), D(w, Ay, 'recnd', [D(w, Ay, 'remulcld', [er_, yr], '( E x. y ) e. RR')], '( E x. y ) e. CC'),
                D(w, Ay, 'recnd', [D(w, Ay, 'renegcld', [D(w, Ay, 'remulcld', [ad(w, Ay, mr, '%s e. RR' % M), ad(w, Ay, lar, '%s e. RR' % LA)], '( %s x. %s ) e. RR' % (M, LA))], '-u ( %s x. %s ) e. RR' % (M, LA))], '-u ( %s x. %s ) e. CC' % (M, LA)))
    mc = D(w, Ay, 'mulcomd', [D(w, Ay, 'efcld', [D(w, Ay, 'recnd', [D(w, Ay, 'remulcld', [er_, yr], '( E x. y ) e. RR')], '( E x. y ) e. CC')], '( exp ` ( E x. y ) ) e. CC'),
                              D(w, Ay, 'rpcnd', [ad(w, Ay, crp, '%s e. RR+' % CC_)], '%s e. CC' % CC_)], '( ( exp ` ( E x. y ) ) x. %s ) = ( %s x. ( exp ` ( E x. y ) ) )' % (CC_, CC_))
    b = D(w, Ay, 'breqtrd', [ee, D(w, Ay, 'eqtrd', [ea, mc], '( exp ` %s ) = ( %s x. ( exp ` ( E x. y ) ) )' % (EXP, CC_))], '( exp ` ( R x. %s ) ) <_ ( %s x. ( exp ` ( E x. y ) ) )' % (LY, CC_))
    INNER = lambda c: 'A. y e. %s ( exp ` ( R x. ( log ` y ) ) ) <_ ( %s x. ( exp ` ( E x. y ) ) )' % (I1, c)
    ral = D(w, A, 'ralrimiva', [b], INNER(CC_))
    sub = w.s([w.s([w.s([], 'oveq1', '( c = %s -> ( c x. ( exp ` ( E x. y ) ) ) = ( %s x. ( exp ` ( E x. y ) ) ) )' % (CC_, CC_))], 'breq2d',
                   '( c = %s -> ( ( exp ` ( R x. ( log ` y ) ) ) <_ ( c x. ( exp ` ( E x. y ) ) ) <-> ( exp ` ( R x. ( log ` y ) ) ) <_ ( %s x. ( exp ` ( E x. y ) ) ) ) )' % (CC_, CC_))],
              'ralbidv', '( c = %s -> ( %s <-> %s ) )' % (CC_, INNER('c'), INNER(CC_)))
    w.qed([crp, ral, w.s([sub], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. c e. RR+ %s )' % (CC_, INNER(CC_), INNER('c')))], 'syl2anc', S['zl3pxe'])
    go(w)


# ---------------------------------------------------------------- zl3pbd
if want('zl3pbd'):
    w = W('zl3pbd', 'On ` ( J , T ) ` , ` T <_ J + 1 ` , the parameter integral and its ` s ` -derivative are bounded by ` K e ^ -BJ e ^ ( R log ( J + 1 ) ) ` when ` abs ( Re S ) + 1 <_ R ` .')
    A, C = ante_of('zl3pbd')
    phv = D(w, A, 'simp1', [], L.PHV)
    h2 = D(w, A, 'simp2', [], '( R e. RR /\\ S e. CC /\\ ( ( abs ` ( Re ` S ) ) + 1 ) <_ R )')
    h3 = D(w, A, 'simp3', [], '( J e. NN /\\ T e. ( J [,] ( J + 1 ) ) )')
    rr = D(w, A, 'simp1d', [h2], 'R e. RR'); sc = D(w, A, 'simp2d', [h2], 'S e. CC')
    RS, ARS = '( Re ` S )', '( abs ` ( Re ` S ) )'
    rle = D(w, A, 'simp3d', [h2], '( %s + 1 ) <_ R' % ARS)
    jn = D(w, A, 'simpld', [h3], 'J e. NN'); tI = D(w, A, 'simprd', [h3], 'T e. ( J [,] ( J + 1 ) )')
    jr = D(w, A, 'nnred', [jn], 'J e. RR'); j1 = D(w, A, 'nnge1d', [jn], '1 <_ J')
    J1 = '( J + 1 )'
    j1r = D(w, A, 'syl', [jr, w.inst('peano2re')], '%s e. RR' % J1)
    tt = D(w, A, 'mpbid', [tI, D(w, A, 'syl2anc', [jr, j1r, w.inst('elicc2')], '( T e. ( J [,] %s ) <-> ( T e. RR /\\ J <_ T /\\ T <_ %s ) )' % (J1, J1))], '( T e. RR /\\ J <_ T /\\ T <_ %s )' % J1)
    tr = D(w, A, 'simp1d', [tt], 'T e. RR'); jt = D(w, A, 'simp2d', [tt], 'J <_ T'); tj1 = D(w, A, 'simp3d', [tt], 'T <_ %s' % J1)
    X = '( J (,) T )'
    f0 = phv_facts(w, A, phv)
    MJJ = L.MJ('J')
    LJ = '( log ` %s )' % J1
    j1rp = rp_of(w, A, j1r, linarith(w, A, [j1], '1 <_ %s' % J1, leaves={'J': jr}), J1)
    ljr = D(w, A, 'relogcld', [j1rp], '%s e. RR' % LJ)
    EBJ = '( exp ` -u ( B x. J ) )'; ERJ = '( exp ` ( R x. %s ) )' % LJ
    ebj = D(w, A, 'reefcld', [D(w, A, 'renegcld', [D(w, A, 'remulcld', [D(w, A, 'rpred', [f0['b']], 'B e. RR'), jr], '( B x. J ) e. RR')], '-u ( B x. J ) e. RR')], '%s e. RR' % EBJ)
    erj = D(w, A, 'reefcld', [D(w, A, 'remulcld', [rr, ljr], '( R x. %s ) e. RR' % LJ)], '%s e. RR' % ERJ)
    kr = D(w, A, 'rpred', [f0['k']], 'K e. RR')
    mjr = D(w, A, 'remulcld', [D(w, A, 'remulcld', [kr, ebj], '( K x. %s ) e. RR' % EBJ), erj], '%s e. RR' % MJJ)
    mj0 = D(w, A, 'mulge0d' if False else 'rpge0d', [D(w, A, 'rpmulcld', [D(w, A, 'rpmulcld', [f0['k'], D(w, A, 'rpefcld', [D(w, A, 'renegcld', [D(w, A, 'remulcld', [D(w, A, 'rpred', [f0['b']], 'B e. RR'), jr], '( B x. J ) e. RR')], '-u ( B x. J ) e. RR')], '%s e. RR+' % EBJ)], '( K x. %s ) e. RR+' % EBJ),
                                                                   D(w, A, 'rpefcld', [D(w, A, 'remulcld', [rr, ljr], '( R x. %s ) e. RR' % LJ)], '%s e. RR+' % ERJ)], '%s e. RR+' % MJJ)], '0 <_ %s' % MJJ)
    # pointwise
    Ay = '( %s /\\ y e. %s )' % (A, X)
    yX = w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, X))
    ss1, ss2 = ioo_in1(w, A, jr, j1, tr, 'J', 'T')
    yf = yfacts(w, Ay, yX, 'J', 'T', ad(w, Ay, jr, 'J e. RR'), ad(w, Ay, j1, '1 <_ J'), ad(w, Ay, tr, 'T e. RR'), ad(w, Ay, ss2, '%s C_ %s' % (X, I1)))
    f = phv_facts(w, Ay, ad(w, Ay, phv, L.PHV))
    gb = gbound(w, Ay, f['bnd'], 'y', yf['i1'])
    gc = D(w, Ay, 'ffvelcdmd', [f['g'], yf['i1']], '( G ` y ) e. CC')
    bi = D(w, Ay, 'syl2anc', [D(w, Ay, 'rexrd', [ad(w, Ay, jr, 'J e. RR')], 'J e. RR*'), D(w, Ay, 'rexrd', [ad(w, Ay, tr, 'T e. RR')], 'T e. RR*'), w.inst('elioo2')],
           '( y e. %s <-> ( y e. RR /\\ J < y /\\ y < T ) )' % X)
    jy = D(w, Ay, 'ltled', [ad(w, Ay, jr, 'J e. RR'), yf['r'], D(w, Ay, 'simp2d', [D(w, Ay, 'mpbid', [yX, bi], '( y e. RR /\\ J < y /\\ y < T )')], 'J < y')], 'J <_ y')
    yj1 = D(w, Ay, 'letrd', [yf['r'], ad(w, Ay, tr, 'T e. RR'), ad(w, Ay, j1r, '%s e. RR' % J1), yf['leq'], ad(w, Ay, tj1, 'T <_ %s' % J1)], 'y <_ %s' % J1)
    br = D(w, Ay, 'rpred', [f['b']], 'B e. RR'); b0 = D(w, Ay, 'rpgt0d', [f['b']], '0 < B')
    ey = efle_(w, Ay, '-u ( B x. y )', '-u ( B x. J )', D(w, Ay, 'renegcld', [D(w, Ay, 'remulcld', [br, yf['r']], '( B x. y ) e. RR')], '-u ( B x. y ) e. RR'),
               D(w, Ay, 'renegcld', [D(w, Ay, 'remulcld', [br, ad(w, Ay, jr, 'J e. RR')], '( B x. J ) e. RR')], '-u ( B x. J ) e. RR'),
               nlinarith(w, Ay, [jy, b0], '-u ( B x. y ) <_ -u ( B x. J )', leaves={'B': br, 'y': yf['r'], 'J': ad(w, Ay, jr, 'J e. RR')}))
    EBY = '( exp ` -u ( B x. y ) )'
    eby = D(w, Ay, 'reefcld', [D(w, Ay, 'renegcld', [D(w, Ay, 'remulcld', [br, yf['r']], '( B x. y ) e. RR')], '-u ( B x. y ) e. RR')], '%s e. RR' % EBY)
    kyr = ad(w, Ay, kr, 'K e. RR')
    gle = D(w, Ay, 'letrd', [D(w, Ay, 'abscld', [gc], '( abs ` ( G ` y ) ) e. RR'), D(w, Ay, 'remulcld', [kyr, eby], '( K x. %s ) e. RR' % EBY),
                             D(w, Ay, 'remulcld', [kyr, ad(w, Ay, ebj, '%s e. RR' % EBJ)], '( K x. %s ) e. RR' % EBJ), gb,
                             D(w, Ay, 'lemul2ad', [eby, ad(w, Ay, ebj, '%s e. RR' % EBJ), kyr, D(w, Ay, 'rpge0d', [f['k']], '0 <_ K'), ey], '( K x. %s ) <_ ( K x. %s )' % (EBY, EBJ))], '( abs ` ( G ` y ) ) <_ ( K x. %s )' % EBJ)
    LY = '( log ` y )'
    lyr = D(w, Ay, 'relogcld', [yf['rp']], '%s e. RR' % LY); ly0 = D(w, Ay, 'logge0d', [yf['r'], yf['ge1']], '0 <_ %s' % LY)
    lyj = D(w, Ay, 'mpbid', [yj1, D(w, Ay, 'logled', [yf['rp'], ad(w, Ay, j1rp, '%s e. RR+' % J1)], '( y <_ %s <-> %s <_ %s )' % (J1, LY, LJ))], '%s <_ %s' % (LY, LJ))
    rsr = D(w, Ay, 'recld', [ad(w, Ay, sc, 'S e. CC')], '%s e. RR' % RS)
    arsr = D(w, Ay, 'abscld', [D(w, Ay, 'recnd', [rsr], '%s e. CC' % RS)], '%s e. RR' % ARS)
    rsl = D(w, Ay, 'leabsd', [rsr], '%s <_ %s' % (RS, ARS)); ars0 = D(w, Ay, 'absge0d', [D(w, Ay, 'recnd', [rsr], '%s e. CC' % RS)], '0 <_ %s' % ARS)
    UA = '( abs ` ( y ^c S ) )'
    uS = D(w, Ay, 'cxpcld', [yf['c'], ad(w, Ay, sc, 'S e. CC')], '( y ^c S ) e. CC')
    ua = D(w, Ay, 'eqtrd', [D(w, Ay, 'syl2anc', [yf['rp'], ad(w, Ay, sc, 'S e. CC'), w.inst('abscxp')], '%s = ( y ^c %s )' % (UA, RS)),
                            D(w, Ay, 'syl3anc', [yf['c'], yf['n0'], D(w, Ay, 'recnd', [rsr], '%s e. CC' % RS), w.inst('cxpef')], '( y ^c %s ) = ( exp ` ( %s x. %s ) )' % (RS, RS, LY))],
           '%s = ( exp ` ( %s x. %s ) )' % (UA, RS, LY))
    ljy = ad(w, Ay, ljr, '%s e. RR' % LJ); ryy = ad(w, Ay, rr, 'R e. RR'); rley = ad(w, Ay, rle, '( %s + 1 ) <_ R' % ARS)
    # the plain integrand: RS log y <_ R LJ
    k1 = nlinarith(w, Ay, [rsl, ly0, lyj, ars0, rley], '( %s x. %s ) <_ ( R x. %s )' % (RS, LY, LJ), leaves={RS: rsr, LY: lyr, ARS: arsr, LJ: ljy, 'R': ryy}, atoms=[RS, LY, ARS, LJ])
    e1 = efle_(w, Ay, '( %s x. %s )' % (RS, LY), '( R x. %s )' % LJ, D(w, Ay, 'remulcld', [rsr, lyr], '( %s x. %s ) e. RR' % (RS, LY)), D(w, Ay, 'remulcld', [ryy, ljy], '( R x. %s ) e. RR' % LJ), k1)
    uab = D(w, Ay, 'eqbrtrd', [ua, e1], '%s <_ %s' % (UA, ERJ))
    uar = D(w, Ay, 'abscld', [uS], '%s e. RR' % UA)
    gar = D(w, Ay, 'abscld', [gc], '( abs ` ( G ` y ) ) e. RR')
    KE = '( K x. %s )' % EBJ
    ker = ad(w, Ay, D(w, A, 'remulcld', [kr, ebj], '%s e. RR' % KE), '%s e. RR' % KE)
    erjy = ad(w, Ay, erj, '%s e. RR' % ERJ)
    p0 = D(w, Ay, 'lemul12ad', [gar, ker, uar, erjy, D(w, Ay, 'absge0d', [gc], '0 <_ ( abs ` ( G ` y ) )'), D(w, Ay, 'absge0d', [uS], '0 <_ %s' % UA), gle, uab],
           '( ( abs ` ( G ` y ) ) x. %s ) <_ %s' % (UA, MJJ))
    pw0 = D(w, Ay, 'eqbrtrd', [D(w, Ay, 'absmuld', [gc, uS], '( abs ` ( ( G ` y ) x. ( y ^c S ) ) ) = ( ( abs ` ( G ` y ) ) x. %s )' % UA), p0], '( abs ` ( ( G ` y ) x. ( y ^c S ) ) ) <_ %s' % MJJ)
    # the log integrand: log y x. |y^S| <_ exp( ( ARS + 1 ) log y ) <_ exp ( R LJ )
    lyc = D(w, Ay, 'recnd', [lyr], '%s e. CC' % LY)
    lu = D(w, Ay, 'mulcld', [lyc, uS], '( %s x. ( y ^c S ) ) e. CC' % LY)
    lua = D(w, Ay, 'absmuld', [lyc, uS], '( abs ` ( %s x. ( y ^c S ) ) ) = ( ( abs ` %s ) x. %s )' % (LY, LY, UA))
    lab = D(w, Ay, 'absidd', [lyr, ly0], '( abs ` %s ) = %s' % (LY, LY))
    ELY = '( exp ` %s )' % LY
    ge = D(w, Ay, 'syl2anc', [lyr, ly0, w.inst('bvefge1p')], '( 1 + %s ) <_ %s' % (LY, ELY))
    ely = D(w, Ay, 'reefcld', [lyr], '%s e. RR' % ELY)
    lle = linarith(w, Ay, [ge], '%s <_ %s' % (LY, ELY), leaves={LY: lyr, ELY: ely}, atoms=[ELY])
    ERS = '( exp ` ( %s x. %s ) )' % (RS, LY)
    ers = D(w, Ay, 'reefcld', [D(w, Ay, 'remulcld', [rsr, lyr], '( %s x. %s ) e. RR' % (RS, LY))], '%s e. RR' % ERS)
    m1 = D(w, Ay, 'lemul1ad', [lyr, ely, D(w, Ay, 'rpge0d', [D(w, Ay, 'rpefcld', [D(w, Ay, 'remulcld', [rsr, lyr], '( %s x. %s ) e. RR' % (RS, LY))], '%s e. RR+' % ERS)], '0 <_ %s' % ERS) if False else ers,
                               D(w, Ay, 'rpge0d', [D(w, Ay, 'rpefcld', [D(w, Ay, 'remulcld', [rsr, lyr], '( %s x. %s ) e. RR' % (RS, LY))], '%s e. RR+' % ERS)], '0 <_ %s' % ERS), lle],
           '( %s x. %s ) <_ ( %s x. %s )' % (LY, ERS, ELY, ERS))
    ea = efadd_(w, Ay, LY, '( %s x. %s )' % (RS, LY), lyc, D(w, Ay, 'recnd', [D(w, Ay, 'remulcld', [rsr, lyr], '( %s x. %s ) e. RR' % (RS, LY))], '( %s x. %s ) e. CC' % (RS, LY)))
    SUMX = '( %s + ( %s x. %s ) )' % (LY, RS, LY)
    k2 = nlinarith(w, Ay, [rsl, ly0, lyj, ars0, rley], '%s <_ ( R x. %s )' % (SUMX, LJ), leaves={RS: rsr, LY: lyr, ARS: arsr, LJ: ljy, 'R': ryy}, atoms=[RS, LY, ARS, LJ])
    e2 = efle_(w, Ay, SUMX, '( R x. %s )' % LJ, D(w, Ay, 'readdcld', [lyr, D(w, Ay, 'remulcld', [rsr, lyr], '( %s x. %s ) e. RR' % (RS, LY))], '%s e. RR' % SUMX),
               D(w, Ay, 'remulcld', [ryy, ljy], '( R x. %s ) e. RR' % LJ), k2)
    lb = D(w, Ay, 'letrd', [D(w, Ay, 'remulcld', [lyr, ers], '( %s x. %s ) e. RR' % (LY, ERS)), D(w, Ay, 'remulcld', [ely, ers], '( %s x. %s ) e. RR' % (ELY, ERS)), erjy,
                            m1, D(w, Ay, 'eqbrtrrd', [ea, e2], '( %s x. %s ) <_ %s' % (ELY, ERS, ERJ))], '( %s x. %s ) <_ %s' % (LY, ERS, ERJ))
    LUA = '( abs ` ( %s x. ( y ^c S ) ) )' % LY
    lua2 = chain(w, Ay, [LUA, '( ( abs ` %s ) x. %s )' % (LY, UA), '( %s x. %s )' % (LY, UA), '( %s x. %s )' % (LY, ERS)],
                 [lua, D(w, Ay, 'oveq1d', [lab], '( ( abs ` %s ) x. %s ) = ( %s x. %s )' % (LY, UA, LY, UA)), D(w, Ay, 'oveq2d', [ua], '( %s x. %s ) = ( %s x. %s )' % (LY, UA, LY, ERS))])
    lub = D(w, Ay, 'eqbrtrd', [lua2, lb], '%s <_ %s' % (LUA, ERJ))
    p1_ = D(w, Ay, 'lemul12ad', [gar, ker, D(w, Ay, 'abscld', [lu], '%s e. RR' % LUA), erjy, D(w, Ay, 'absge0d', [gc], '0 <_ ( abs ` ( G ` y ) )'), D(w, Ay, 'absge0d', [lu], '0 <_ %s' % LUA), gle, lub],
            '( ( abs ` ( G ` y ) ) x. %s ) <_ %s' % (LUA, MJJ))
    GLU = '( ( G ` y ) x. ( %s x. ( y ^c S ) ) )' % LY
    pw1 = D(w, Ay, 'eqbrtrd', [D(w, Ay, 'absmuld', [gc, lu], '( abs ` %s ) = ( ( abs ` ( G ` y ) ) x. %s )' % (GLU, LUA)), p1_], '( abs ` %s ) <_ %s' % (GLU, MJJ))
    # integrate
    vx = D(w, A, 'syl3anc', [jr, tr, jt, w.inst('volioo')], '( vol ` %s ) = ( T - J )' % X)
    vr = D(w, A, 'eqeltrd', [vx, D(w, A, 'resubcld', [tr, jr], '( T - J ) e. RR')], '( vol ` %s ) e. RR' % X)
    mjc = D(w, A, 'recnd', [mjr], '%s e. CC' % MJJ)
    icst = D(w, A, 'syl3anc', [cst(w, A, 'ioombl', '%s e. dom vol' % X), vr, mjc, w.inst('iblconst')], '( %s X. { %s } ) e. L^1' % (X, MJJ))
    icst2 = D(w, A, 'eqeltrrd', [w.s([w.s([], 'fconstmpt', '( %s X. { %s } ) = ( y e. %s |-> %s )' % (X, MJJ, X, MJJ))], 'a1i', '( %s -> ( %s X. { %s } ) = ( y e. %s |-> %s ) )' % (A, X, MJJ, X, MJJ)), icst],
                 '( y e. %s |-> %s ) e. L^1' % (X, MJJ))
    ic = D(w, A, 'eqtrd', [D(w, A, 'syl3anc', [cst(w, A, 'ioombl', '%s e. dom vol' % X), vr, mjc, w.inst('itgconst')], 'S. %s %s _d y = ( %s x. ( vol ` %s ) )' % (X, MJJ, MJJ, X)),
                           D(w, A, 'oveq2d', [vx], '( %s x. ( vol ` %s ) ) = ( %s x. ( T - J ) )' % (MJJ, X, MJJ))], 'S. %s %s _d y = ( %s x. ( T - J ) )' % (X, MJJ, MJJ))
    tj = linarith(w, A, [tj1], '( T - J ) <_ 1', leaves={'T': tr, 'J': jr})
    mt = nlinarith(w, A, [tj, mj0, jt], '( %s x. ( T - J ) ) <_ %s' % (MJJ, MJJ), leaves={MJJ: mjr, 'T': tr, 'J': jr}, atoms=[MJJ])
    icle = D(w, A, 'eqbrtrd', [ic, mt], 'S. %s %s _d y <_ %s' % (X, MJJ, MJJ))
    def one(log):
        body = GLU if log else '( ( G ` y ) x. ( y ^c S ) )'
        ib = ibl_pa(w, A, phv, jr, j1, tr, 'S', sc, 'J', 'T', log=log)
        cl_ = integrand_cl(w, A, phv, jr, j1, tr, 'S', sc, log=log, P='J', Q='T')
        I_ = L.PV('S', 'J', 'T') if log else L.PA('S', 'J', 'T')
        ab = D(w, A, 'itgabs', [cl_, ib], '( abs ` %s ) <_ S. %s ( abs ` %s ) _d y' % (I_, X, body))
        iab = D(w, A, 'iblabs', [cl_, ib], '( y e. %s |-> ( abs ` %s ) ) e. L^1' % (X, body))
        le_ = D(w, A, 'itgle', [iab, icst2, D(w, Ay, 'abscld', [cl_], '( abs ` %s ) e. RR' % body), ad(w, Ay, mjr, '%s e. RR' % MJJ), pw1 if log else pw0],
                'S. %s ( abs ` %s ) _d y <_ S. %s %s _d y' % (X, body, X, MJJ))
        i1r = D(w, A, 'itgrecl', [D(w, Ay, 'abscld', [cl_], '( abs ` %s ) e. RR' % body), iab], 'S. %s ( abs ` %s ) _d y e. RR' % (X, body))
        i2r = D(w, A, 'itgrecl', [ad(w, Ay, mjr, '%s e. RR' % MJJ), icst2], 'S. %s %s _d y e. RR' % (X, MJJ))
        t1 = D(w, A, 'letrd', [D(w, A, 'abscld', [D(w, A, 'itgcl', [ib, cl_], '%s e. CC' % I_)], '( abs ` %s ) e. RR' % I_), i1r, i2r, ab, le_], '( abs ` %s ) <_ S. %s %s _d y' % (I_, X, MJJ))
        return D(w, A, 'letrd', [D(w, A, 'abscld', [D(w, A, 'itgcl', [ib, cl_], '%s e. CC' % I_)], '( abs ` %s ) e. RR' % I_), i2r, mjr, t1, icle], '( abs ` %s ) <_ %s' % (I_, MJJ))
    w.qed([one(False), one(True)], 'jca', S['zl3pbd'])
    go(w)


# ---------------------------------------------------------------- zl3msum
if want('zl3msum'):
    w = W('zl3msum', 'The majorant ` K e ^ -Bj e ^ ( R log ( j + 1 ) ) ` is summable ( ~ zl3pxe , ~ zl3mser ).')
    A, C = ante_of('zl3msum')
    krp = D(w, A, 'simp1', [], 'K e. RR+'); brp = D(w, A, 'simp2', [], 'B e. RR+'); rr = D(w, A, 'simp3', [], 'R e. RR')
    B2 = '( B / 2 )'
    b2p = D(w, A, 'rphalfcld', [brp], '%s e. RR+' % B2)
    PSI = 'A. y e. %s ( exp ` ( R x. ( log ` y ) ) ) <_ ( c x. ( exp ` ( %s x. y ) ) )' % (I1, B2)
    ex = D(w, A, 'syl2anc', [rr, b2p, w.inst('zl3pxe')], 'E. c e. RR+ %s' % PSI)
    Ac = '( ( %s /\\ c e. RR+ ) /\\ %s )' % (A, PSI)
    psi = w.s([], 'simpr', '( %s -> %s )' % (Ac, PSI))
    def up(st, f):
        return w.s([st], 'ad2antrr', '( %s -> %s )' % (Ac, f))
    crp = w.s([], 'simplr', '( %s -> c e. RR+ )' % Ac)
    kr, br, rrc = D(w, Ac, 'rpred', [up(krp, 'K e. RR+')], 'K e. RR'), D(w, Ac, 'rpred', [up(brp, 'B e. RR+')], 'B e. RR'), up(rr, 'R e. RR')
    b2r = D(w, Ac, 'rpred', [up(b2p, '%s e. RR+' % B2)], '%s e. RR' % B2)
    RR_ = '( exp ` -u %s )' % B2
    rrp_ = D(w, Ac, 'rpefcld', [D(w, Ac, 'renegcld', [b2r], '-u %s e. RR' % B2)], '%s e. RR+' % RR_)
    rrr = D(w, Ac, 'rpred', [rrp_], '%s e. RR' % RR_)
    rlt = D(w, Ac, 'mpbid', [D(w, Ac, 'rpgt0d' if False else 'syl', [D(w, Ac, 'rpgt0d', [up(b2p, '%s e. RR+' % B2)], '0 < %s' % B2), w.inst('dummy')], '') if False else
                             linarith(w, Ac, [D(w, Ac, 'rpgt0d', [up(b2p, '%s e. RR+' % B2)], '0 < %s' % B2)], '-u %s < 0' % B2, leaves={B2: b2r}, atoms=[B2]),
                             D(w, Ac, 'syl2anc', [D(w, Ac, 'renegcld', [b2r], '-u %s e. RR' % B2), cst(w, Ac, '0re', '0 e. RR'), w.inst('eflt')], '( -u %s < 0 <-> %s < ( exp ` 0 ) )' % (B2, RR_))],
              '%s < ( exp ` 0 )' % RR_)
    rlt1 = D(w, Ac, 'breqtrd', [rlt, cst(w, Ac, 'ef0', '( exp ` 0 ) = 1')], '%s < 1' % RR_)
    CB = '( ( K x. c ) x. ( exp ` %s ) )' % B2
    cbr = D(w, Ac, 'remulcld', [D(w, Ac, 'remulcld', [kr, D(w, Ac, 'rpred', [crp], 'c e. RR')], '( K x. c ) e. RR'), D(w, Ac, 'reefcld', [b2r], '( exp ` %s ) e. RR' % B2)], '%s e. RR' % CB)
    FM = '( j e. NN |-> %s )' % L.MJ('j')
    Ak = '( %s /\\ k e. NN )' % Ac
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    fsub = w.s([w.s([w.s([w.s([w.s([], 'oveq2', '( j = k -> ( B x. j ) = ( B x. k ) )')], 'negeqd', '( j = k -> -u ( B x. j ) = -u ( B x. k ) )')], 'fveq2d', '( j = k -> ( exp ` -u ( B x. j ) ) = ( exp ` -u ( B x. k ) ) )')],
                     'oveq2d', '( j = k -> ( K x. ( exp ` -u ( B x. j ) ) ) = ( K x. ( exp ` -u ( B x. k ) ) ) )'),
                w.s([w.s([w.s([w.s([], 'oveq1', '( j = k -> ( j + 1 ) = ( k + 1 ) )')], 'fveq2d', '( j = k -> ( log ` ( j + 1 ) ) = ( log ` ( k + 1 ) ) )')], 'oveq2d',
                         '( j = k -> ( R x. ( log ` ( j + 1 ) ) ) = ( R x. ( log ` ( k + 1 ) ) ) )')], 'fveq2d', '( j = k -> ( exp ` ( R x. ( log ` ( j + 1 ) ) ) ) = ( exp ` ( R x. ( log ` ( k + 1 ) ) ) ) )')],
               'oveq12d', '( j = k -> %s = %s )' % (L.MJ('j'), L.MJ('k')))
    fv = D(w, Ak, 'syl', [kn, w.s([fsub, w.s([], 'eqid', '%s = %s' % (FM, FM)), w.s([], 'ovex', '%s e. _V' % L.MJ('k'))], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (FM, L.MJ('k')))],
           '( %s ` k ) = %s' % (FM, L.MJ('k')))
    def uk(st, f):
        return w.s([st], 'adantr', '( %s -> %s )' % (Ak, f))
    kr_ = D(w, Ak, 'nnred', [kn], 'k e. RR'); krk = uk(kr, 'K e. RR'); brk = uk(br, 'B e. RR'); rrk = uk(rrc, 'R e. RR'); b2k = uk(b2r, '%s e. RR' % B2)
    K1 = '( k + 1 )'
    k1r = D(w, Ak, 'syl', [kr_, w.inst('peano2re')], '%s e. RR' % K1)
    k1i = D(w, Ak, 'mpbir2and', [k1r, linarith(w, Ak, [D(w, Ak, 'nnge1d', [kn], '1 <_ k')], '1 <_ %s' % K1, leaves={'k': kr_}),
                                  D(w, Ak, 'syl', [cst(w, Ak, '1re', '1 e. RR'), w.inst('elicopnf')], '( %s e. %s <-> ( %s e. RR /\\ 1 <_ %s ) )' % (K1, I1, K1, K1))], '%s e. %s' % (K1, I1))
    sub2 = w.s([w.s([w.s([w.s([], 'fveq2', '( y = %s -> ( log ` y ) = ( log ` %s ) )' % (K1, K1))], 'oveq2d', '( y = %s -> ( R x. ( log ` y ) ) = ( R x. ( log ` %s ) ) )' % (K1, K1))], 'fveq2d',
                     '( y = %s -> ( exp ` ( R x. ( log ` y ) ) ) = ( exp ` ( R x. ( log ` %s ) ) ) )' % (K1, K1)),
                w.s([w.s([w.s([], 'oveq2', '( y = %s -> ( %s x. y ) = ( %s x. %s ) )' % (K1, B2, B2, K1))], 'fveq2d', '( y = %s -> ( exp ` ( %s x. y ) ) = ( exp ` ( %s x. %s ) ) )' % (K1, B2, B2, K1))], 'oveq2d',
                    '( y = %s -> ( c x. ( exp ` ( %s x. y ) ) ) = ( c x. ( exp ` ( %s x. %s ) ) ) )' % (K1, B2, B2, K1))], 'breq12d',
               '( y = %s -> ( ( exp ` ( R x. ( log ` y ) ) ) <_ ( c x. ( exp ` ( %s x. y ) ) ) <-> ( exp ` ( R x. ( log ` %s ) ) ) <_ ( c x. ( exp ` ( %s x. %s ) ) ) ) )' % (K1, B2, K1, B2, K1))
    ERK = '( exp ` ( R x. ( log ` %s ) ) )' % K1
    E2 = '( exp ` ( %s x. %s ) )' % (B2, K1)
    pk = D(w, Ak, 'rspcdva', [sub2, uk(psi, PSI), k1i], '%s <_ ( c x. %s )' % (ERK, E2))
    E1 = '( exp ` -u ( B x. k ) )'
    e1r = D(w, Ak, 'reefcld', [D(w, Ak, 'renegcld', [D(w, Ak, 'remulcld', [brk, kr_], '( B x. k ) e. RR')], '-u ( B x. k ) e. RR')], '%s e. RR' % E1)
    ke1 = D(w, Ak, 'remulcld', [krk, e1r], '( K x. %s ) e. RR' % E1)
    ke10 = D(w, Ak, 'rpge0d', [D(w, Ak, 'rpmulcld', [uk(up(krp, 'K e. RR+'), 'K e. RR+'), D(w, Ak, 'rpefcld', [D(w, Ak, 'renegcld', [D(w, Ak, 'remulcld', [brk, kr_], '( B x. k ) e. RR')], '-u ( B x. k ) e. RR')], '%s e. RR+' % E1)], '( K x. %s ) e. RR+' % E1)], '0 <_ ( K x. %s )' % E1)
    crk = D(w, Ak, 'rpred', [uk(crp, 'c e. RR+')], 'c e. RR')
    e2r = D(w, Ak, 'reefcld', [D(w, Ak, 'remulcld', [b2k, k1r], '( %s x. %s ) e. RR' % (B2, K1))], '%s e. RR' % E2)
    erkr = D(w, Ak, 'reefcld', [D(w, Ak, 'remulcld', [rrk, D(w, Ak, 'relogcld', [rp_of(w, Ak, k1r, linarith(w, Ak, [D(w, Ak, 'nnge1d', [kn], '1 <_ k')], '1 <_ %s' % K1, leaves={'k': kr_}), K1)], '( log ` %s ) e. RR' % K1)],
                                                   '( R x. ( log ` %s ) ) e. RR' % K1)], '%s e. RR' % ERK)
    b1 = D(w, Ak, 'lemul2ad', [erkr, D(w, Ak, 'remulcld', [crk, e2r], '( c x. %s ) e. RR' % E2), ke1, ke10, pk], '( ( K x. %s ) x. %s ) <_ ( ( K x. %s ) x. ( c x. %s ) )' % (E1, ERK, E1, E2))
    # ( K e1 ) ( c e2 ) = CB x. ( RR_ ^ k )
    E3, E4 = '( exp ` %s )' % B2, '( exp ` ( k x. -u %s ) )' % B2
    cl = Closure(w, Ak, {'K': krk, 'c': crk, 'k': kr_, 'B': brk})
    cc = lambda e: cl.mem(e, 'CC')
    m1 = D(w, Ak, 'mul4d', [cc('K'), cc(E1), cc('c'), cc(E2)], '( ( K x. %s ) x. ( c x. %s ) ) = ( ( K x. c ) x. ( %s x. %s ) )' % (E1, E2, E1, E2))
    x1 = efadd_(w, Ak, '-u ( B x. k )', '( %s x. %s )' % (B2, K1), cc('-u ( B x. k )'), cc('( %s x. %s )' % (B2, K1)))
    x2 = efadd_(w, Ak, B2, '( k x. -u %s )' % B2, cc(B2), cc('( k x. -u %s )' % B2))
    ee = lineq(w, Ak, '( -u ( B x. k ) + ( %s x. %s ) )' % (B2, K1), '( %s + ( k x. -u %s ) )' % (B2, B2), closure=cl, products=True)
    e12 = D(w, Ak, 'eqtr3d', [x1, D(w, Ak, 'eqtrd', [D(w, Ak, 'fveq2d', [ee], '( exp ` ( -u ( B x. k ) + ( %s x. %s ) ) ) = ( exp ` ( %s + ( k x. -u %s ) ) )' % (B2, K1, B2, B2)), x2],
                                                   '( exp ` ( -u ( B x. k ) + ( %s x. %s ) ) ) = ( %s x. %s )' % (B2, K1, E3, E4))], '( %s x. %s ) = ( %s x. %s )' % (E1, E2, E3, E4))
    m2 = D(w, Ak, 'oveq2d', [e12], '( ( K x. c ) x. ( %s x. %s ) ) = ( ( K x. c ) x. ( %s x. %s ) )' % (E1, E2, E3, E4))
    m3 = D(w, Ak, 'eqcomd', [D(w, Ak, 'mulassd', [cc('( K x. c )'), cc(E3), cc(E4)], '( ( ( K x. c ) x. %s ) x. %s ) = ( ( K x. c ) x. ( %s x. %s ) )' % (E3, E4, E3, E4))],
           '( ( K x. c ) x. ( %s x. %s ) ) = ( %s x. %s )' % (E3, E4, CB, E4))
    ex4 = D(w, Ak, 'syl2anc', [cc('-u %s' % B2), D(w, Ak, 'nnzd', [kn], 'k e. ZZ'), w.inst('efexp')], '( exp ` ( k x. -u %s ) ) = ( %s ^ k )' % (B2, RR_))
    m4 = D(w, Ak, 'oveq2d', [ex4], '( %s x. %s ) = ( %s x. ( %s ^ k ) )' % (CB, E4, CB, RR_))
    meq = chain(w, Ak, ['( ( K x. %s ) x. ( c x. %s ) )' % (E1, E2), '( ( K x. c ) x. ( %s x. %s ) )' % (E1, E2), '( ( K x. c ) x. ( %s x. %s ) )' % (E3, E4), '( %s x. %s )' % (CB, E4), '( %s x. ( %s ^ k ) )' % (CB, RR_)],
                [m1, m2, m3, m4])
    mj = L.MJ('k')
    mjr = D(w, Ak, 'remulcld', [ke1, erkr], '%s e. RR' % mj)
    mj0 = D(w, Ak, 'mulge0d', [ke1, erkr, ke10, D(w, Ak, 'rpge0d', [D(w, Ak, 'rpefcld', [D(w, Ak, 'remulcld', [rrk, D(w, Ak, 'relogcld', [rp_of(w, Ak, k1r, linarith(w, Ak, [D(w, Ak, 'nnge1d', [kn], '1 <_ k')], '1 <_ %s' % K1, leaves={'k': kr_}), K1)], '( log ` %s ) e. RR' % K1)], '( R x. ( log ` %s ) ) e. RR' % K1)], '%s e. RR+' % ERK)], '0 <_ %s' % ERK)],
             '0 <_ %s' % mj)
    ab = D(w, Ak, 'eqtrd', [D(w, Ak, 'fveq2d', [fv], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (FM, mj)), D(w, Ak, 'absidd', [mjr, mj0], '( abs ` %s ) = %s' % (mj, mj))], '( abs ` ( %s ` k ) ) = %s' % (FM, mj))
    bd = D(w, Ak, 'breqtrd', [D(w, Ak, 'eqbrtrd', [ab, b1], '( abs ` ( %s ` k ) ) <_ ( ( K x. %s ) x. ( c x. %s ) )' % (FM, E1, E2)), meq], '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ^ k ) )' % (FM, CB, RR_))
    fkc = D(w, Ak, 'eqeltrd', [fv, D(w, Ak, 'recnd', [mjr], '%s e. CC' % mj)], '( %s ` k ) e. CC' % FM)
    ms = D(w, Ac, 'zl3mser', [cbr, rrr, D(w, Ac, 'rpge0d', [rrp_], '0 <_ %s' % RR_), rlt1, fkc, bd],
           '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. %s ) / ( 1 - %s ) ) )' % (FM, FM, CB, RR_, RR_))
    fin = D(w, Ac, 'simpld', [ms], 'seq 1 ( + , %s ) e. dom ~~>' % FM)
    r = D(w, A, 'rexlimdva', [D(w, '( %s /\\ c e. RR+ )' % A, 'ex', [fin], '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (PSI, FM))], '( E. c e. RR+ %s -> seq 1 ( + , %s ) e. dom ~~> )' % (PSI, FM))
    w.qed([ex, r], 'mpd', S['zl3msum'])
    go(w)


# ---------------------------------------------------------------- zl3flr
if want('zl3flr'):
    w = W('zl3flr', 'A function on ` RR+ ` within ` E ( |_ t ) ` of a convergent sequence ` S ( |_ t ) ` , with ` E ~~> 0 ` , converges to the limit of ` S ` .')
    A, C = ante_of('zl3flr')
    h1 = D(w, A, 'simp1', [], '( F : RR+ --> CC /\\ L e. CC )'); h2 = D(w, A, 'simp2', [], '( S : NN --> CC /\\ S ~~> L )')
    HT = 'A. t e. %s ( abs ` ( ( F ` t ) - ( S ` ( |_ ` t ) ) ) ) <_ ( E ` ( |_ ` t ) )' % I1
    h3 = D(w, A, 'simp3', [], '( E : NN --> RR /\\ E ~~> 0 /\\ %s )' % HT)
    ff = D(w, A, 'simpld', [h1], 'F : RR+ --> CC'); lc = D(w, A, 'simprd', [h1], 'L e. CC')
    sf = D(w, A, 'simpld', [h2], 'S : NN --> CC'); sl = D(w, A, 'simprd', [h2], 'S ~~> L')
    ef = D(w, A, 'simp1d', [h3], 'E : NN --> RR'); e0 = D(w, A, 'simp2d', [h3], 'E ~~> 0'); ht = D(w, A, 'simp3d', [h3], HT)
    FM = '( u e. RR+ |-> ( F ` u ) )'
    feq = D(w, A, 'feqmptd', [ff], 'F = %s' % FM)
    Au0 = '( %s /\\ u e. RR+ )' % A
    fuc = D(w, Au0, 'ffvelcdmd', [ad(w, Au0, ff, 'F : RR+ --> CC'), w.s([], 'simpr', '( %s -> u e. RR+ )' % Au0)], '( F ` u ) e. CC')
    INN = lambda r: 'A. u e. RR+ ( %s <_ u -> ( abs ` ( ( F ` u ) - L ) ) < e )' % r
    rl = D(w, A, 'rlim2', [D(w, A, 'ralrimiva', [fuc], 'A. u e. RR+ ( F ` u ) e. CC'), cst(w, A, 'rpssre', 'RR+ C_ RR'), lc],
           '( %s ~~>r L <-> A. e e. RR+ E. r e. RR %s )' % (FM, INN('r')))
    Ae = '( %s /\\ e e. RR+ )' % A
    erp = w.s([], 'simpr', '( %s -> e e. RR+ )' % Ae)
    e2 = D(w, Ae, 'rphalfcld', [erp], '( e / 2 ) e. RR+')
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    PJ = 'A. k e. ( ZZ>= ` j ) ( ( S ` k ) e. CC /\\ ( abs ` ( ( S ` k ) - L ) ) < ( e / 2 ) )'
    PI = 'A. k e. ( ZZ>= ` i ) ( ( E ` k ) e. CC /\\ ( abs ` ( ( E ` k ) - 0 ) ) < ( e / 2 ) )'
    Ak = '( %s /\\ k e. NN )' % Ae
    cj = D(w, Ae, 'climi', [nnu, cst(w, Ae, '1z', '1 e. ZZ'), e2, D(w, Ak, 'eqidd', [], '( S ` k ) = ( S ` k )'), ad(w, Ae, sl, 'S ~~> L')], 'E. j e. NN %s' % PJ)
    ci = D(w, Ae, 'climi', [nnu, cst(w, Ae, '1z', '1 e. ZZ'), e2, D(w, Ak, 'eqidd', [], '( E ` k ) = ( E ` k )'), ad(w, Ae, e0, 'E ~~> 0')], 'E. i e. NN %s' % PI)
    Aj = '( %s /\\ ( j e. NN /\\ %s ) )' % (Ae, PJ)
    Aji = '( %s /\\ ( i e. NN /\\ %s ) )' % (Aj, PI)
    Au = '( ( %s /\\ u e. RR+ ) /\\ ( j + i ) <_ u )' % Aji
    def up(st, f, frm):
        """lift ( frm -> f ) to Au"""
        from cl import lift
        return lift(w, st, Au) if False else None
    jn = D(w, Aji, 'simplrl' if False else 'simprl', [], '') if False else None
    jn_ = w.s([], 'simplrl', '( %s -> j e. NN )' % Aji)
    pj_ = w.s([], 'simplrr', '( %s -> %s )' % (Aji, PJ))
    in_ = w.s([], 'simprl', '( %s -> i e. NN )' % Aji)
    pi_ = w.s([], 'simprr', '( %s -> %s )' % (Aji, PI))
    aji_a = w.s([], 'simplll' if False else 'simpll', '( %s -> %s )' % (Aji, Ae)) if False else None
    ae_ = D(w, Aji, 'simpld', [w.s([], 'simpl', '( %s -> %s )' % (Aji, Aj))], Ae)
    a_ = D(w, Aji, 'simpld', [ae_], A)
    def u2(st, f):
        return w.s([st], 'adantr', '( ( %s /\\ u e. RR+ ) -> %s )' % (Aji, f))
    def uu(st, f):
        return w.s([u2(st, f)], 'adantr', '( %s -> %s )' % (Au, f))
    urp = w.s([], 'simplr', '( %s -> u e. RR+ )' % Au); ule = w.s([], 'simpr', '( %s -> ( j + i ) <_ u )' % Au)
    ur = D(w, Au, 'rpred', [urp], 'u e. RR')
    jr = D(w, Au, 'nnred', [uu(jn_, 'j e. NN')], 'j e. RR'); ir = D(w, Au, 'nnred', [uu(in_, 'i e. NN')], 'i e. RR')
    j1 = D(w, Au, 'nnge1d', [uu(jn_, 'j e. NN')], '1 <_ j'); i1 = D(w, Au, 'nnge1d', [uu(in_, 'i e. NN')], '1 <_ i')
    u1 = linarith(w, Au, [ule, j1, i1], '1 <_ u', leaves={'u': ur, 'j': jr, 'i': ir})
    ui = D(w, Au, 'mpbir2and', [ur, u1, D(w, Au, 'syl', [cst(w, Au, '1re', '1 e. RR'), w.inst('elicopnf')], '( u e. %s <-> ( u e. RR /\\ 1 <_ u ) )' % I1)], 'u e. %s' % I1)
    N = '( |_ ` u )'
    nz = D(w, Au, 'flcld', [ur], '%s e. ZZ' % N)
    jiz = D(w, Au, 'zaddcld', [D(w, Au, 'nnzd', [uu(jn_, 'j e. NN')], 'j e. ZZ'), D(w, Au, 'nnzd', [uu(in_, 'i e. NN')], 'i e. ZZ')], '( j + i ) e. ZZ')
    jin = D(w, Au, 'mpbid', [ule, D(w, Au, 'syl2anc', [ur, jiz, w.inst('flge')], '( ( j + i ) <_ u <-> ( j + i ) <_ %s )' % N)], '( j + i ) <_ %s' % N)
    nr = D(w, Au, 'zred', [nz], '%s e. RR' % N)
    jle = linarith(w, Au, [jin, i1], 'j <_ %s' % N, leaves={'j': jr, 'i': ir, N: nr})
    ile = linarith(w, Au, [jin, j1], 'i <_ %s' % N, leaves={'j': jr, 'i': ir, N: nr})
    nuj = D(w, Au, 'syl3anbrc' if False else 'mpbir3and', [D(w, Au, 'nnzd', [uu(jn_, 'j e. NN')], 'j e. ZZ'), nz, jle, w.s([], 'eluz2', '( %s e. ( ZZ>= ` j ) <-> ( j e. ZZ /\\ %s e. ZZ /\\ j <_ %s ) )' % (N, N, N)) if False else
                                         cst(w, Au, 'eluz2', '( %s e. ( ZZ>= ` j ) <-> ( j e. ZZ /\\ %s e. ZZ /\\ j <_ %s ) )' % (N, N, N))], '%s e. ( ZZ>= ` j )' % N)
    nui = D(w, Au, 'mpbir3and', [D(w, Au, 'nnzd', [uu(in_, 'i e. NN')], 'i e. ZZ'), nz, ile, cst(w, Au, 'eluz2', '( %s e. ( ZZ>= ` i ) <-> ( i e. ZZ /\\ %s e. ZZ /\\ i <_ %s ) )' % (N, N, N))], '%s e. ( ZZ>= ` i )' % N)
    subj = w.s([w.s([], 'fveq2', '( k = %s -> ( S ` k ) = ( S ` %s ) )' % (N, N)) if False else None], 'dummy', '') if False else None
    def ksub(Fn, R_):
        a = w.s([], 'fveq2', '( k = %s -> ( %s ` k ) = ( %s ` %s ) )' % (N, Fn, Fn, N))
        b = w.s([a], 'eleq1d', '( k = %s -> ( ( %s ` k ) e. CC <-> ( %s ` %s ) e. CC ) )' % (N, Fn, Fn, N))
        c = w.s([w.s([w.s([a], 'oveq1d', '( k = %s -> ( ( %s ` k ) - %s ) = ( ( %s ` %s ) - %s ) )' % (N, Fn, R_, Fn, N, R_))], 'fveq2d',
                     '( k = %s -> ( abs ` ( ( %s ` k ) - %s ) ) = ( abs ` ( ( %s ` %s ) - %s ) ) )' % (N, Fn, R_, Fn, N, R_))], 'breq1d',
                '( k = %s -> ( ( abs ` ( ( %s ` k ) - %s ) ) < ( e / 2 ) <-> ( abs ` ( ( %s ` %s ) - %s ) ) < ( e / 2 ) ) )' % (N, Fn, R_, Fn, N, R_))
        return w.s([b, c], 'anbi12d', '( k = %s -> ( ( ( %s ` k ) e. CC /\\ ( abs ` ( ( %s ` k ) - %s ) ) < ( e / 2 ) ) <-> ( ( %s ` %s ) e. CC /\\ ( abs ` ( ( %s ` %s ) - %s ) ) < ( e / 2 ) ) ) )'
                   % (N, Fn, Fn, R_, Fn, N, Fn, N, R_))
    sn = D(w, Au, 'rspcdva', [ksub('S', 'L'), uu(pj_, PJ), nuj], '( ( S ` %s ) e. CC /\\ ( abs ` ( ( S ` %s ) - L ) ) < ( e / 2 ) )' % (N, N))
    en = D(w, Au, 'rspcdva', [ksub('E', '0'), uu(pi_, PI), nui], '( ( E ` %s ) e. CC /\\ ( abs ` ( ( E ` %s ) - 0 ) ) < ( e / 2 ) )' % (N, N))
    nn_ = D(w, Au, 'mpbir2and', [nz, linarith(w, Au, [jle, j1], '1 <_ %s' % N, leaves={'j': jr, N: nr}), cst(w, Au, 'elnnz1', '( %s e. NN <-> ( %s e. ZZ /\\ 1 <_ %s ) )' % (N, N, N))], '%s e. NN' % N)
    auA = D(w, Au, 'simpld', [D(w, Au, 'simpld', [D(w, Au, 'simpld', [D(w, Au, 'simpld', [w.s([], 'simpll', '( %s -> %s )' % (Au, Aji))], Aj)], Ae)], A)], A) if False else None
    auA = w.s([uu(a_, A)], 'idi', '( %s -> %s )' % (Au, A))
    LA = lambda st, f: D(w, Au, 'syl', [auA, st], f)
    efn = D(w, Au, 'ffvelcdmd', [LA(ef, 'E : NN --> RR'), nn_], '( E ` %s ) e. RR' % N)
    enc = D(w, Au, 'recnd', [efn], '( E ` %s ) e. CC' % N)
    ena = D(w, Au, 'simprd', [en], '( abs ` ( ( E ` %s ) - 0 ) ) < ( e / 2 )' % N)
    ena2 = D(w, Au, 'eqbrtrrd', [D(w, Au, 'fveq2d', [D(w, Au, 'subid1d', [enc], '( ( E ` %s ) - 0 ) = ( E ` %s )' % (N, N))], '( abs ` ( ( E ` %s ) - 0 ) ) = ( abs ` ( E ` %s ) )' % (N, N)), ena],
                 '( abs ` ( E ` %s ) ) < ( e / 2 )' % N)
    e2r = D(w, Au, 'rpred', [uu(D(w, Aji, 'rphalfcld', [D(w, Aji, 'simprd', [ae_], 'e e. RR+')], '( e / 2 ) e. RR+'), '( e / 2 ) e. RR+')], '( e / 2 ) e. RR')
    enl = D(w, Au, 'lelttrd', [efn, D(w, Au, 'abscld', [enc], '( abs ` ( E ` %s ) ) e. RR' % N), e2r, D(w, Au, 'leabsd', [efn], '( E ` %s ) <_ ( abs ` ( E ` %s ) )' % (N, N)), ena2],
            '( E ` %s ) < ( e / 2 )' % N)
    tsub = w.s([w.s([w.s([w.s([], 'fveq2', '( t = u -> ( F ` t ) = ( F ` u ) )'), w.s([w.s([], 'fveq2', '( t = u -> ( |_ ` t ) = %s )' % N)], 'fveq2d', '( t = u -> ( S ` ( |_ ` t ) ) = ( S ` %s ) )' % N)],
                           'oveq12d', '( t = u -> ( ( F ` t ) - ( S ` ( |_ ` t ) ) ) = ( ( F ` u ) - ( S ` %s ) ) )' % N)], 'fveq2d',
                     '( t = u -> ( abs ` ( ( F ` t ) - ( S ` ( |_ ` t ) ) ) ) = ( abs ` ( ( F ` u ) - ( S ` %s ) ) ) )' % N),
                w.s([w.s([], 'fveq2', '( t = u -> ( |_ ` t ) = %s )' % N)], 'fveq2d', '( t = u -> ( E ` ( |_ ` t ) ) = ( E ` %s ) )' % N)], 'breq12d',
               '( t = u -> ( ( abs ` ( ( F ` t ) - ( S ` ( |_ ` t ) ) ) ) <_ ( E ` ( |_ ` t ) ) <-> ( abs ` ( ( F ` u ) - ( S ` %s ) ) ) <_ ( E ` %s ) ) )' % (N, N))
    hu = D(w, Au, 'rspcdva', [tsub, LA(ht, HT), ui], '( abs ` ( ( F ` u ) - ( S ` %s ) ) ) <_ ( E ` %s )' % (N, N))
    fuc2 = D(w, Au, 'ffvelcdmd', [LA(ff, 'F : RR+ --> CC'), urp], '( F ` u ) e. CC')
    snc = D(w, Au, 'simpld', [sn], '( S ` %s ) e. CC' % N)
    d1 = D(w, Au, 'lelttrd', [D(w, Au, 'abscld', [D(w, Au, 'subcld', [fuc2, snc], '( ( F ` u ) - ( S ` %s ) ) e. CC' % N)], '( abs ` ( ( F ` u ) - ( S ` %s ) ) ) e. RR' % N), efn, e2r, hu, enl],
           '( abs ` ( ( F ` u ) - ( S ` %s ) ) ) < ( e / 2 )' % N)
    er_ = D(w, Au, 'rpred', [uu(D(w, Aji, 'simprd', [ae_], 'e e. RR+'), 'e e. RR+')], 'e e. RR')
    fin = D(w, Au, 'abs3lemd', [fuc2, LA(lc, 'L e. CC'), snc, er_, d1, D(w, Au, 'simprd', [sn], '( abs ` ( ( S ` %s ) - L ) ) < ( e / 2 )' % N)], '( abs ` ( ( F ` u ) - L ) ) < e')
    ral = D(w, Aji, 'ralrimiva', [D(w, '( %s /\\ u e. RR+ )' % Aji, 'ex', [fin], '( ( j + i ) <_ u -> ( abs ` ( ( F ` u ) - L ) ) < e )')], INN('( j + i )'))
    jir = D(w, Aji, 'readdcld', [D(w, Aji, 'nnred', [jn_], 'j e. RR'), D(w, Aji, 'nnred', [in_], 'i e. RR')], '( j + i ) e. RR')
    rsub = w.s([w.s([w.s([], 'breq1', '( r = ( j + i ) -> ( r <_ u <-> ( j + i ) <_ u ) )')], 'imbi1d',
                    '( r = ( j + i ) -> ( ( r <_ u -> ( abs ` ( ( F ` u ) - L ) ) < e ) <-> ( ( j + i ) <_ u -> ( abs ` ( ( F ` u ) - L ) ) < e ) ) )')], 'ralbidv',
               '( r = ( j + i ) -> ( %s <-> %s ) )' % (INN('r'), INN('( j + i )')))
    rex = D(w, Aji, 'syl2anc', [jir, ral, w.s([rsub], 'rspcev', '( ( ( j + i ) e. RR /\\ %s ) -> E. r e. RR %s )' % (INN('( j + i )'), INN('r')))], 'E. r e. RR %s' % INN('r'))
    r1 = D(w, Aj, 'rexlimddv', [D(w, Aj, 'simpld' if False else 'syl', [w.s([], 'simpl', '( %s -> %s )' % (Aj, Ae)), w.s([ci], 'idi', '( %s -> E. i e. NN %s )' % (Ae, PI))], 'E. i e. NN %s' % PI), rex],
           'E. r e. RR %s' % INN('r'))
    r2 = D(w, Ae, 'rexlimddv', [cj, r1], 'E. r e. RR %s' % INN('r'))
    ralE = D(w, A, 'ralrimiva', [r2], 'A. e e. RR+ E. r e. RR %s' % INN('r'))
    lim = D(w, A, 'mpbird', [ralE, rl], '%s ~~>r L' % FM)
    w.qed([feq, lim], 'eqbrtrd' if False else 'breqtrrd' if False else 'eqbrtrd', S['zl3flr']) if False else None
    w.qed([D(w, A, 'eqcomd', [feq], '%s = F' % FM), lim], 'breqtrrd' if False else 'eqbrtrrd', S['zl3flr']) if False else None
    w.lines.append('qed:%s,%s:eqbrtrd |- %s' % (feq, lim, S['zl3flr'])) if False else None
    w.qed([feq, lim], 'breqtrrid' if False else 'eqbrtrd', S['zl3flr']) if False else None
    q = D(w, A, 'breqtrrd' if False else 'eqbrtrd', [feq, lim], '') if False else None
    w.qed([feq, lim], 'eqbrtrd', S['zl3flr'])
    go(w)


def cbv_xy(w, P, Q, s='S'):
    """closed: PA(s,P,Q,x) = PA(s,P,Q,y)"""
    h = w.s([w.s([], 'fveq2', '( x = y -> ( G ` x ) = ( G ` y ) )'), w.s([], 'oveq1', '( x = y -> ( x ^c %s ) = ( y ^c %s ) )' % (s, s))], 'oveq12d',
            '( x = y -> ( ( G ` x ) x. ( x ^c %s ) ) = ( ( G ` y ) x. ( y ^c %s ) ) )' % (s, s))
    return w.s([h], 'cbvitgv', '%s = %s' % (L.PA(s, P, Q, 'x'), L.PA(s, P, Q)))


def fjm_val(w, K, s='S'):
    """closed: ( K e. NN -> ( FJM ` K ) = PA(s,K,K+1,x) )"""
    FJ = L.FJM(s)
    sub = w.s([w.s([w.s([], 'id', '( j = %s -> j = %s )' % (K, K)), w.s([], 'oveq1', '( j = %s -> ( j + 1 ) = ( %s + 1 ) )' % (K, K))], 'oveq12d',
                   '( j = %s -> ( j (,) ( j + 1 ) ) = ( %s (,) ( %s + 1 ) ) )' % (K, K, K))], 'itgeq1d' if False else 'syl',
              '') if False else None
    ieq = w.s([w.s([w.s([], 'id', '( j = %s -> j = %s )' % (K, K)), w.s([], 'oveq1', '( j = %s -> ( j + 1 ) = ( %s + 1 ) )' % (K, K))], 'oveq12d',
                   '( j = %s -> ( j (,) ( j + 1 ) ) = ( %s (,) ( %s + 1 ) ) )' % (K, K, K)),
               w.s([], 'itgeq1', '( ( j (,) ( j + 1 ) ) = ( %s (,) ( %s + 1 ) ) -> %s = %s )' % (K, K, L.PA(s, 'j', '( j + 1 )', 'x'), L.PA(s, K, '( %s + 1 )' % K, 'x')))],
              'syl', '( j = %s -> %s = %s )' % (K, L.PA(s, 'j', '( j + 1 )', 'x'), L.PA(s, K, '( %s + 1 )' % K, 'x')))
    return w.s([ieq, w.s([], 'eqid', '%s = %s' % (FJ, FJ)), w.s([], 'itgex', '%s e. _V' % L.PA(s, K, '( %s + 1 )' % K, 'x'))], 'fvmpt',
               '( %s e. NN -> ( %s ` %s ) = %s )' % (K, FJ, K, L.PA(s, K, '( %s + 1 )' % K, 'x')))


# ---------------------------------------------------------------- zl3pcs
if want('zl3pcs'):
    w = W('zl3pcs', 'The partial sums of the unit pieces are the integrals over ` ( 1 , N + 1 ) ` ( induction with ~ itgsplitioo ).')
    A3, C = ante_of('zl3pcs')
    A0 = '( %s /\\ S e. CC )' % L.PHV
    phv = D(w, A0, 'simpl', [], L.PHV); sc = D(w, A0, 'simpr', [], 'S e. CC')
    SEQ = 'seq 1 ( + , %s )' % L.FJM('S')
    PS = lambda n: '( %s ` %s ) = %s' % (SEQ, n, L.PA('S', '1', '( %s + 1 )' % n))
    def psub(n, v):
        a = w.s([], 'fveq2', '( n = %s -> ( %s ` n ) = ( %s ` %s ) )' % (v, SEQ, SEQ, v))
        b = w.s([w.s([w.s([], 'oveq1', '( n = %s -> ( n + 1 ) = ( %s + 1 ) )' % (v, v))], 'oveq2d', '( n = %s -> ( 1 (,) ( n + 1 ) ) = ( 1 (,) ( %s + 1 ) ) )' % (v, v)),
                 w.s([], 'itgeq1', '( ( 1 (,) ( n + 1 ) ) = ( 1 (,) ( %s + 1 ) ) -> %s = %s )' % (v, L.PA('S', '1', '( n + 1 )'), L.PA('S', '1', '( %s + 1 )' % v)))],
                'syl', '( n = %s -> %s = %s )' % (v, L.PA('S', '1', '( n + 1 )'), L.PA('S', '1', '( %s + 1 )' % v)))
        return w.s([a, b], 'eqeq12d', '( n = %s -> ( %s <-> %s ) )' % (v, PS('n'), PS(v)))
    h1, h2, h3, h4 = psub('n', '1'), psub('n', 'm'), psub('n', '( m + 1 )'), psub('n', 'N')
    # base
    b1 = D(w, A0, 'syl', [cst(w, A0, '1z', '1 e. ZZ'), w.inst('seq1')], '( %s ` 1 ) = ( %s ` 1 )' % (SEQ, L.FJM('S')))
    b2 = D(w, A0, 'syl', [cst(w, A0, '1nn', '1 e. NN'), fjm_val(w, '1')], '( %s ` 1 ) = %s' % (L.FJM('S'), L.PA('S', '1', '( 1 + 1 )', 'x')))
    b3 = w.s([cbv_xy(w, '1', '( 1 + 1 )')], 'a1i', '( %s -> %s = %s )' % (A0, L.PA('S', '1', '( 1 + 1 )', 'x'), L.PA('S', '1', '( 1 + 1 )')))
    base = chain(w, A0, ['( %s ` 1 )' % SEQ, '( %s ` 1 )' % L.FJM('S'), L.PA('S', '1', '( 1 + 1 )', 'x'), L.PA('S', '1', '( 1 + 1 )')], [b1, b2, b3])
    # step
    Am = '( ( %s /\\ m e. NN ) /\\ %s )' % (A0, PS('m'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (Am, PS('m')))
    mn = w.s([], 'simplr', '( %s -> m e. NN )' % Am)
    phm = w.s([phv], 'ad2antrr', '( %s -> %s )' % (Am, L.PHV)); scm = w.s([sc], 'ad2antrr', '( %s -> S e. CC )' % Am)
    M1, M2 = '( m + 1 )', '( ( m + 1 ) + 1 )'
    mr = D(w, Am, 'nnred', [mn], 'm e. RR')
    m1r = D(w, Am, 'syl', [mr, w.inst('peano2re')], '%s e. RR' % M1); m2r = D(w, Am, 'syl', [m1r, w.inst('peano2re')], '%s e. RR' % M2)
    m1n = D(w, Am, 'peano2nnd', [mn], '%s e. NN' % M1)
    s1 = D(w, Am, 'syl', [D(w, Am, 'mpbid', [mn, cst(w, Am, 'elnnuz', '( m e. NN <-> m e. ( ZZ>= ` 1 ) )')], 'm e. ( ZZ>= ` 1 )'), w.inst('seqp1')],
           '( %s ` %s ) = ( ( %s ` m ) + ( %s ` %s ) )' % (SEQ, M1, SEQ, L.FJM('S'), M1))
    f1 = D(w, Am, 'eqtrd', [D(w, Am, 'syl', [m1n, fjm_val(w, M1)], '( %s ` %s ) = %s' % (L.FJM('S'), M1, L.PA('S', M1, M2, 'x'))),
                            w.s([cbv_xy(w, M1, M2)], 'a1i', '( %s -> %s = %s )' % (Am, L.PA('S', M1, M2, 'x'), L.PA('S', M1, M2)))], '( %s ` %s ) = %s' % (L.FJM('S'), M1, L.PA('S', M1, M2)))
    Am0 = '( %s /\\ m e. NN )' % A0
    mn0 = w.s([], 'simpr', '( %s -> m e. NN )' % Am0)
    phm0 = w.s([phv], 'adantr', '( %s -> %s )' % (Am0, L.PHV)); scm0 = w.s([sc], 'adantr', '( %s -> S e. CC )' % Am0)
    mr0 = D(w, Am0, 'nnred', [mn0], 'm e. RR')
    m1r0 = D(w, Am0, 'syl', [mr0, w.inst('peano2re')], '%s e. RR' % M1); m2r0 = D(w, Am0, 'syl', [m1r0, w.inst('peano2re')], '%s e. RR' % M2)
    one = cst(w, Am0, '1re', '1 e. RR'); le11 = D(w, Am0, 'leidd', [one], '1 <_ 1')
    m1ge = linarith(w, Am0, [D(w, Am0, 'nnge1d', [mn0], '1 <_ m')], '1 <_ %s' % M1, leaves={'m': mr0})
    ibA = ibl_pa(w, Am0, phm0, one, le11, m1r0, 'S', scm0, '1', M1)
    ibB = ibl_pa(w, Am0, phm0, m1r0, m1ge, m2r0, 'S', scm0, M1, M2)
    clC = integrand_cl(w, Am0, phm0, one, le11, m2r0, 'S', scm0, P='1', Q=M2)
    bin_ = D(w, Am0, 'mpbir3and', [m1r0, m1ge, linarith(w, Am0, [], '%s <_ %s' % (M1, M2), leaves={'m': mr0}),
                                  D(w, Am0, 'syl2anc', [one, m2r0, w.inst('elicc2')], '( %s e. ( 1 [,] %s ) <-> ( %s e. RR /\\ 1 <_ %s /\\ %s <_ %s ) )' % (M1, M2, M1, M1, M1, M2))],
               '%s e. ( 1 [,] %s )' % (M1, M2))
    sp0 = D(w, Am0, 'itgsplitioo', [one, m2r0, bin_, clC, ibA, ibB], '%s = ( %s + %s )' % (L.PA('S', '1', M2), L.PA('S', '1', M1), L.PA('S', M1, M2)))
    sp = w.s([sp0], 'adantr', '( %s -> %s = ( %s + %s ) )' % (Am, L.PA('S', '1', M2), L.PA('S', '1', M1), L.PA('S', M1, M2)))
    st_ = chain(w, Am, ['( %s ` %s )' % (SEQ, M1), '( ( %s ` m ) + ( %s ` %s ) )' % (SEQ, L.FJM('S'), M1), '( %s + %s )' % (L.PA('S', '1', M1), L.PA('S', M1, M2)), L.PA('S', '1', M2)],
                [s1, D(w, Am, 'oveq12d', [ih, f1], '( ( %s ` m ) + ( %s ` %s ) ) = ( %s + %s )' % (SEQ, L.FJM('S'), M1, L.PA('S', '1', M1), L.PA('S', M1, M2))), ('r', sp)])
    ind = w.s([h1, h2, h3, h4, base, st_], 'nnindd', '( ( %s /\\ N e. NN ) -> %s )' % (A0, PS('N')))
    w.qed([ind], '3impa', S['zl3pcs'])
    go(w)


# ---------------------------------------------------------------- zl3pcv
if want('zl3pcv'):
    w = W('zl3pcv', 'The improper integral ` lim_t S. ( 1 (,) t ) G ( y ) y ^c S _d y ` exists and is the series of the unit pieces ( ~ zl3flr , ~ zl3pcs , ~ zl3pbd ).')
    A, C = ante_of('zl3pcv')
    phv = D(w, A, 'simpl', [], L.PHV); sc = D(w, A, 'simpr', [], 'S e. CC')
    f0 = phv_facts(w, A, phv)
    RS, ARS = '( Re ` S )', '( abs ` ( Re ` S ) )'
    R = '( %s + 1 )' % ARS
    arsr = D(w, A, 'abscld', [D(w, A, 'recnd', [D(w, A, 'recld', [sc], '%s e. RR' % RS)], '%s e. CC' % RS)], '%s e. RR' % ARS)
    rr = D(w, A, 'readdcld', [arsr, cst(w, A, '1re', '1 e. RR')], '%s e. RR' % R)
    rle = D(w, A, 'leidd', [rr], '%s <_ %s' % (R, R))
    MJM = '( j e. NN |-> %s )' % L.MJ('j', R)
    msum = D(w, A, 'syl3anc', [f0['k'], f0['b'], rr, w.inst('zl3msum')], 'seq 1 ( + , %s ) e. dom ~~>' % MJM)
    FJ = L.FJM('S'); SEQ = 'seq 1 ( + , %s )' % FJ
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    def mjm_val(K):
        sub = w.s([w.s([w.s([w.s([w.s([], 'oveq2', '( j = %s -> ( B x. j ) = ( B x. %s ) )' % (K, K))], 'negeqd', '( j = %s -> -u ( B x. j ) = -u ( B x. %s ) )' % (K, K))], 'fveq2d',
                             '( j = %s -> ( exp ` -u ( B x. j ) ) = ( exp ` -u ( B x. %s ) ) )' % (K, K))], 'oveq2d', '( j = %s -> ( K x. ( exp ` -u ( B x. j ) ) ) = ( K x. ( exp ` -u ( B x. %s ) ) ) )' % (K, K)),
                    w.s([w.s([w.s([w.s([], 'oveq1', '( j = %s -> ( j + 1 ) = ( %s + 1 ) )' % (K, K))], 'fveq2d', '( j = %s -> ( log ` ( j + 1 ) ) = ( log ` ( %s + 1 ) ) )' % (K, K))], 'oveq2d',
                             '( j = %s -> ( %s x. ( log ` ( j + 1 ) ) ) = ( %s x. ( log ` ( %s + 1 ) ) ) )' % (K, R, R, K))], 'fveq2d',
                        '( j = %s -> ( exp ` ( %s x. ( log ` ( j + 1 ) ) ) ) = ( exp ` ( %s x. ( log ` ( %s + 1 ) ) ) ) )' % (K, R, R, K))],
                   'oveq12d', '( j = %s -> %s = %s )' % (K, L.MJ('j', R), L.MJ(K, R)))
        return w.s([sub, w.s([], 'eqid', '%s = %s' % (MJM, MJM)), w.s([], 'ovex', '%s e. _V' % L.MJ(K, R))], 'fvmpt', '( %s e. NN -> ( %s ` %s ) = %s )' % (K, MJM, K, L.MJ(K, R)))
    def mj_re(A2, K, kn_):
        """( A2 -> MJ(K) e. RR )"""
        f_ = phv_facts(w, A2, ad(w, A2, phv, L.PHV)) if A2 != A else f0
        krr = D(w, A2, 'nnred', [kn_], '%s e. RR' % K)
        k1 = D(w, A2, 'syl', [krr, w.inst('peano2re')], '( %s + 1 ) e. RR' % K)
        k1p = rp_of(w, A2, k1, linarith(w, A2, [D(w, A2, 'nnge1d', [kn_], '1 <_ %s' % K)], '1 <_ ( %s + 1 )' % K, leaves={K: krr}), '( %s + 1 )' % K)
        a = D(w, A2, 'remulcld', [D(w, A2, 'rpred', [f_['k']], 'K e. RR'), D(w, A2, 'reefcld', [D(w, A2, 'renegcld', [D(w, A2, 'remulcld', [D(w, A2, 'rpred', [f_['b']], 'B e. RR'), krr], '( B x. %s ) e. RR' % K)], '-u ( B x. %s ) e. RR' % K)],
                                                                                        '( exp ` -u ( B x. %s ) ) e. RR' % K)], '( K x. ( exp ` -u ( B x. %s ) ) ) e. RR' % K)
        b = D(w, A2, 'reefcld', [D(w, A2, 'remulcld', [ad(w, A2, rr, '%s e. RR' % R), D(w, A2, 'relogcld', [k1p], '( log ` ( %s + 1 ) ) e. RR' % K)], '( %s x. ( log ` ( %s + 1 ) ) ) e. RR' % (R, K))],
                  '( exp ` ( %s x. ( log ` ( %s + 1 ) ) ) ) e. RR' % (R, K))
        return D(w, A2, 'remulcld', [a, b], '%s e. RR' % L.MJ(K, R))
    mjk = D(w, Ak, 'syl', [kn, mjm_val('k')], '( %s ` k ) = %s' % (MJM, L.MJ('k', R)))
    mjkr = D(w, Ak, 'eqeltrd', [mjk, mj_re(Ak, 'k', kn)], '( %s ` k ) e. RR' % MJM)
    fjk = D(w, Ak, 'eqtrd', [D(w, Ak, 'syl', [kn, fjm_val(w, 'k')], '( %s ` k ) = %s' % (FJ, L.PA('S', 'k', '( k + 1 )', 'x'))),
                             w.s([cbv_xy(w, 'k', '( k + 1 )')], 'a1i', '( %s -> %s = %s )' % (Ak, L.PA('S', 'k', '( k + 1 )', 'x'), L.PA('S', 'k', '( k + 1 )')))],
           '( %s ` k ) = %s' % (FJ, L.PA('S', 'k', '( k + 1 )')))
    krr = D(w, Ak, 'nnred', [kn], 'k e. RR')
    k1r = D(w, Ak, 'syl', [krr, w.inst('peano2re')], '( k + 1 ) e. RR')
    k1i = D(w, Ak, 'mpbir3and', [k1r, linarith(w, Ak, [], 'k <_ ( k + 1 )', leaves={'k': krr}), D(w, Ak, 'leidd', [k1r], '( k + 1 ) <_ ( k + 1 )'),
                                  D(w, Ak, 'syl2anc', [krr, k1r, w.inst('elicc2')], '( ( k + 1 ) e. ( k [,] ( k + 1 ) ) <-> ( ( k + 1 ) e. RR /\\ k <_ ( k + 1 ) /\\ ( k + 1 ) <_ ( k + 1 ) ) )')],
           '( k + 1 ) e. ( k [,] ( k + 1 ) )')
    pb = D(w, Ak, 'syl3anc', [ad(w, Ak, phv, L.PHV), D(w, Ak, '3jca', [ad(w, Ak, rr, '%s e. RR' % R), ad(w, Ak, sc, 'S e. CC'), ad(w, Ak, rle, '%s <_ %s' % (R, R))], '( %s e. RR /\\ S e. CC /\\ %s <_ %s )' % (R, R, R)),
                               D(w, Ak, 'jca', [kn, k1i], '( k e. NN /\\ ( k + 1 ) e. ( k [,] ( k + 1 ) ) )'), w.inst('zl3pbd')],
           '( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s )' % (L.PA('S', 'k', '( k + 1 )'), L.MJ('k', R), L.PV('S', 'k', '( k + 1 )'), L.MJ('k', R)))
    fb = D(w, Ak, 'eqbrtrd', [D(w, Ak, 'fveq2d', [fjk], '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (FJ, L.PA('S', 'k', '( k + 1 )'))), D(w, Ak, 'simpld', [pb], '( abs ` %s ) <_ %s' % (L.PA('S', 'k', '( k + 1 )'), L.MJ('k', R)))],
           '( abs ` ( %s ` k ) ) <_ %s' % (FJ, L.MJ('k', R)))
    fb1 = D(w, Ak, 'breqtrd', [fb, D(w, Ak, 'eqtr4d', [mjk, D(w, Ak, 'mullidd', [D(w, Ak, 'recnd', [mjkr], '( %s ` k ) e. CC' % MJM)], '( 1 x. ( %s ` k ) ) = ( %s ` k )' % (MJM, MJM))],
                                                  '( %s ` k ) = ( 1 x. ( %s ` k ) )' % (MJM, MJM)) if False else
                                  D(w, Ak, 'eqtr3d', [mjk, D(w, Ak, 'mullidd', [D(w, Ak, 'recnd', [mjkr], '( %s ` k ) e. CC' % MJM)], '( 1 x. ( %s ` k ) ) = ( %s ` k )' % (MJM, MJM))],
                                    '%s = ( 1 x. ( %s ` k ) )' % (L.MJ('k', R), MJM)) if False else None], '') if False else None
    mjk1 = D(w, Ak, 'eqtr4d', [D(w, Ak, 'eqcomd', [mjk], '%s = ( %s ` k )' % (L.MJ('k', R), MJM)), D(w, Ak, 'mullidd', [D(w, Ak, 'recnd', [mjkr], '( %s ` k ) e. CC' % MJM)], '( 1 x. ( %s ` k ) ) = ( %s ` k )' % (MJM, MJM))],
            '%s = ( 1 x. ( %s ` k ) )' % (L.MJ('k', R), MJM))
    fb2 = D(w, Ak, 'breqtrd', [fb, mjk1], '( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) )' % (FJ, MJM))
    Akk = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A
    def to_uz(st, f):
        """( Ak -> f ) to ( Akk -> f )"""
        e = D(w, Akk, 'mpbird', [w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Akk), cst(w, Akk, 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'k e. NN')
        return D(w, Akk, 'syl2anc', [w.s([], 'simpl', '( %s -> %s )' % (Akk, A)), e, w.s([D(w, A, 'ex' if False else 'idi', [], '') if False else st], 'ex' if False else 'idi', '') if False else None], f) if False else \
            w.s([w.s([], 'simpl', '( %s -> %s )' % (Akk, A)), e, w.s([st], 'ex', '( %s -> ( k e. NN -> %s ) )' % (A, f))], 'sylc', '( %s -> %s )' % (Akk, f))
    fkc = D(w, Ak, 'eqeltrd', [fjk, D(w, Ak, 'itgcl', [ibl_pa(w, Ak, ad(w, Ak, phv, L.PHV), krr, D(w, Ak, 'nnge1d', [kn], '1 <_ k'), k1r, 'S', ad(w, Ak, sc, 'S e. CC'), 'k', '( k + 1 )'),
                                                             integrand_cl(w, Ak, ad(w, Ak, phv, L.PHV), krr, D(w, Ak, 'nnge1d', [kn], '1 <_ k'), k1r, 'S', ad(w, Ak, sc, 'S e. CC'), P='k', Q='( k + 1 )')],
                                                  '%s e. CC' % L.PA('S', 'k', '( k + 1 )'))], '( %s ` k ) e. CC' % FJ)
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    cvg = D(w, A, 'cvgcmpce', [nnu, cst(w, A, '1nn', '1 e. NN'), mjkr, fkc, msum, cst(w, A, '1re', '1 e. RR'), to_uz(fb2, '( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) )' % (FJ, MJM))],
            '%s e. dom ~~>' % SEQ)
    LL = 'sum_ j e. NN %s' % L.PA('S', 'j', '( j + 1 )', 'x')
    LK = 'sum_ k e. NN %s' % L.PA('S', 'k', '( k + 1 )', 'x')
    fkx = D(w, Ak, 'syl', [kn, fjm_val(w, 'k')], '( %s ` k ) = %s' % (FJ, L.PA('S', 'k', '( k + 1 )', 'x')))
    fkxc = D(w, Ak, 'eqeltrrd', [fkx, fkc], '%s e. CC' % L.PA('S', 'k', '( k + 1 )', 'x'))
    lim0 = D(w, A, 'isumclim2', [nnu, cst(w, A, '1z', '1 e. ZZ'), fkx, fkxc, cvg], '%s ~~> %s' % (SEQ, LK))
    jsub = w.s([w.s([w.s([], 'id', '( j = k -> j = k )'), w.s([], 'oveq1', '( j = k -> ( j + 1 ) = ( k + 1 ) )')], 'oveq12d', '( j = k -> ( j (,) ( j + 1 ) ) = ( k (,) ( k + 1 ) ) )'),
                w.s([], 'itgeq1', '( ( j (,) ( j + 1 ) ) = ( k (,) ( k + 1 ) ) -> %s = %s )' % (L.PA('S', 'j', '( j + 1 )', 'x'), L.PA('S', 'k', '( k + 1 )', 'x')))],
               'syl', '( j = k -> %s = %s )' % (L.PA('S', 'j', '( j + 1 )', 'x'), L.PA('S', 'k', '( k + 1 )', 'x')))
    ljk = w.s([jsub], 'cbvsumv', '%s = %s' % (LL, LK))
    lim = D(w, A, 'breqtrrd', [lim0, w.s([ljk], 'a1i', '( %s -> %s = %s )' % (A, LL, LK))], '%s ~~> %s' % (SEQ, LL))
    llc = D(w, A, 'syl', [lim, w.inst('climcl')], '%s e. CC' % LL)
    seqf = D(w, A, 'feq2d' if False else 'mpbird', [D(w, A, 'serf', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), fkc], '%s : NN --> CC' % SEQ)], '') if False else \
        D(w, A, 'serf', [nnu, cst(w, A, '1z', '1 e. ZZ'), fkc], '%s : NN --> CC' % SEQ)
    # E
    EM = '( n e. NN |-> ( 2 x. %s ) )' % L.MJ('n', R)
    m0 = D(w, A, 'serf0', [nnu, cst(w, A, '1z', '1 e. ZZ'), w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % MJM)], 'a1i', '( %s -> %s e. _V )' % (A, MJM)), msum, D(w, Ak, 'recnd', [mjkr], '( %s ` k ) e. CC' % MJM)],
           '%s ~~> 0' % MJM)
    emk = D(w, Ak, 'eqtrd', [D(w, Ak, 'syl', [kn, w.s([w.s([w.s([], 'oveq2' if False else 'idi', '') if False else None], 'dummy', '') if False else
                                                   w.s([w.s([w.s([w.s([w.s([w.s([], 'oveq2', '( n = k -> ( B x. n ) = ( B x. k ) )')], 'negeqd', '( n = k -> -u ( B x. n ) = -u ( B x. k ) )')], 'fveq2d',
                                                                             '( n = k -> ( exp ` -u ( B x. n ) ) = ( exp ` -u ( B x. k ) ) )')], 'oveq2d', '( n = k -> ( K x. ( exp ` -u ( B x. n ) ) ) = ( K x. ( exp ` -u ( B x. k ) ) ) )'),
                                                             w.s([w.s([w.s([w.s([], 'oveq1', '( n = k -> ( n + 1 ) = ( k + 1 ) )')], 'fveq2d', '( n = k -> ( log ` ( n + 1 ) ) = ( log ` ( k + 1 ) ) )')], 'oveq2d',
                                                                      '( n = k -> ( %s x. ( log ` ( n + 1 ) ) ) = ( %s x. ( log ` ( k + 1 ) ) ) )' % (R, R))], 'fveq2d',
                                                                 '( n = k -> ( exp ` ( %s x. ( log ` ( n + 1 ) ) ) ) = ( exp ` ( %s x. ( log ` ( k + 1 ) ) ) ) )' % (R, R))], 'oveq12d',
                                                            '( n = k -> %s = %s )' % (L.MJ('n', R), L.MJ('k', R)))], 'oveq2d', '( n = k -> ( 2 x. %s ) = ( 2 x. %s ) )' % (L.MJ('n', R), L.MJ('k', R))),
                                                   w.s([], 'eqid', '%s = %s' % (EM, EM)), w.s([], 'ovex', '( 2 x. %s ) e. _V' % L.MJ('k', R))], 'fvmpt',
                                                  '( k e. NN -> ( %s ` k ) = ( 2 x. %s ) )' % (EM, L.MJ('k', R)))], '( %s ` k ) = ( 2 x. %s )' % (EM, L.MJ('k', R))),
                             D(w, Ak, 'oveq2d', [D(w, Ak, 'eqcomd', [mjk], '%s = ( %s ` k )' % (L.MJ('k', R), MJM))], '( 2 x. %s ) = ( 2 x. ( %s ` k ) )' % (L.MJ('k', R), MJM))],
           '( %s ` k ) = ( 2 x. ( %s ` k ) )' % (EM, MJM))
    e0 = D(w, A, 'climmulc2', [nnu, cst(w, A, '1z', '1 e. ZZ'), m0, cst(w, A, '2cn', '2 e. CC'), w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % EM)], 'a1i', '( %s -> %s e. _V )' % (A, EM)),
                                D(w, Ak, 'recnd', [mjkr], '( %s ` k ) e. CC' % MJM), emk],
           '%s ~~> ( 2 x. 0 )' % EM)
    e00 = D(w, A, 'breqtrd', [e0, cst(w, A, '2t0e0', '( 2 x. 0 ) = 0')], '%s ~~> 0' % EM)
    emr = D(w, Ak, 'eqeltrd', [emk, D(w, Ak, 'remulcld', [cst(w, Ak, '2re', '2 e. RR'), mjkr], '( 2 x. ( %s ` k ) ) e. RR' % MJM)], '( %s ` k ) e. RR' % EM)
    An = '( %s /\\ n e. NN )' % A
    emf = D(w, A, 'fmptd', [D(w, An, 'remulcld', [cst(w, An, '2re', '2 e. RR'), mj_re(An, 'n', w.s([], 'simpr', '( %s -> n e. NN )' % An))], '( 2 x. %s ) e. RR' % L.MJ('n', R)),
                            w.s([], 'eqid', '%s = %s' % (EM, EM))], '%s : NN --> RR' % EM)
    IY = lambda a, b: L.PA('S', a, b)
    FU = '( u e. RR+ |-> %s )' % IY('1', 'u')
    Au_ = '( %s /\\ u e. RR+ )' % A
    ur_ = D(w, Au_, 'rpred', [w.s([], 'simpr', '( %s -> u e. RR+ )' % Au_)], 'u e. RR')
    one_ = cst(w, Au_, '1re', '1 e. RR')
    fuc = D(w, Au_, 'itgcl', [ibl_pa(w, Au_, ad(w, Au_, phv, L.PHV), one_, D(w, Au_, 'leidd', [one_], '1 <_ 1'), ur_, 'S', ad(w, Au_, sc, 'S e. CC'), '1', 'u'),
                              integrand_cl(w, Au_, ad(w, Au_, phv, L.PHV), one_, D(w, Au_, 'leidd', [one_], '1 <_ 1'), ur_, 'S', ad(w, Au_, sc, 'S e. CC'), P='1', Q='u')], '%s e. CC' % IY('1', 'u'))
    fuf = D(w, A, 'fmptd', [fuc, w.s([], 'eqid', '%s = %s' % (FU, FU))], '%s : RR+ --> CC' % FU)
    At = '( %s /\\ t e. %s )' % (A, I1)
    tr, t1 = ge1(w, At, w.s([], 'simpr', '( %s -> t e. %s )' % (At, I1)), 't')
    trp = rp_of(w, At, tr, t1, 't')
    N = '( |_ ` t )'; N1 = '( %s + 1 )' % N
    nn_ = D(w, At, 'syl2anc', [tr, t1, w.inst('flge1nn')], '%s e. NN' % N)
    nr = D(w, At, 'nnred', [nn_], '%s e. RR' % N); n1r = D(w, At, 'syl', [nr, w.inst('peano2re')], '%s e. RR' % N1)
    nt = D(w, At, 'syl', [tr, w.inst('flle')], '%s <_ t' % N)
    tn1 = D(w, At, 'ltled', [tr, n1r, D(w, At, 'syl', [tr, w.inst('flltp1')], 't < %s' % N1)], 't <_ %s' % N1)
    n1 = D(w, At, 'nnge1d', [nn_], '1 <_ %s' % N)
    phA, scA = ad(w, At, phv, L.PHV), ad(w, At, sc, 'S e. CC')
    oneA = cst(w, At, '1re', '1 e. RR'); l11 = D(w, At, 'leidd', [oneA], '1 <_ 1')
    def ib(P, pr, p1, Q, qr):
        return ibl_pa(w, At, phA, pr, p1, qr, 'S', scA, P, Q)
    def cl_(P, pr, p1, Q, qr):
        return integrand_cl(w, At, phA, pr, p1, qr, 'S', scA, P=P, Q=Q)
    def icc(B, br, lo, lor, hi, hir, l1, l2):
        return D(w, At, 'mpbir3and', [br, l1, l2, D(w, At, 'syl2anc', [lor, hir, w.inst('elicc2')], '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (B, lo, hi, B, lo, B, B, hi))],
                 '%s e. ( %s [,] %s )' % (B, lo, hi))
    sp1 = D(w, At, 'itgsplitioo', [oneA, n1r, icc('t', tr, '1', oneA, N1, n1r, t1, tn1), cl_('1', oneA, l11, N1, n1r), ib('1', oneA, l11, 't', tr), ib('t', tr, t1, N1, n1r)],
            '%s = ( %s + %s )' % (IY('1', N1), IY('1', 't'), IY('t', N1)))
    sp2 = D(w, At, 'itgsplitioo', [nr, n1r, icc('t', tr, N, nr, N1, n1r, nt, tn1), cl_(N, nr, n1, N1, n1r), ib(N, nr, n1, 't', tr), ib('t', tr, t1, N1, n1r)],
            '%s = ( %s + %s )' % (IY(N, N1), IY(N, 't'), IY('t', N1)))
    def icl(P, pr, p1, Q, qr):
        return D(w, At, 'itgcl', [ib(P, pr, p1, Q, qr), cl_(P, pr, p1, Q, qr)], '%s e. CC' % IY(P, Q))
    ac, bc, cc_, dc = icl('1', oneA, l11, 't', tr), icl('t', tr, t1, N1, n1r), icl(N, nr, n1, 't', tr), icl(N, nr, n1, N1, n1r)
    ec = icl('1', oneA, l11, N1, n1r)
    a_, b_, c_, d_, e_ = IY('1', 't'), IY('t', N1), IY(N, 't'), IY(N, N1), IY('1', N1)
    fut = D(w, At, 'syl', [trp, w.s([w.s([w.s([], 'oveq2', '( u = t -> ( 1 (,) u ) = ( 1 (,) t ) )'), w.s([], 'itgeq1', '( ( 1 (,) u ) = ( 1 (,) t ) -> %s = %s )' % (IY('1', 'u'), a_))], 'syl',
                                             '( u = t -> %s = %s )' % (IY('1', 'u'), a_)), w.s([], 'eqid', '%s = %s' % (FU, FU)), w.s([], 'itgex', '%s e. _V' % a_)], 'fvmpt',
                                        '( t e. RR+ -> ( %s ` t ) = %s )' % (FU, a_))], '( %s ` t ) = %s' % (FU, a_))
    sqn = D(w, At, 'syl3anc', [phA, scA, nn_, w.inst('zl3pcs')], '( %s ` %s ) = %s' % (SEQ, N, e_))
    X1 = '( ( %s ` t ) - ( %s ` %s ) )' % (FU, SEQ, N)
    x1 = D(w, At, 'oveq12d', [fut, sqn], '%s = ( %s - %s )' % (X1, a_, e_))
    ab1 = D(w, At, 'abssubd', [ac, ec], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (a_, e_, e_, a_))
    eb = D(w, At, 'eqtrd', [D(w, At, 'oveq1d', [sp1], '( %s - %s ) = ( ( %s + %s ) - %s )' % (e_, a_, a_, b_, a_)), D(w, At, 'pncan2d', [ac, bc], '( ( %s + %s ) - %s ) = %s' % (a_, b_, a_, b_))],
           '( %s - %s ) = %s' % (e_, a_, b_))
    db = D(w, At, 'eqtrd', [D(w, At, 'oveq1d', [sp2], '( %s - %s ) = ( ( %s + %s ) - %s )' % (d_, c_, c_, b_, c_)), D(w, At, 'pncan2d', [cc_, bc], '( ( %s + %s ) - %s ) = %s' % (c_, b_, c_, b_))],
           '( %s - %s ) = %s' % (d_, c_, b_))
    absX = chain(w, At, ['( abs ` %s )' % X1, '( abs ` ( %s - %s ) )' % (a_, e_), '( abs ` ( %s - %s ) )' % (e_, a_), '( abs ` %s )' % b_, '( abs ` ( %s - %s ) )' % (d_, c_)],
                 [D(w, At, 'fveq2d', [x1], '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (X1, a_, e_)), ab1, D(w, At, 'fveq2d', [eb], '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (e_, a_, b_)),
                  ('r', D(w, At, 'fveq2d', [db], '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (d_, c_, b_)))])
    tri = D(w, At, 'abs2dif2d', [dc, cc_], '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (d_, c_, d_, c_))
    def pbd(T, tI):
        return D(w, At, 'simpld', [D(w, At, 'syl3anc', [phA, D(w, At, '3jca', [ad(w, At, rr, '%s e. RR' % R), scA, ad(w, At, rle, '%s <_ %s' % (R, R))], '( %s e. RR /\\ S e. CC /\\ %s <_ %s )' % (R, R, R)),
                                                          D(w, At, 'jca', [nn_, tI], '( %s e. NN /\\ %s e. ( %s [,] %s ) )' % (N, T, N, N1)), w.inst('zl3pbd')],
                                                  '( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s )' % (IY(N, T), L.MJ(N, R), L.PV('S', N, T), L.MJ(N, R)))], '( abs ` %s ) <_ %s' % (IY(N, T), L.MJ(N, R)))
    bd = pbd(N1, icc(N1, n1r, N, nr, N1, n1r, linarith(w, At, [], '%s <_ %s' % (N, N1), leaves={N: nr}), D(w, At, 'leidd', [n1r], '%s <_ %s' % (N1, N1))))
    bc2 = pbd('t', icc('t', tr, N, nr, N1, n1r, nt, tn1))
    mjn = mj_re(At, N, nn_)
    sum_ = D(w, At, 'le2addd', [D(w, At, 'abscld', [dc], '( abs ` %s ) e. RR' % d_), mjn, D(w, At, 'abscld', [cc_], '( abs ` %s ) e. RR' % c_), mjn, bd, bc2],
             '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s + %s )' % (d_, c_, L.MJ(N, R), L.MJ(N, R)))
    emn = D(w, At, 'syl', [nn_, w.s([w.s([w.s([w.s([w.s([w.s([w.s([], 'oveq2', '( n = %s -> ( B x. n ) = ( B x. %s ) )' % (N, N))], 'negeqd', '( n = %s -> -u ( B x. n ) = -u ( B x. %s ) )' % (N, N))], 'fveq2d',
                                                                  '( n = %s -> ( exp ` -u ( B x. n ) ) = ( exp ` -u ( B x. %s ) ) )' % (N, N))], 'oveq2d', '( n = %s -> ( K x. ( exp ` -u ( B x. n ) ) ) = ( K x. ( exp ` -u ( B x. %s ) ) ) )' % (N, N)),
                                                  w.s([w.s([w.s([w.s([], 'oveq1', '( n = %s -> ( n + 1 ) = %s )' % (N, N1))], 'fveq2d', '( n = %s -> ( log ` ( n + 1 ) ) = ( log ` %s ) )' % (N, N1))], 'oveq2d',
                                                           '( n = %s -> ( %s x. ( log ` ( n + 1 ) ) ) = ( %s x. ( log ` %s ) ) )' % (N, R, R, N1))], 'fveq2d',
                                                      '( n = %s -> ( exp ` ( %s x. ( log ` ( n + 1 ) ) ) ) = ( exp ` ( %s x. ( log ` %s ) ) ) )' % (N, R, R, N1))], 'oveq12d',
                                                 '( n = %s -> %s = %s )' % (N, L.MJ('n', R), L.MJ(N, R)))], 'oveq2d', '( n = %s -> ( 2 x. %s ) = ( 2 x. %s ) )' % (N, L.MJ('n', R), L.MJ(N, R))),
                                        w.s([], 'eqid', '%s = %s' % (EM, EM)), w.s([], 'ovex', '( 2 x. %s ) e. _V' % L.MJ(N, R))], 'fvmpt', '( %s e. NN -> ( %s ` %s ) = ( 2 x. %s ) )' % (N, EM, N, L.MJ(N, R)))],
              '( %s ` %s ) = ( 2 x. %s )' % (EM, N, L.MJ(N, R)))
    two = D(w, At, 'eqtrd', [emn, D(w, At, '2timesd', [D(w, At, 'recnd', [mjn], '%s e. CC' % L.MJ(N, R))], '( 2 x. %s ) = ( %s + %s )' % (L.MJ(N, R), L.MJ(N, R), L.MJ(N, R)))],
              '( %s ` %s ) = ( %s + %s )' % (EM, N, L.MJ(N, R), L.MJ(N, R)))
    pt = D(w, At, 'breqtrrd', [D(w, At, 'letrd', [D(w, At, 'abscld', [D(w, At, 'subcld', [dc, cc_], '( %s - %s ) e. CC' % (d_, c_))], '( abs ` ( %s - %s ) ) e. RR' % (d_, c_)),
                                                   D(w, At, 'readdcld', [D(w, At, 'abscld', [dc], '( abs ` %s ) e. RR' % d_), D(w, At, 'abscld', [cc_], '( abs ` %s ) e. RR' % c_)], '( ( abs ` %s ) + ( abs ` %s ) ) e. RR' % (d_, c_)),
                                                   D(w, At, 'readdcld', [mjn, mjn], '( %s + %s ) e. RR' % (L.MJ(N, R), L.MJ(N, R))), tri, sum_],
                                     '( abs ` ( %s - %s ) ) <_ ( %s + %s )' % (d_, c_, L.MJ(N, R), L.MJ(N, R))), two], '( abs ` ( %s - %s ) ) <_ ( %s ` %s )' % (d_, c_, EM, N))
    ptt = D(w, At, 'eqbrtrd', [absX, pt], '( abs ` %s ) <_ ( %s ` %s )' % (X1, EM, N))
    HT = 'A. t e. %s ( abs ` %s ) <_ ( %s ` %s )' % (I1, X1, EM, N)
    ht = D(w, A, 'ralrimiva', [ptt], HT)
    flr = D(w, A, 'syl3anc', [D(w, A, 'jca', [fuf, llc], '( %s : RR+ --> CC /\\ %s e. CC )' % (FU, LL)), D(w, A, 'jca', [seqf, lim], '( %s : NN --> CC /\\ %s ~~> %s )' % (SEQ, SEQ, LL)),
                              D(w, A, '3jca', [emf, e00, ht], '( %s : NN --> RR /\\ %s ~~> 0 /\\ %s )' % (EM, EM, HT)), w.inst('zl3flr')], '%s ~~>r %s' % (FU, LL))
    cb = w.s([w.s([w.s([], 'oveq2', '( t = u -> ( 1 (,) t ) = ( 1 (,) u ) )'), w.s([], 'itgeq1', '( ( 1 (,) t ) = ( 1 (,) u ) -> %s = %s )' % (a_, IY('1', 'u')))], 'syl', '( t = u -> %s = %s )' % (a_, IY('1', 'u')))],
             'cbvmptv', '%s = %s' % (L.IMP('S'), FU))
    w.qed([w.s([cb], 'a1i', '( %s -> %s = %s )' % (A, L.IMP('S'), FU)), flr], 'eqbrtrd', S['zl3pcv'])
    go(w)


def val_of(w, A_, F, Lv, conv, ff):
    """( A_ -> ( ~~>r ` F ) = Lv ) from conv: ( A_ -> F ~~>r Lv ), ff: ( A_ -> F : RR+ --> CC )  (as tools/gen/zl3b_e5.py)"""
    dm = w.s([conv, w.s([w.s([], 'rlimrel', 'Rel ~~>r')], 'releldmi', '( %s ~~>r %s -> %s e. dom ~~>r )' % (F, Lv, F))], 'syl', '( %s -> %s e. dom ~~>r )' % (A_, F))
    sup = cst(w, A_, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')
    rv = D(w, A_, 'mpbid', [dm, w.s([ff, sup], 'rlimdm', '( %s -> ( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) ) )' % (A_, F, F, F))], '%s ~~>r ( ~~>r ` %s )' % (F, F))
    return w.s([ff, sup, rv, conv], 'rlimuni', '( %s -> ( ~~>r ` %s ) = %s )' % (A_, F, Lv))


def imp_f(w, A2, phv, sc, s):
    """( A2 -> IMP(s) : RR+ --> CC )"""
    At = '( %s /\\ t e. RR+ )' % A2
    tr = D(w, At, 'rpred', [w.s([], 'simpr', '( %s -> t e. RR+ )' % At)], 't e. RR')
    one = cst(w, At, '1re', '1 e. RR'); l11 = D(w, At, 'leidd', [one], '1 <_ 1')
    ph_, sc_ = ad(w, At, phv, L.PHV), ad(w, At, sc, '%s e. CC' % s)
    c = D(w, At, 'itgcl', [ibl_pa(w, At, ph_, one, l11, tr, s, sc_, '1', 't'), integrand_cl(w, At, ph_, one, l11, tr, s, sc_, P='1', Q='t')], '%s e. CC' % L.PA(s, '1', 't'))
    return D(w, A2, 'fmptd', [c, w.s([], 'eqid', '%s = %s' % (L.IMP(s), L.IMP(s)))], '%s : RR+ --> CC' % L.IMP(s))


def mj_sub(w, n, K, R):
    """closed: ( n = K -> MJ(n,R) = MJ(K,R) )"""
    a = w.s([w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( B x. %s ) = ( B x. %s ) )' % (n, K, n, K))], 'negeqd', '( %s = %s -> -u ( B x. %s ) = -u ( B x. %s ) )' % (n, K, n, K))], 'fveq2d',
                  '( %s = %s -> ( exp ` -u ( B x. %s ) ) = ( exp ` -u ( B x. %s ) ) )' % (n, K, n, K))], 'oveq2d',
            '( %s = %s -> ( K x. ( exp ` -u ( B x. %s ) ) ) = ( K x. ( exp ` -u ( B x. %s ) ) ) )' % (n, K, n, K))
    b = w.s([w.s([w.s([w.s([], 'oveq1', '( %s = %s -> ( %s + 1 ) = ( %s + 1 ) )' % (n, K, n, K))], 'fveq2d', '( %s = %s -> ( log ` ( %s + 1 ) ) = ( log ` ( %s + 1 ) ) )' % (n, K, n, K))], 'oveq2d',
                  '( %s = %s -> ( %s x. ( log ` ( %s + 1 ) ) ) = ( %s x. ( log ` ( %s + 1 ) ) ) )' % (n, K, R, n, R, K))], 'fveq2d',
            '( %s = %s -> ( exp ` ( %s x. ( log ` ( %s + 1 ) ) ) ) = ( exp ` ( %s x. ( log ` ( %s + 1 ) ) ) ) )' % (n, K, R, n, R, K))
    return w.s([a, b], 'oveq12d', '( %s = %s -> %s = %s )' % (n, K, L.MJ(n, R), L.MJ(K, R)))


# ---------------------------------------------------------------- zl3pih
if want('zl3pih'):
    w = W('zl3pih', 'The improper parameter integral ` s |-> lim_t S. ( 1 (,) t ) G ( y ) y ^c s _d y ` of a continuous ` G ` with exponential decay is entire ( ~ uhhol on vertical strips, ~ holloc ).')
    PH, C = L.split_imp(S['zl3pih'])
    A0 = L.PHV
    J = '( TopOpen ` CCfld )'
    FIL = '( s e. CC |-> ( ~~>r ` %s ) )' % L.IMP('s')
    Az = '( %s /\\ z e. CC )' % A0
    zc = w.s([], 'simpr', '( %s -> z e. CC )' % Az)
    phz = w.s([], 'simpl', '( %s -> %s )' % (Az, A0))
    RZ, ARZ = '( Re ` z )', '( abs ` ( Re ` z ) )'
    R = '( %s + 1 )' % ARZ; R1 = '( %s + 1 )' % R
    U = "( `' Re \" ( -u %s (,) %s ) )" % (R, R)
    rzr = D(w, Az, 'recld', [zc], '%s e. RR' % RZ)
    arz = D(w, Az, 'abscld', [D(w, Az, 'recnd', [rzr], '%s e. CC' % RZ)], '%s e. RR' % ARZ)
    rr = D(w, Az, 'readdcld', [arz, cst(w, Az, '1re', '1 e. RR')], '%s e. RR' % R)
    r1r = D(w, Az, 'readdcld', [rr, cst(w, Az, '1re', '1 e. RR')], '%s e. RR' % R1)
    uop = cst(w, Az, 'z6mstopn', '%s e. %s' % (U, J))
    refn = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Re Fn CC')
    def inU(A2, pt, ptc, lt):
        """( A2 -> pt e. U ) from ptc: pt e. CC, lt: ( abs ` ( Re ` pt ) ) < R"""
        rp_ = D(w, A2, 'recld', [ptc], '( Re ` %s ) e. RR' % pt)
        ab = D(w, A2, 'mpbid', [lt, D(w, A2, 'syl2anc', [rp_, ad(w, A2, rr, '%s e. RR' % R) if A2 != Az else rr, w.inst('abslt')],
                                        '( ( abs ` ( Re ` %s ) ) < %s <-> ( -u %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s ) )' % (pt, R, R, pt, pt, R))],
               '( -u %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s )' % (R, pt, pt, R))
        rrA = ad(w, A2, rr, '%s e. RR' % R) if A2 != Az else rr
        io = D(w, A2, 'mpbir3and', [rp_, D(w, A2, 'simpld', [ab], '-u %s < ( Re ` %s )' % (R, pt)), D(w, A2, 'simprd', [ab], '( Re ` %s ) < %s' % (pt, R)),
                                    D(w, A2, 'syl2anc', [D(w, A2, 'rexrd', [D(w, A2, 'renegcld', [rrA], '-u %s e. RR' % R)], '-u %s e. RR*' % R), D(w, A2, 'rexrd', [rrA], '%s e. RR*' % R), w.inst('elioo2')],
                                      '( ( Re ` %s ) e. ( -u %s (,) %s ) <-> ( ( Re ` %s ) e. RR /\\ -u %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s ) )' % (pt, R, R, pt, R, pt, pt, R))],
               '( Re ` %s ) e. ( -u %s (,) %s )' % (pt, R, R))
        return D(w, A2, 'mpbir2and', [ptc, io, w.s([w.s([refn, w.inst('elpreima')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( -u %s (,) %s ) ) )' % (pt, U, pt, pt, R, R))], 'a1i',
                                                    '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( -u %s (,) %s ) ) ) )' % (A2, pt, U, pt, pt, R, R))], '%s e. %s' % (pt, U))
    zU = inU(Az, 'z', zc, linarith(w, Az, [], '%s < %s' % (ARZ, R), leaves={ARZ: arz}))
    dmre = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('fdm')], 'ax-mp', 'dom Re = CC')
    ucc0 = w.s([w.s([], 'cnvimass', '%s C_ dom Re' % U), dmre], 'sseqtri', '%s C_ CC' % U)
    ucc = w.s([ucc0], 'a1i', '( %s -> %s C_ CC )' % (Az, U))
    uex = w.s([w.s([], 'cnex', 'CC e. _V'), ucc0], 'ssexi', '%s e. _V' % U)
    def fromU(A2, a, aU):
        """a e. U -> a e. CC and ( abs ` ( Re ` a ) ) < R"""
        bi = w.s([w.s([refn, w.inst('elpreima')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( -u %s (,) %s ) ) )' % (a, U, a, a, R, R))], 'a1i',
                 '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( -u %s (,) %s ) ) ) )' % (A2, a, U, a, a, R, R))
        both = D(w, A2, 'mpbid', [aU, bi], '( %s e. CC /\\ ( Re ` %s ) e. ( -u %s (,) %s ) )' % (a, a, R, R))
        ac = D(w, A2, 'simpld', [both], '%s e. CC' % a)
        rrA = ad(w, A2, rr, '%s e. RR' % R)
        tr = D(w, A2, 'mpbid', [D(w, A2, 'simprd', [both], '( Re ` %s ) e. ( -u %s (,) %s )' % (a, R, R)),
                                 D(w, A2, 'syl2anc', [D(w, A2, 'rexrd', [D(w, A2, 'renegcld', [rrA], '-u %s e. RR' % R)], '-u %s e. RR*' % R), D(w, A2, 'rexrd', [rrA], '%s e. RR*' % R), w.inst('elioo2')],
                                   '( ( Re ` %s ) e. ( -u %s (,) %s ) <-> ( ( Re ` %s ) e. RR /\\ -u %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s ) )' % (a, R, R, a, R, a, a, R))],
                '( ( Re ` %s ) e. RR /\\ -u %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s )' % (a, R, a, a, R))
        lt = D(w, A2, 'mpbird', [D(w, A2, '3simpc' if False else 'jca', [D(w, A2, 'simp2d', [tr], '-u %s < ( Re ` %s )' % (R, a)), D(w, A2, 'simp3d', [tr], '( Re ` %s ) < %s' % (a, R))],
                                   '( -u %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s )' % (R, a, a, R)),
                                 D(w, A2, 'syl2anc', [D(w, A2, 'simp1d', [tr], '( Re ` %s ) e. RR' % a), rrA, w.inst('abslt')],
                                   '( ( abs ` ( Re ` %s ) ) < %s <-> ( -u %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s ) )' % (a, R, R, a, a, R))], '( abs ` ( Re ` %s ) ) < %s' % (a, R))
        return ac, lt
    # the pieces
    FJx = lambda wv, m: L.PA(wv, m, '( %s + 1 )' % m, 'x')
    Fm = '( m e. NN |-> ( w e. %s |-> %s ) )' % (U, FJx('w', 'm'))
    Fj = '( w e. %s |-> %s )' % (U, FJx('w', 'j'))
    Aj = '( %s /\\ j e. NN )' % Az
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    msub = w.s([w.s([w.s([w.s([], 'id', '( m = j -> m = j )'), w.s([], 'oveq1', '( m = j -> ( m + 1 ) = ( j + 1 ) )')], 'oveq12d', '( m = j -> ( m (,) ( m + 1 ) ) = ( j (,) ( j + 1 ) ) )'),
                     w.s([], 'itgeq1', '( ( m (,) ( m + 1 ) ) = ( j (,) ( j + 1 ) ) -> %s = %s )' % (FJx('w', 'm'), FJx('w', 'j')))], 'syl', '( m = j -> %s = %s )' % (FJx('w', 'm'), FJx('w', 'j')))],
               'mpteq2dv', '( m = j -> ( w e. %s |-> %s ) = %s )' % (U, FJx('w', 'm'), Fj))
    fjv = D(w, Aj, 'syl', [jn, w.s([msub, w.s([], 'eqid', '%s = %s' % (Fm, Fm)), w.s([uex], 'mptex', '%s e. _V' % Fj)], 'fvmpt', '( j e. NN -> ( %s ` j ) = %s )' % (Fm, Fj))], '( %s ` j ) = %s' % (Fm, Fj))
    jr = D(w, Aj, 'nnred', [jn], 'j e. RR'); j1 = D(w, Aj, 'nnge1d', [jn], '1 <_ j'); j1r = D(w, Aj, 'syl', [jr, w.inst('peano2re')], '( j + 1 ) e. RR')
    phj = ad(w, Aj, phz, A0)
    pdv = D(w, Aj, 'syl3anc', [phj, D(w, Aj, 'jca', [D(w, Aj, 'jca', [jr, j1], '( j e. RR /\\ 1 <_ j )'), D(w, Aj, 'jca', [j1r, linarith(w, Aj, [], 'j <_ ( j + 1 )', leaves={'j': jr})], '( ( j + 1 ) e. RR /\\ j <_ ( j + 1 ) )')],
                                                 '( ( j e. RR /\\ 1 <_ j ) /\\ ( ( j + 1 ) e. RR /\\ j <_ ( j + 1 ) ) )'), ad(w, Aj, uop, '%s e. %s' % (U, J)), w.inst('zl3pdv')],
            '( ( ( s e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D ( s e. %s |-> %s ) ) ) /\\ ( CC _D ( s e. %s |-> %s ) ) = ( s e. %s |-> %s ) )'
            % (U, L.PA('s', 'j', '( j + 1 )'), U, U, U, L.PA('s', 'j', '( j + 1 )'), U, L.PA('s', 'j', '( j + 1 )'), U, L.PV('s', 'j', '( j + 1 )')))
    MY = '( s e. %s |-> %s )' % (U, L.PA('s', 'j', '( j + 1 )'))
    swy = w.s([pa_sub(w, 's', 'w', 'j', '( j + 1 )'), cbv_xy(w, 'j', '( j + 1 )', 'w') if False else w.s([cbv_xy(w, 'j', '( j + 1 )', 'w')], 'eqcomi', '%s = %s' % (L.PA('w', 'j', '( j + 1 )'), FJx('w', 'j')))],
              'eqtrdi', '( s = w -> %s = %s )' % (L.PA('s', 'j', '( j + 1 )'), FJx('w', 'j')))
    myeq = w.s([swy], 'cbvmptv', '%s = %s' % (MY, Fj))
    feq = D(w, Aj, 'eqtr4d', [fjv, w.s([myeq], 'a1i', '( %s -> %s = %s )' % (Aj, MY, Fj))], '( %s ` j ) = %s' % (Fm, MY))
    holy = D(w, Aj, 'simpld', [pdv], '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (MY, U, U, MY))
    dvy = D(w, Aj, 'simprd', [pdv], '( CC _D %s ) = ( s e. %s |-> %s )' % (MY, U, L.PV('s', 'j', '( j + 1 )')))
    FJ_ = '( %s ` j )' % Fm
    hj1 = D(w, Aj, 'eqeltrd', [feq, D(w, Aj, 'simpld', [holy], '%s e. ( %s -cn-> CC )' % (MY, U))], '%s e. ( %s -cn-> CC )' % (FJ_, U))
    dfe = D(w, Aj, 'oveq2d', [feq], '( CC _D %s ) = ( CC _D %s )' % (FJ_, MY))
    hj2 = D(w, Aj, 'sseqtrrd', [D(w, Aj, 'simprd', [holy], '%s C_ dom ( CC _D %s )' % (U, MY)), D(w, Aj, 'dmeqd', [dfe], 'dom ( CC _D %s ) = dom ( CC _D %s )' % (FJ_, MY))],
             '%s C_ dom ( CC _D %s )' % (U, FJ_))
    holj = D(w, Aj, 'jca', [hj1, hj2], '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (FJ_, U, U, FJ_))
    dvj = D(w, Aj, 'eqtrd', [dfe, dvy], '( CC _D %s ) = ( s e. %s |-> %s )' % (FJ_, U, L.PV('s', 'j', '( j + 1 )')))
    def pax_sub(s1, s2, m):
        """closed: ( s1 = s2 -> FJx(s1,m) = FJx(s2,m) )"""
        X = '( %s (,) ( %s + 1 ) )' % (m, m)
        a = w.s([w.s([], 'oveq2', '( %s = %s -> ( x ^c %s ) = ( x ^c %s ) )' % (s1, s2, s1, s2))], 'oveq2d', '( %s = %s -> ( ( G ` x ) x. ( x ^c %s ) ) = ( ( G ` x ) x. ( x ^c %s ) ) )' % (s1, s2, s1, s2))
        b = w.s([a], 'adantr', '( ( %s = %s /\\ x e. %s ) -> ( ( G ` x ) x. ( x ^c %s ) ) = ( ( G ` x ) x. ( x ^c %s ) ) )' % (s1, s2, X, s1, s2))
        return w.s([b], 'itgeq2dv', '( %s = %s -> %s = %s )' % (s1, s2, FJx(s1, m), FJx(s2, m)))
    def mjre(A2, n, nn):
        f_ = phv_facts(w, A2, w.s([phz], 'adantr', '( %s -> %s )' % (A2, A0)) if A2.startswith('( %s /\\ ' % Az) else None)
        nr = D(w, A2, 'nnred', [nn], '%s e. RR' % n)
        n1 = D(w, A2, 'syl', [nr, w.inst('peano2re')], '( %s + 1 ) e. RR' % n)
        n1p = rp_of(w, A2, n1, linarith(w, A2, [D(w, A2, 'nnge1d', [nn], '1 <_ %s' % n)], '1 <_ ( %s + 1 )' % n, leaves={n: nr}), '( %s + 1 )' % n)
        a = D(w, A2, 'remulcld', [D(w, A2, 'rpred', [f_['k']], 'K e. RR'), D(w, A2, 'reefcld', [D(w, A2, 'renegcld', [D(w, A2, 'remulcld', [D(w, A2, 'rpred', [f_['b']], 'B e. RR'), nr], '( B x. %s ) e. RR' % n)], '-u ( B x. %s ) e. RR' % n)],
                                                                                        '( exp ` -u ( B x. %s ) ) e. RR' % n)], '( K x. ( exp ` -u ( B x. %s ) ) ) e. RR' % n)
        b = D(w, A2, 'reefcld', [D(w, A2, 'remulcld', [ad(w, A2, r1r, '%s e. RR' % R1), D(w, A2, 'relogcld', [n1p], '( log ` ( %s + 1 ) ) e. RR' % n)], '( %s x. ( log ` ( %s + 1 ) ) ) e. RR' % (R1, n))],
                  '( exp ` ( %s x. ( log ` ( %s + 1 ) ) ) ) e. RR' % (R1, n))
        return D(w, A2, 'remulcld', [a, b], '%s e. RR' % L.MJ(n, R1))
    # F : NN --> ( CC ^m U )
    Am = '( %s /\\ m e. NN )' % Az
    Amw = '( %s /\\ w e. %s )' % (Am, U)
    mn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
    mr = D(w, Am, 'nnred', [mn], 'm e. RR'); m1r = D(w, Am, 'syl', [mr, w.inst('peano2re')], '( m + 1 ) e. RR'); m1 = D(w, Am, 'nnge1d', [mn], '1 <_ m')
    wc, _ = fromU(Amw, 'w', w.s([], 'simpr', '( %s -> w e. %s )' % (Amw, U)))
    phw = w.s([phz], 'ad2antrr', '( %s -> %s )' % (Amw, A0))
    cy = D(w, Amw, 'itgcl', [ibl_pa(w, Amw, phw, ad(w, Amw, mr, 'm e. RR'), ad(w, Amw, m1, '1 <_ m'), ad(w, Amw, m1r, '( m + 1 ) e. RR'), 'w', wc, 'm', '( m + 1 )'),
                             integrand_cl(w, Amw, phw, ad(w, Amw, mr, 'm e. RR'), ad(w, Amw, m1, '1 <_ m'), ad(w, Amw, m1r, '( m + 1 ) e. RR'), 'w', wc, P='m', Q='( m + 1 )')], '%s e. CC' % L.PA('w', 'm', '( m + 1 )'))
    cx = D(w, Amw, 'eqeltrd', [w.s([cbv_xy(w, 'm', '( m + 1 )', 'w')], 'a1i', '( %s -> %s = %s )' % (Amw, FJx('w', 'm'), L.PA('w', 'm', '( m + 1 )'))), cy], '%s e. CC' % FJx('w', 'm'))
    FWm = '( w e. %s |-> %s )' % (U, FJx('w', 'm'))
    fwf = D(w, Am, 'fmptd', [cx, w.s([], 'eqid', '%s = %s' % (FWm, FWm))], '%s : %s --> CC' % (FWm, U))
    fwm = D(w, Am, 'mpbird', [fwf, w.s([w.s([w.s([], 'cnex', 'CC e. _V'), uex], 'pm3.2i', '( CC e. _V /\\ %s e. _V )' % U), w.inst('elmapg')], 'ax-mp',
                                       '( %s e. ( CC ^m %s ) <-> %s : %s --> CC )' % (FWm, U, FWm, U)) if False else
                                  cst(w, Am, 'idi', '') if False else
                                  w.s([w.s([w.s([w.s([], 'cnex', 'CC e. _V'), uex], 'pm3.2i', '( CC e. _V /\\ %s e. _V )' % U), w.inst('elmapg')], 'ax-mp',
                                           '( %s e. ( CC ^m %s ) <-> %s : %s --> CC )' % (FWm, U, FWm, U))], 'a1i', '( %s -> ( %s e. ( CC ^m %s ) <-> %s : %s --> CC ) )' % (Am, FWm, U, FWm, U))],
              '%s e. ( CC ^m %s )' % (FWm, U))
    ff = D(w, Az, 'fmptd', [fwm, w.s([], 'eqid', '%s = %s' % (Fm, Fm))], '%s : NN --> ( CC ^m %s )' % (Fm, U))
    hol_all = D(w, Az, 'ralrimiva', [holj], 'A. j e. NN ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (FJ_, U, U, FJ_))
    # M
    MM_ = '( n e. NN |-> %s )' % L.MJ('n', R1)
    An = '( %s /\\ n e. NN )' % Az
    mf = D(w, Az, 'fmptd', [mjre(An, 'n', w.s([], 'simpr', '( %s -> n e. NN )' % An)), w.s([], 'eqid', '%s = %s' % (MM_, MM_))], '%s : NN --> RR' % MM_)
    f0 = phv_facts(w, Az, phz)
    ms = D(w, Az, 'syl3anc', [f0['k'], f0['b'], r1r, w.inst('zl3msum')], 'seq 1 ( + , %s ) e. dom ~~>' % MM_)
    # bounds at ( j , a )
    Aja = '( %s /\\ ( j e. NN /\\ a e. %s ) )' % (Az, U)
    jn2 = w.s([], 'simprl', '( %s -> j e. NN )' % Aja); aU = w.s([], 'simprr', '( %s -> a e. %s )' % (Aja, U))
    Aj2 = lambda st, f: D(w, Aja, 'syl2anc' if False else 'sylan2', [], f) if False else None
    toAj = lambda st, f: w.s([w.s([], 'simpl', '( %s -> %s )' % (Aja, Az)), jn2, w.s([st], 'ex', '( %s -> ( j e. NN -> %s ) )' % (Az, f))], 'sylc', '( %s -> %s )' % (Aja, f))
    ac_, alt = fromU(Aja, 'a', aU)
    fja = D(w, Aja, 'eqtrd', [D(w, Aja, 'fveq1d', [toAj(fjv, '( %s ` j ) = %s' % (Fm, Fj))], '( ( %s ` j ) ` a ) = ( %s ` a )' % (Fm, Fj)),
                              D(w, Aja, 'syl', [aU, w.s([pax_sub('w', 'a', 'j'), w.s([], 'eqid', '%s = %s' % (Fj, Fj)), w.s([], 'itgex', '%s e. _V' % FJx('a', 'j'))], 'fvmpt',
                                                        '( a e. %s -> ( %s ` a ) = %s )' % (U, Fj, FJx('a', 'j')))], '( %s ` a ) = %s' % (Fj, FJx('a', 'j')))],
              '( ( %s ` j ) ` a ) = %s' % (Fm, FJx('a', 'j')))
    fja2 = D(w, Aja, 'eqtrd', [fja, w.s([cbv_xy(w, 'j', '( j + 1 )', 'a')], 'a1i', '( %s -> %s = %s )' % (Aja, FJx('a', 'j'), L.PA('a', 'j', '( j + 1 )')))], '( ( %s ` j ) ` a ) = %s' % (Fm, L.PA('a', 'j', '( j + 1 )')))
    dva = D(w, Aja, 'eqtrd', [D(w, Aja, 'fveq1d', [toAj(dvj, '( CC _D %s ) = ( s e. %s |-> %s )' % (FJ_, U, L.PV('s', 'j', '( j + 1 )')))],
                                '( ( CC _D %s ) ` a ) = ( ( s e. %s |-> %s ) ` a )' % (FJ_, U, L.PV('s', 'j', '( j + 1 )'))),
                              D(w, Aja, 'syl', [aU, w.s([pa_sub(w, 's', 'a', 'j', '( j + 1 )', log=True), w.s([], 'eqid', '( s e. %s |-> %s ) = ( s e. %s |-> %s )' % (U, L.PV('s', 'j', '( j + 1 )'), U, L.PV('s', 'j', '( j + 1 )'))),
                                                        w.s([], 'itgex', '%s e. _V' % L.PV('a', 'j', '( j + 1 )'))], 'fvmpt',
                                                       '( a e. %s -> ( ( s e. %s |-> %s ) ` a ) = %s )' % (U, U, L.PV('s', 'j', '( j + 1 )'), L.PV('a', 'j', '( j + 1 )')))],
                                '( ( s e. %s |-> %s ) ` a ) = %s' % (U, L.PV('s', 'j', '( j + 1 )'), L.PV('a', 'j', '( j + 1 )')))],
              '( ( CC _D %s ) ` a ) = %s' % (FJ_, L.PV('a', 'j', '( j + 1 )')))
    jr2 = D(w, Aja, 'nnred', [jn2], 'j e. RR'); j1r2 = D(w, Aja, 'syl', [jr2, w.inst('peano2re')], '( j + 1 ) e. RR')
    ji = D(w, Aja, 'mpbir3and', [j1r2, linarith(w, Aja, [], 'j <_ ( j + 1 )', leaves={'j': jr2}), D(w, Aja, 'leidd', [j1r2], '( j + 1 ) <_ ( j + 1 )'),
                                 D(w, Aja, 'syl2anc', [jr2, j1r2, w.inst('elicc2')], '( ( j + 1 ) e. ( j [,] ( j + 1 ) ) <-> ( ( j + 1 ) e. RR /\\ j <_ ( j + 1 ) /\\ ( j + 1 ) <_ ( j + 1 ) ) )')],
            '( j + 1 ) e. ( j [,] ( j + 1 ) )')
    ara = D(w, Aja, 'abscld', [D(w, Aja, 'recnd', [D(w, Aja, 'recld', [ac_], '( Re ` a ) e. RR')], '( Re ` a ) e. CC')], '( abs ` ( Re ` a ) ) e. RR')
    rle = linarith(w, Aja, [alt], '( ( abs ` ( Re ` a ) ) + 1 ) <_ %s' % R1, leaves={'( abs ` ( Re ` a ) )': ara, ARZ: ad(w, Aja, arz, '%s e. RR' % ARZ)}, atoms=['( abs ` ( Re ` a ) )', ARZ])
    pbd = D(w, Aja, 'syl3anc', [w.s([phz], 'adantr', '( %s -> %s )' % (Aja, A0)), D(w, Aja, '3jca', [ad(w, Aja, r1r, '%s e. RR' % R1), ac_, rle], '( %s e. RR /\\ a e. CC /\\ ( ( abs ` ( Re ` a ) ) + 1 ) <_ %s )' % (R1, R1)),
                                D(w, Aja, 'jca', [jn2, ji], '( j e. NN /\\ ( j + 1 ) e. ( j [,] ( j + 1 ) ) )'), w.inst('zl3pbd')],
            '( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s )' % (L.PA('a', 'j', '( j + 1 )'), L.MJ('j', R1), L.PV('a', 'j', '( j + 1 )'), L.MJ('j', R1)))
    mjv = D(w, Aja, 'syl', [jn2, w.s([mj_sub(w, 'n', 'j', R1), w.s([], 'eqid', '%s = %s' % (MM_, MM_)), w.s([], 'ovex', '%s e. _V' % L.MJ('j', R1))], 'fvmpt',
                                     '( j e. NN -> ( %s ` j ) = %s )' % (MM_, L.MJ('j', R1)))], '( %s ` j ) = %s' % (MM_, L.MJ('j', R1)))
    b1 = D(w, Aja, 'breqtrrd', [D(w, Aja, 'eqbrtrd', [D(w, Aja, 'fveq2d', [fja2], '( abs ` ( ( %s ` j ) ` a ) ) = ( abs ` %s )' % (Fm, L.PA('a', 'j', '( j + 1 )'))),
                                                     D(w, Aja, 'simpld', [pbd], '( abs ` %s ) <_ %s' % (L.PA('a', 'j', '( j + 1 )'), L.MJ('j', R1)))], '( abs ` ( ( %s ` j ) ` a ) ) <_ %s' % (Fm, L.MJ('j', R1))), mjv],
            '( abs ` ( ( %s ` j ) ` a ) ) <_ ( %s ` j )' % (Fm, MM_))
    b2 = D(w, Aja, 'breqtrrd', [D(w, Aja, 'eqbrtrd', [D(w, Aja, 'fveq2d', [dva], '( abs ` ( ( CC _D %s ) ` a ) ) = ( abs ` %s )' % (FJ_, L.PV('a', 'j', '( j + 1 )'))),
                                                     D(w, Aja, 'simprd', [pbd], '( abs ` %s ) <_ %s' % (L.PV('a', 'j', '( j + 1 )'), L.MJ('j', R1)))], '( abs ` ( ( CC _D %s ) ` a ) ) <_ %s' % (FJ_, L.MJ('j', R1))), mjv],
            '( abs ` ( ( CC _D %s ) ` a ) ) <_ ( %s ` j )' % (FJ_, MM_))
    B1 = 'A. j e. NN A. a e. %s ( abs ` ( ( %s ` j ) ` a ) ) <_ ( %s ` j )' % (U, Fm, MM_)
    B2 = 'A. j e. NN A. a e. %s ( abs ` ( ( CC _D %s ) ` a ) ) <_ ( %s ` j )' % (U, FJ_, MM_)
    rb1 = D(w, Az, 'ralrimivva', [b1], B1); rb2 = D(w, Az, 'ralrimivva', [b2], B2)
    UHM = '( s e. %s |-> sum_ k e. NN ( ( %s ` k ) ` s ) )' % (U, Fm)
    uh = D(w, Az, 'syl2anc', [D(w, Az, 'jca', [ff, hol_all], '( %s : NN --> ( CC ^m %s ) /\\ A. j e. NN ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (Fm, U, FJ_, U, U, FJ_)),
                             D(w, Az, 'jca', [D(w, Az, '3jca', [mf, ms, rb1], '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s )' % (MM_, MM_, B1)),
                                              D(w, Az, '3jca', [mf, ms, rb2], '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s )' % (MM_, MM_, B2))],
                               '( ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s ) /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s ) )' % (MM_, MM_, B1, MM_, MM_, B2)),
                             w.inst('uhhol')], '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (UHM, U, U, UHM))
    # the uhhol sum is the improper integral
    As = '( %s /\\ s e. %s )' % (Az, U)
    sU = w.s([], 'simpr', '( %s -> s e. %s )' % (As, U))
    sc_, _ = fromU(As, 's', sU)
    Ask = '( %s /\\ k e. NN )' % As
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ask)
    Fk = '( w e. %s |-> %s )' % (U, FJx('w', 'k'))
    ksub = w.s([w.s([w.s([w.s([], 'id', '( m = k -> m = k )'), w.s([], 'oveq1', '( m = k -> ( m + 1 ) = ( k + 1 ) )')], 'oveq12d', '( m = k -> ( m (,) ( m + 1 ) ) = ( k (,) ( k + 1 ) ) )'),
                     w.s([], 'itgeq1', '( ( m (,) ( m + 1 ) ) = ( k (,) ( k + 1 ) ) -> %s = %s )' % (FJx('w', 'm'), FJx('w', 'k')))], 'syl', '( m = k -> %s = %s )' % (FJx('w', 'm'), FJx('w', 'k')))],
               'mpteq2dv', '( m = k -> ( w e. %s |-> %s ) = %s )' % (U, FJx('w', 'm'), Fk))
    fkv = D(w, Ask, 'syl', [kn, w.s([ksub, w.s([], 'eqid', '%s = %s' % (Fm, Fm)), w.s([uex], 'mptex', '%s e. _V' % Fk)], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (Fm, Fk))], '( %s ` k ) = %s' % (Fm, Fk))
    fks = D(w, Ask, 'eqtrd', [D(w, Ask, 'fveq1d', [fkv], '( ( %s ` k ) ` s ) = ( %s ` s )' % (Fm, Fk)),
                              D(w, Ask, 'syl', [ad(w, Ask, sU, 's e. %s' % U), w.s([pax_sub('w', 's', 'k'), w.s([], 'eqid', '%s = %s' % (Fk, Fk)), w.s([], 'itgex', '%s e. _V' % FJx('s', 'k'))], 'fvmpt',
                                                                              '( s e. %s -> ( %s ` s ) = %s )' % (U, Fk, FJx('s', 'k')))], '( %s ` s ) = %s' % (Fk, FJx('s', 'k')))],
              '( ( %s ` k ) ` s ) = %s' % (Fm, FJx('s', 'k')))
    se1 = D(w, As, 'sumeq2dv', [fks], 'sum_ k e. NN ( ( %s ` k ) ` s ) = sum_ k e. NN %s' % (Fm, FJx('s', 'k')))
    kj = w.s([w.s([w.s([], 'id', '( k = j -> k = j )'), w.s([], 'oveq1', '( k = j -> ( k + 1 ) = ( j + 1 ) )')], 'oveq12d', '( k = j -> ( k (,) ( k + 1 ) ) = ( j (,) ( j + 1 ) ) )'),
              w.s([], 'itgeq1', '( ( k (,) ( k + 1 ) ) = ( j (,) ( j + 1 ) ) -> %s = %s )' % (FJx('s', 'k'), FJx('s', 'j')))], 'syl', '( k = j -> %s = %s )' % (FJx('s', 'k'), FJx('s', 'j')))
    se2 = w.s([kj], 'cbvsumv', 'sum_ k e. NN %s = sum_ j e. NN %s' % (FJx('s', 'k'), FJx('s', 'j')))
    LLs = 'sum_ j e. NN %s' % FJx('s', 'j')
    phs = w.s([phz], 'adantr', '( %s -> %s )' % (As, A0))
    pcv = D(w, As, 'syl2anc', [phs, sc_, w.inst('zl3pcv')], '%s ~~>r %s' % (L.IMP('s'), LLs))
    vo = val_of(w, As, L.IMP('s'), LLs, pcv, imp_f(w, As, phs, sc_, 's'))
    pt = chain(w, As, ['sum_ k e. NN ( ( %s ` k ) ` s )' % Fm, 'sum_ k e. NN %s' % FJx('s', 'k'), LLs, '( ~~>r ` %s )' % L.IMP('s')],
               [se1, w.s([se2], 'a1i', '( %s -> sum_ k e. NN %s = %s )' % (As, FJx('s', 'k'), LLs)), ('r', vo)])
    FU_ = '( s e. %s |-> ( ~~>r ` %s ) )' % (U, L.IMP('s'))
    meq = D(w, Az, 'mpteq2dva', [pt], '%s = %s' % (UHM, FU_))
    rs = D(w, Az, 'syl', [ucc, w.inst('resmpt')], '( %s |` %s ) = %s' % (FIL, U, FU_))
    feq = D(w, Az, 'eqtr4d', [meq, rs], '%s = ( %s |` %s )' % (UHM, FIL, U))
    dsub = D(w, Az, 'sseqtrd', [D(w, Az, 'simprd', [uh], '%s C_ dom ( CC _D %s )' % (U, UHM)),
                                D(w, Az, 'dmeqd', [D(w, Az, 'oveq2d', [feq], '( CC _D %s ) = ( CC _D ( %s |` %s ) )' % (UHM, FIL, U))], 'dom ( CC _D %s ) = dom ( CC _D ( %s |` %s ) )' % (UHM, FIL, U))],
             '%s C_ dom ( CC _D ( %s |` %s ) )' % (U, FIL, U))
    COND = lambda u: '( z e. %s /\\ %s C_ CC /\\ %s C_ dom ( CC _D ( %s |` %s ) ) )' % (u, u, u, FIL, u)
    usub = w.s([w.s([], 'eleq2', '( u = %s -> ( z e. u <-> z e. %s ) )' % (U, U)), w.s([], 'sseq1', '( u = %s -> ( u C_ CC <-> %s C_ CC ) )' % (U, U)),
                w.s([w.s([], 'id', '( u = %s -> u = %s )' % (U, U)), w.s([w.s([w.s([], 'reseq2', '( u = %s -> ( %s |` u ) = ( %s |` %s ) )' % (U, FIL, FIL, U))], 'oveq2d',
                                                                        '( u = %s -> ( CC _D ( %s |` u ) ) = ( CC _D ( %s |` %s ) ) )' % (U, FIL, FIL, U))], 'dmeqd',
                                                               '( u = %s -> dom ( CC _D ( %s |` u ) ) = dom ( CC _D ( %s |` %s ) ) )' % (U, FIL, FIL, U))], 'sseq12d',
                    '( u = %s -> ( u C_ dom ( CC _D ( %s |` u ) ) <-> %s C_ dom ( CC _D ( %s |` %s ) ) ) )' % (U, FIL, U, FIL, U))], '3anbi123d', '( u = %s -> ( %s <-> %s ) )' % (U, COND('u'), COND(U)))
    ex = D(w, Az, 'syl2anc', [uop, D(w, Az, '3jca', [zU, ucc, dsub], COND(U)), w.s([usub], 'rspcev', '( ( %s e. %s /\\ %s ) -> E. u e. %s %s )' % (U, J, COND(U), J, COND('u')))],
           'E. u e. %s %s' % (J, COND('u')))
    ral = D(w, A0, 'ralrimiva', [ex], 'A. z e. CC E. u e. %s %s' % (J, COND('u')))
    # FIL : CC --> CC
    Ac = '( %s /\\ s e. CC )' % A0
    scc = w.s([], 'simpr', '( %s -> s e. CC )' % Ac)
    phc = w.s([], 'simpl', '( %s -> %s )' % (Ac, A0))
    pcc = D(w, Ac, 'syl2anc', [phc, scc, w.inst('zl3pcv')], '%s ~~>r %s' % (L.IMP('s'), LLs))
    vcc = D(w, Ac, 'eqeltrd', [val_of(w, Ac, L.IMP('s'), LLs, pcc, imp_f(w, Ac, phc, scc, 's')), D(w, Ac, 'syl', [pcc, w.inst('rlimcl')], '%s e. CC' % LLs)], '( ~~>r ` %s ) e. CC' % L.IMP('s'))
    filf = D(w, A0, 'fmptd', [vcc, w.s([], 'eqid', '%s = %s' % (FIL, FIL))], '%s : CC --> CC' % FIL)
    hol = D(w, A0, 'syl2anc', [D(w, A0, 'jca', [filf, cst(w, A0, 'ssid', 'CC C_ CC')], '( %s : CC --> CC /\\ CC C_ CC )' % FIL), ral, w.inst('holloc')],
            '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (FIL, FIL))
    # PH -> PHV
    BY = 'A. y e. ( 1 [,) +oo ) ( abs ` ( G ` y ) ) <_ ( K x. ( exp ` -u ( B x. y ) ) )'
    cb = w.s([w.s([w.s([w.s([], 'fveq2', '( y = v -> ( G ` y ) = ( G ` v ) )')], 'fveq2d', '( y = v -> ( abs ` ( G ` y ) ) = ( abs ` ( G ` v ) ) )'),
                   w.s([w.s([w.s([w.s([], 'oveq2', '( y = v -> ( B x. y ) = ( B x. v ) )')], 'negeqd', '( y = v -> -u ( B x. y ) = -u ( B x. v ) )')], 'fveq2d',
                             '( y = v -> ( exp ` -u ( B x. y ) ) = ( exp ` -u ( B x. v ) ) )')], 'oveq2d', '( y = v -> ( K x. ( exp ` -u ( B x. y ) ) ) = ( K x. ( exp ` -u ( B x. v ) ) ) )')],
              'breq12d', '( y = v -> ( ( abs ` ( G ` y ) ) <_ ( K x. ( exp ` -u ( B x. y ) ) ) <-> ( abs ` ( G ` v ) ) <_ ( K x. ( exp ` -u ( B x. v ) ) ) ) )')], 'cbvralvw', '( %s <-> %s )' % (BY, BNDV))
    b3 = w.s([cb], '3anbi3i', '( ( K e. RR+ /\\ B e. RR+ /\\ %s ) <-> ( K e. RR+ /\\ B e. RR+ /\\ %s ) )' % (BY, BNDV))
    b4 = w.s([b3], 'anbi2i', '( %s <-> %s )' % (PH, A0))
    w.qed([w.s([b4], 'biimpi', '( %s -> %s )' % (PH, A0)), hol], 'syl', S['zl3pih'])
    go(w)
