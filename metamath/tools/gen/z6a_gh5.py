"""Z6a (block z6ab): the log-Gamma series is holomorphic on an open box in the right
half-plane (z6hbxuh: the uniform-limit package, z6hbxhol: uhhol)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_ghlib import *
from z6a_gh3 import V1, DD, CK, TK, DTK
from congr import mptval
from lin import linarith

B = BX('L', 'R')
A0 = '( L e. RR+ /\\ R e. RR )'
IN = lambda K: '( p e. %s |-> %s )' % (B, TK(K, 'p'))
GF = '( a e. NN |-> %s )' % IN('a')
CM = '( ( 1 + ( 2 x. R ) ) x. ( 2 x. R ) )'
CD = '( 1 + ( 2 x. R ) )'
MJ = '( n e. NN |-> ( %s x. ( n ^c -u 2 ) ) )' % CM
MD = '( n e. NN |-> ( %s x. ( n ^c -u 2 ) ) )' % CD


def UHM(Fn, Mn, U):
    return '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (Mn, Mn, U, Fn, Mn)


def UHD(Fn, Rn, U):
    return '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (Rn, Rn, U, Fn, Rn)


def UHT(Fn, U):
    return 'A. j e. NN ( ( %s ` j ) e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D ( %s ` j ) ) )' % (Fn, U, U, Fn)


def UH(Fn, Mn, Rn, U):
    return '( ( %s : NN --> ( CC ^m %s ) /\\ %s ) /\\ ( %s /\\ %s ) )' % (Fn, U, UHT(Fn, U), UHM(Fn, Mn, U), UHD(Fn, Rn, U))


GSUMZ = '( z e. %s |-> sum_ k e. NN %s )' % (B, TK('k', 'z'))
S_BXUH = '( %s -> %s )' % (A0, UH(GF, MJ, MD, B))
S_BXHOL = '( %s -> %s )' % (A0, HOLG(GSUMZ, B))


def bex(w, ante):
    return w.s([w.s([w.s([], 'bxopn', '%s e. %s' % (B, TOP))], 'elexi', '%s e. _V' % B)], 'a1i', '( %s -> %s e. _V )' % (ante, B))


def subst(w, expr, var, val):
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))
    stp, new = w.congr(expr, {var: val}, '%s = %s' % (var, val), {var: idk})
    return stp


def gfv(w, ante, K, mk):
    """( ante -> ( GF ` K ) = IN(K) )"""
    sub = subst(w, IN('a'), 'a', K)
    ex = w.s([w.s([w.s([w.s([], 'bxopn', '%s e. %s' % (B, TOP))], 'elexi', '%s e. _V' % B)], 'mptex', '%s e. _V' % IN(K))], 'a1i', '( %s -> %s e. _V )' % (ante, IN(K)))
    fv = w.s([sub, w.s([], 'eqid', '%s = %s' % (GF, GF))], 'fvmptg', '( ( %s e. NN /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (K, IN(K), GF, K, IN(K)))
    return w.s([mk, ex, fv], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, GF, K, IN(K)))


def inval(w, ante, K, Y, my):
    """( ante -> ( IN(K) ` Y ) = TK(K,Y) )"""
    stp, val = mpval(w, ante, 'p', B, TK(K, 'p'), Y, my)
    return stp


def inb(w, ante, lrp, rr, ystep, Y='y'):
    """facts for Y e. B: (Y e. CC, 0 <_ Re Y, Y e. V1, abs Y <_ 2 R)"""
    s = st(w, ante)
    el = s([ystep, w.inst('elbxi')], 'syl', '( %s e. CC /\\ ( L < ( Re ` %s ) /\\ ( Re ` %s ) < R ) /\\ ( -u R < ( Im ` %s ) /\\ ( Im ` %s ) < R ) )' % (Y, Y, Y, Y, Y))
    yc = s([el, w.inst('simp1')], 'syl', '%s e. CC' % Y)
    lre = s([s([el, w.inst('simp2')], 'syl', '( L < ( Re ` %s ) /\\ ( Re ` %s ) < R )' % (Y, Y))], 'simpld', 'L < ( Re ` %s )' % Y)
    lr = s([lrp], 'rpred', 'L e. RR')
    l0 = s([lrp], 'rpge0d', '0 <_ L')
    ry = s([yc], 'recld', '( Re ` %s ) e. RR' % Y)
    rge = linarith(w, ante, [l0, lre], '0 <_ ( Re ` %s )' % Y, leaves={'L': lr, '( Re ` %s )' % Y: ry})
    m1 = w.s([w.s([], '1re', '1 e. RR')], 'renegcli', '-u 1 e. RR')
    bi = s([w.s([m1, w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ -u 1 < ( Re ` %s ) ) )' % (Y, V1, Y, Y))], 'a1i',
           '( %s e. %s <-> ( %s e. CC /\\ -u 1 < ( Re ` %s ) ) )' % (Y, V1, Y, Y))
    gt = linarith(w, ante, [rge], '-u 1 < ( Re ` %s )' % Y, leaves={'( Re ` %s )' % Y: ry})
    yv = s([s([yc, gt], 'jca', '( %s e. CC /\\ -u 1 < ( Re ` %s ) )' % (Y, Y)), bi], 'mpbird', '%s e. %s' % (Y, V1))
    ab = s([s([s([lr, l0, rr], '3jca', '( L e. RR /\\ 0 <_ L /\\ R e. RR )'), ystep], 'jca', '( ( L e. RR /\\ 0 <_ L /\\ R e. RR ) /\\ %s e. %s )' % (Y, B)), w.inst('bxabs')],
           'syl', '( abs ` %s ) <_ ( 2 x. R )' % Y)
    return yc, rge, yv, ab


def cxm2(w, ante, jn, J='j'):
    """( ante -> ( J ^c -u 2 ) = ( 1 / ( J ^ 2 ) ) )"""
    s = st(w, ante)
    jc = s([jn], 'nncnd', '%s e. CC' % J)
    j0 = s([jn], 'nnne0d', '%s =/= 0' % J)
    return s([s([jc, j0, s([], '2cnd', '2 e. CC'), w.inst('cxpneg')], 'syl3anc', '( %s ^c -u 2 ) = ( 1 / ( %s ^c 2 ) )' % (J, J)),
              s([s([jc, c1(w, ante, '2nn0', '2 e. NN0'), w.inst('cxpexp')], 'syl2anc', '( %s ^c 2 ) = ( %s ^ 2 )' % (J, J))], 'oveq2d',
                '( 1 / ( %s ^c 2 ) ) = ( 1 / ( %s ^ 2 ) )' % (J, J))], 'eqtrd', '( %s ^c -u 2 ) = ( 1 / ( %s ^ 2 ) )' % (J, J))


def bxuh():
    w = W('z6hbxuh', 'The log-Gamma term functions on an open box in the right half-plane satisfy the hypotheses '
          'of the uniform-limit theorem ~ uhhol ( ~ z6hthol , ~ z6htb , ~ z6hdtb ).')
    s = st(w, A0)
    lrp = w.s([], 'simpl', '( %s -> L e. RR+ )' % A0)
    rr = w.s([], 'simpr', '( %s -> R e. RR )' % A0)
    bo = c1(w, A0, 'bxopn', '%s e. %s' % (B, TOP))
    # B C_ V1
    Aw = '( %s /\\ w e. %s )' % (A0, B)
    _, _, wv, _ = inb(w, Aw, w.s([lrp], 'adantr', '( %s -> L e. RR+ )' % Aw), w.s([rr], 'adantr', '( %s -> R e. RR )' % Aw), w.s([], 'simpr', '( %s -> w e. %s )' % (Aw, B)), 'w')
    bv = s([w.s([wv], 'ex', '( %s -> ( w e. %s -> w e. %s ) )' % (A0, B, V1))], 'ssrdv', '%s C_ %s' % (B, V1))
    # GF : NN --> ( CC ^m B )
    Aa = '( %s /\\ a e. NN )' % A0
    Aap = '( %s /\\ p e. %s )' % (Aa, B)
    an = w.s([w.s([], 'simpr', '( %s -> a e. NN )' % Aa)], 'adantr', '( %s -> a e. NN )' % Aap)
    pv = w.s([w.s([bv], 'ad2antrr', '( %s -> %s C_ %s )' % (Aap, B, V1)), w.s([], 'simpr', '( %s -> p e. %s )' % (Aap, B))], 'sseldd', '( %s -> p e. %s )' % (Aap, V1))
    t = st(w, Aap)
    fac = t([t([an, pv], 'jca', '( a e. NN /\\ p e. %s )' % V1), w.inst('z6hv1')], 'syl', '( ( ( p / a ) + 1 ) e. %s /\\ ( p + a ) =/= 0 )' % DD)
    qd = t([fac], 'simpld', '( ( p / a ) + 1 ) e. %s' % DD)
    ed = w.s([], 'eqid', '%s = %s' % (DD, DD))
    pc = t([w.s([w.s([], 'hpss', '%s C_ CC' % V1)], 'a1i', '( %s -> %s C_ CC )' % (Aap, V1)), pv], 'sseldd', 'p e. CC')
    krp = t([an], 'nnrpd', 'a e. RR+')
    k1rp = t([t([an, w.inst('peano2nn')], 'syl', '( a + 1 ) e. NN')], 'nnrpd', '( a + 1 ) e. RR+')
    cca = t([t([t([k1rp, krp], 'rpdivcld', '( ( a + 1 ) / a ) e. RR+')], 'relogcld', '%s e. RR' % CK('a'))], 'recnd', '%s e. CC' % CK('a'))
    tc = t([t([pc, cca], 'mulcld', '( p x. %s ) e. CC' % CK('a')),
            t([t([qd], 'eldifad', '( ( p / a ) + 1 ) e. CC'), t([qd, w.s([ed], 'logdmn0', '( ( ( p / a ) + 1 ) e. %s -> ( ( p / a ) + 1 ) =/= 0 )' % DD)], 'syl', '( ( p / a ) + 1 ) =/= 0')],
              'logcld', '( log ` ( ( p / a ) + 1 ) ) e. CC')], 'subcld', '%s e. CC' % TK('a', 'p'))
    mf = w.s([tc, w.s([], 'eqid', '%s = %s' % (IN('a'), IN('a')))], 'fmptd', '( %s -> %s : %s --> CC )' % (Aa, IN('a'), B))
    cn = c1(w, Aa, 'cnex', 'CC e. _V')
    mm = w.s([mf, w.s([cn, bex(w, Aa)], 'elmapd', '( %s -> ( %s e. ( CC ^m %s ) <-> %s : %s --> CC ) )' % (Aa, IN('a'), B, IN('a'), B))], 'mpbird',
             '( %s -> %s e. ( CC ^m %s ) )' % (Aa, IN('a'), B))
    fm = s([mm, w.s([], 'eqid', '%s = %s' % (GF, GF))], 'fmptd', '%s : NN --> ( CC ^m %s )' % (GF, B))
    # termwise holomorphy
    Aj = '( %s /\\ j e. NN )' % A0
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    u = st(w, Aj)
    sv = gfv(w, Aj, 'j', jn)
    ZM = '( z e. %s |-> %s )' % (B, TK('j', 'z'))
    cbv = w.s([subst(w, TK('j', 'z'), 'z', 'p')], 'cbvmptv', '%s = %s' % (ZM, IN('j')))
    trij = u([jn, w.s([bo], 'adantr', '( %s -> %s e. %s )' % (Aj, B, TOP)), w.s([bv], 'adantr', '( %s -> %s C_ %s )' % (Aj, B, V1))], '3jca',
             '( j e. NN /\\ %s e. %s /\\ %s C_ %s )' % (B, TOP, B, V1))
    holz = u([trij, w.inst('z6hthol')], 'syl', HOLG(ZM, B))
    eqz = u([u([cbv], 'a1i', '%s = %s' % (ZM, IN('j'))), sv], 'eqtr4d', '%s = ( %s ` j )' % (ZM, GF))
    holj = holeq(w, Aj, ZM, '( %s ` j )' % GF, B, holz, eqz)
    ral = s([holj], 'ralrimiva', UHT(GF, B))
    # the majorants
    r2 = s([c1(w, A0, '2re', '2 e. RR'), rr], 'remulcld', '( 2 x. R ) e. RR')
    cdr = s([c1(w, A0, '1re', '1 e. RR'), r2], 'readdcld', '%s e. RR' % CD)
    cmr = s([cdr, r2], 'remulcld', '%s e. RR' % CM)
    An = '( %s /\\ n e. NN )' % A0
    nm2 = w.s([w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An)], 'nnrpd', '( %s -> n e. RR+ )' % An),
               w.s([w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR')], 'a1i', '( %s -> -u 2 e. RR )' % An)], 'rpcxpcld', '( %s -> ( n ^c -u 2 ) e. RR+ )' % An)
    nm2r = w.s([nm2], 'rpred', '( %s -> ( n ^c -u 2 ) e. RR )' % An)
    mjf = s([w.s([w.s([cmr], 'adantr', '( %s -> %s e. RR )' % (An, CM)), nm2r], 'remulcld', '( %s -> ( %s x. ( n ^c -u 2 ) ) e. RR )' % (An, CM)),
             w.s([], 'eqid', '%s = %s' % (MJ, MJ))], 'fmptd', '%s : NN --> RR' % MJ)
    mdf = s([w.s([w.s([cdr], 'adantr', '( %s -> %s e. RR )' % (An, CD)), nm2r], 'remulcld', '( %s -> ( %s x. ( n ^c -u 2 ) ) e. RR )' % (An, CD)),
             w.s([], 'eqid', '%s = %s' % (MD, MD))], 'fmptd', '%s : NN --> RR' % MD)
    two = s([c1(w, A0, '2re', '2 e. RR'), c1(w, A0, '1lt2', '1 < 2')], 'jca', '( 2 e. RR /\\ 1 < 2 )')
    mjc = s([s([two, s([cmr], 'recnd', '%s e. CC' % CM)], 'jca', '( ( 2 e. RR /\\ 1 < 2 ) /\\ %s e. CC )' % CM), w.inst('zsercvgc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % MJ)
    mdc = s([s([two, s([cdr], 'recnd', '%s e. CC' % CD)], 'jca', '( ( 2 e. RR /\\ 1 < 2 ) /\\ %s e. CC )' % CD), w.inst('zsercvgc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % MD)
    # the bounds at ( j , y )
    Ajy = '( %s /\\ ( j e. NN /\\ y e. %s ) )' % (A0, B)
    v = st(w, Ajy)
    jn2 = w.s([], 'simprl', '( %s -> j e. NN )' % Ajy)
    yb = w.s([], 'simprr', '( %s -> y e. %s )' % (Ajy, B))
    lrp2 = w.s([lrp], 'adantr', '( %s -> L e. RR+ )' % Ajy)
    rr2 = w.s([rr], 'adantr', '( %s -> R e. RR )' % Ajy)
    yc, rge, yv, ab = inb(w, Ajy, lrp2, rr2, yb)
    vv = v([v([gfv(w, Ajy, 'j', jn2)], 'fveq1d', '( ( %s ` j ) ` y ) = ( %s ` y )' % (GF, IN('j'))), inval(w, Ajy, 'j', 'y', yb)], 'eqtrd',
           '( ( %s ` j ) ` y ) = %s' % (GF, TK('j', 'y')))
    kin = v([jn2, v([yc, rge], 'jca', '( y e. CC /\\ 0 <_ ( Re ` y ) )')], 'jca', '( j e. NN /\\ ( y e. CC /\\ 0 <_ ( Re ` y ) ) )')
    tb = v([kin, w.inst('z6htb')], 'syl', '( abs ` %s ) <_ ( ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) x. ( abs ` y ) )' % TK('j', 'y'))
    j2 = v([v([jn2], 'nnrpd', 'j e. RR+'), c1(w, Ajy, '2z', '2 e. ZZ')], 'rpexpcld', '( j ^ 2 ) e. RR+')
    ay = v([yc], 'abscld', '( abs ` y ) e. RR')
    ay0 = v([yc], 'absge0d', '0 <_ ( abs ` y )')
    one = c1(w, Ajy, '1re', '1 e. RR')
    r2y = v([c1(w, Ajy, '2re', '2 e. RR'), rr2], 'remulcld', '( 2 x. R ) e. RR')
    a1y = v([one, ay], 'readdcld', '( 1 + ( abs ` y ) ) e. RR')
    cdy = v([one, r2y], 'readdcld', '%s e. RR' % CD)
    qa = v([a1y, j2], 'rerpdivcld', '( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) e. RR')
    qb = v([cdy, j2], 'rerpdivcld', '( %s / ( j ^ 2 ) ) e. RR' % CD)
    a10 = linarith(w, Ajy, [ay0], '0 <_ ( 1 + ( abs ` y ) )', leaves={'( abs ` y )': ay})
    qa0 = v([a1y, j2, a10], 'divge0d', '0 <_ ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) )')
    qle = v([a1y, cdy, j2, v([ay, r2y, one, ab], 'leadd2dd', '( 1 + ( abs ` y ) ) <_ %s' % CD)], 'lediv1dd', '( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) <_ ( %s / ( j ^ 2 ) )' % CD)
    mono = v([qa, qb, ay, r2y, qa0, qle, ay0, ab], 'lemul12ad', '( ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) x. ( abs ` y ) ) <_ ( ( %s / ( j ^ 2 ) ) x. ( 2 x. R ) )' % CD)
    cx = cxm2(w, Ajy, jn2)
    j2c = v([j2], 'rpcnd', '( j ^ 2 ) e. CC'); j20 = v([j2], 'rpne0d', '( j ^ 2 ) =/= 0')
    cdc = v([cdy], 'recnd', '%s e. CC' % CD); r2c = v([r2y], 'recnd', '( 2 x. R ) e. CC')
    cmc = v([cdc, r2c], 'mulcld', '%s e. CC' % CM)
    e1 = v([cmc, j2c, j20], 'divrecd', '( %s / ( j ^ 2 ) ) = ( %s x. ( 1 / ( j ^ 2 ) ) )' % (CM, CM))
    e2 = v([cdc, r2c, j2c, j20], 'div23d', '( %s / ( j ^ 2 ) ) = ( ( %s / ( j ^ 2 ) ) x. ( 2 x. R ) )' % (CM, CD))
    e3 = v([cx], 'oveq2d', '( %s x. ( j ^c -u 2 ) ) = ( %s x. ( 1 / ( j ^ 2 ) ) )' % (CM, CM))
    c12 = v([e2, e1], 'eqtr3d', '( ( %s / ( j ^ 2 ) ) x. ( 2 x. R ) ) = ( %s x. ( 1 / ( j ^ 2 ) ) )' % (CD, CM))
    conv = v([c12, e3], 'eqtr4d', '( ( %s / ( j ^ 2 ) ) x. ( 2 x. R ) ) = ( %s x. ( j ^c -u 2 ) )' % (CD, CM))
    mv, _ = mpval(w, Ajy, 'n', 'NN', '( %s x. ( n ^c -u 2 ) )' % CM, 'j', jn2)
    ft = v([v([vv], 'fveq2d', '( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s )' % (GF, TK('j', 'y'))), tb], 'eqbrtrd',
           '( abs ` ( ( %s ` j ) ` y ) ) <_ ( ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) x. ( abs ` y ) )' % GF)
    mono2 = v([mono, conv], 'breqtrd', '( ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) x. ( abs ` y ) ) <_ ( %s x. ( j ^c -u 2 ) )' % CM)
    absr = v([v([v([jn2, yv], 'jca', '( j e. NN /\\ y e. %s )' % V1), w.inst('z6hv1')], 'syl', '( ( ( y / j ) + 1 ) e. %s /\\ ( y + j ) =/= 0 )' % DD)], 'simpld',
             '( ( y / j ) + 1 ) e. %s' % DD)
    jrp = v([jn2], 'nnrpd', 'j e. RR+')
    j1rp = v([v([jn2, w.inst('peano2nn')], 'syl', '( j + 1 ) e. NN')], 'nnrpd', '( j + 1 ) e. RR+')
    ccj = v([v([v([j1rp, jrp], 'rpdivcld', '( ( j + 1 ) / j ) e. RR+')], 'relogcld', '%s e. RR' % CK('j'))], 'recnd', '%s e. CC' % CK('j'))
    tkc = v([v([yc, ccj], 'mulcld', '( y x. %s ) e. CC' % CK('j')),
             v([v([absr], 'eldifad', '( ( y / j ) + 1 ) e. CC'), v([absr, w.s([ed], 'logdmn0', '( ( ( y / j ) + 1 ) e. %s -> ( ( y / j ) + 1 ) =/= 0 )' % DD)], 'syl', '( ( y / j ) + 1 ) =/= 0')],
               'logcld', '( log ` ( ( y / j ) + 1 ) ) e. CC')], 'subcld', '%s e. CC' % TK('j', 'y'))
    fvr = v([v([vv, tkc], 'eqeltrd', '( ( %s ` j ) ` y ) e. CC' % GF)], 'abscld', '( abs ` ( ( %s ` j ) ` y ) ) e. RR' % GF)
    prod1 = v([qa, ay], 'remulcld', '( ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) x. ( abs ` y ) ) e. RR')
    mjr = v([w.s([cmr], 'adantr', '( %s -> %s e. RR )' % (Ajy, CM)), v([v([jrp, v([w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR')], 'a1i', '-u 2 e. RR')], 'rpcxpcld', '( j ^c -u 2 ) e. RR+')],
                                                                   'rpred', '( j ^c -u 2 ) e. RR')], 'remulcld', '( %s x. ( j ^c -u 2 ) ) e. RR' % CM)
    bd = v([fvr, prod1, mjr, ft, mono2], 'letrd', '( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s x. ( j ^c -u 2 ) )' % (GF, CM))
    bd2 = v([bd, mv], 'breqtrrd', '( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (GF, MJ))
    mb = s([bd2], 'ralrimivva', 'A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j )' % (B, GF, MJ))
    um = s([mjf, mjc, mb], '3jca', UHM(GF, MJ, B))
    # the derivative bound
    trij2 = v([jn2, w.s([bo], 'adantr', '( %s -> %s e. %s )' % (Ajy, B, TOP)), w.s([bv], 'adantr', '( %s -> %s C_ %s )' % (Ajy, B, V1))], '3jca',
              '( j e. NN /\\ %s e. %s /\\ %s C_ %s )' % (B, TOP, B, V1))
    DZ = '( z e. %s |-> %s )' % (B, DTK('j', 'z'))
    dvz = v([trij2, w.inst('z6htdv')], 'syl', '( CC _D %s ) = %s' % (ZM, DZ))
    eqz2 = v([v([cbv], 'a1i', '%s = %s' % (ZM, IN('j'))), gfv(w, Ajy, 'j', jn2)], 'eqtr4d', '%s = ( %s ` j )' % (ZM, GF))
    dvj = v([v([eqz2], 'oveq2d', '( CC _D %s ) = ( CC _D ( %s ` j ) )' % (ZM, GF)), dvz], 'eqtr3d', '( CC _D ( %s ` j ) ) = %s' % (GF, DZ))
    dval, _ = mpval(w, Ajy, 'z', B, DTK('j', 'z'), 'y', yb)
    dvv = v([v([dvj], 'fveq1d', '( ( CC _D ( %s ` j ) ) ` y ) = ( %s ` y )' % (GF, DZ)), dval], 'eqtrd', '( ( CC _D ( %s ` j ) ) ` y ) = %s' % (GF, DTK('j', 'y')))
    db = v([kin, w.inst('z6hdtb')], 'syl', '( abs ` %s ) <_ ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) )' % DTK('j', 'y'))
    dconv = v([v([cdc, j2c, j20], 'divrecd', '( %s / ( j ^ 2 ) ) = ( %s x. ( 1 / ( j ^ 2 ) ) )' % (CD, CD)), v([cx], 'oveq2d', '( %s x. ( j ^c -u 2 ) ) = ( %s x. ( 1 / ( j ^ 2 ) ) )' % (CD, CD))],
              'eqtr4d', '( %s / ( j ^ 2 ) ) = ( %s x. ( j ^c -u 2 ) )' % (CD, CD))
    ynz = v([v([v([jn2, yv], 'jca', '( j e. NN /\\ y e. %s )' % V1), w.inst('z6hv1')], 'syl', '( ( ( y / j ) + 1 ) e. %s /\\ ( y + j ) =/= 0 )' % DD)], 'simprd', '( y + j ) =/= 0')
    dtc = v([ccj, v([v([yc, v([jn2], 'nncnd', 'j e. CC')], 'addcld', '( y + j ) e. CC'), ynz], 'reccld', '( 1 / ( y + j ) ) e. CC')], 'subcld', '%s e. CC' % DTK('j', 'y'))
    dfr = v([v([dvv, dtc], 'eqeltrd', '( ( CC _D ( %s ` j ) ) ` y ) e. CC' % GF)], 'abscld', '( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) e. RR' % GF)
    dft = v([v([dvv], 'fveq2d', '( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) = ( abs ` %s )' % (GF, DTK('j', 'y'))), db], 'eqbrtrd',
            '( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) )' % GF)
    dmono = v([qle, dconv], 'breqtrd', '( ( 1 + ( abs ` y ) ) / ( j ^ 2 ) ) <_ ( %s x. ( j ^c -u 2 ) )' % CD)
    mdr = v([w.s([cdr], 'adantr', '( %s -> %s e. RR )' % (Ajy, CD)), v([v([jrp, v([w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR')], 'a1i', '-u 2 e. RR')], 'rpcxpcld', '( j ^c -u 2 ) e. RR+')],
                                                                   'rpred', '( j ^c -u 2 ) e. RR')], 'remulcld', '( %s x. ( j ^c -u 2 ) ) e. RR' % CD)
    dbd = v([dfr, qa, mdr, dft, dmono], 'letrd', '( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s x. ( j ^c -u 2 ) )' % (GF, CD))
    mdv, _ = mpval(w, Ajy, 'n', 'NN', '( %s x. ( n ^c -u 2 ) )' % CD, 'j', jn2)
    dbd2 = v([dbd, mdv], 'breqtrrd', '( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j )' % (GF, MD))
    rb = s([dbd2], 'ralrimivva', 'A. j e. NN A. y e. %s ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j )' % (B, GF, MD))
    ud = s([mdf, mdc, rb], '3jca', UHD(GF, MD, B))
    w.qed([s([fm, ral], 'jca', '( %s : NN --> ( CC ^m %s ) /\\ %s )' % (GF, B, UHT(GF, B))), s([um, ud], 'jca', '( %s /\\ %s )' % (UHM(GF, MJ, B), UHD(GF, MD, B)))], 'jca', S_BXUH)
    return run(w)


def bxhol():
    w = W('z6hbxhol', 'The log-Gamma series ` sum_ k z log ( ( k + 1 ) / k ) - log ( z / k + 1 ) ` is holomorphic on every '
          'open box in the right half-plane ( ~ uhhol at ~ z6hbxuh ).')
    GS = '( z e. %s |-> sum_ k e. NN ( ( %s ` k ) ` z ) )' % (B, GF)
    hol = w.s([w.s([], 'z6hbxuh', S_BXUH), w.inst('uhhol')], 'syl', '( %s -> %s )' % (A0, HOLG(GS, B)))
    Az = '( %s /\\ z e. %s )' % (A0, B)
    Azk = '( %s /\\ k e. NN )' % Az
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Azk)
    zb = w.s([], 'simplr', '( %s -> z e. %s )' % (Azk, B))
    vv = w.s([w.s([gfv(w, Azk, 'k', kn)], 'fveq1d', '( %s -> ( ( %s ` k ) ` z ) = ( %s ` z ) )' % (Azk, GF, IN('k'))), inval(w, Azk, 'k', 'z', zb)], 'eqtrd',
             '( %s -> ( ( %s ` k ) ` z ) = %s )' % (Azk, GF, TK('k', 'z')))
    sm = w.s([vv], 'sumeq2dv', '( %s -> sum_ k e. NN ( ( %s ` k ) ` z ) = sum_ k e. NN %s )' % (Az, GF, TK('k', 'z')))
    eq = w.s([sm], 'mpteq2dva', '( %s -> %s = %s )' % (A0, GS, GSUMZ))
    h = holeq(w, A0, GS, GSUMZ, B, hol, eq)
    w.lines[-1] = w.lines[-1].replace(h + ':', 'qed:', 1)
    return run(w)


if __name__ == '__main__':
    want = sys.argv[1:]
    for lab, fn in [('z6hbxuh', bxuh), ('z6hbxhol', bxhol)]:
        if lab in want:
            if fn():
                status(lab)
