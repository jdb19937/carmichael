"""Sortie Z5c, section F: the L-series factorisation (Detector.lean 690-972)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5clib import *
from cl import Closure, lift
import lin

HG = '( ( G : NN --> CC /\\ ( G ` 1 ) = 1 /\\ %s ) /\\ ( A e. Fin /\\ A C_ NN ) )' % MUL('G')


def z5mulprod():
    w = W('z5mulprod', "A completely multiplicative G on NN with G ( 1 ) = 1 takes a finite product of positive integers to the product "
                       "of its values (Lean map_prod, as LSeries_Gker_char uses it for chi; findcard2d).")
    ante = HG
    st = mkst(w, ante)
    hg = st([], 'simpl', '( G : NN --> CC /\\ ( G ` 1 ) = 1 /\\ %s )' % MUL('G'))
    gf = st([hg], 'simp1d', 'G : NN --> CC'); g1 = st([hg], 'simp2d', '( G ` 1 ) = 1'); gm = st([hg], 'simp3d', MUL('G'))
    af = st([], 'simprl', 'A e. Fin'); an = st([], 'simprr', 'A C_ NN')
    PS = lambda X: '( G ` prod_ p e. %s p ) = prod_ p e. %s ( G ` p )' % (X, X)
    cgs = {}
    for X in ('(/)', 'y', '( y u. { z } )', 'A'):
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (X, X))
        st_, new = w.wcongr(PS('x'), {'x': X}, 'x = %s' % X, {'x': idx})
        cgs[X] = st_
    # base
    b1 = st([w.s([w.s([], 'prod0', 'prod_ p e. (/) p = 1')], 'fveq2i', '( G ` prod_ p e. (/) p ) = ( G ` 1 )'), g1], 'eqtrid',
            '( G ` prod_ p e. (/) p ) = 1')
    b2 = w.s([], 'prod0', 'prod_ p e. (/) ( G ` p ) = 1')
    base = st([b1, w.s([b2], 'a1i', '( %s -> prod_ p e. (/) ( G ` p ) = 1 )' % ante)], 'eqtr4d', PS('(/)'))
    # step
    c = '( %s /\\ ( y C_ A /\\ z e. ( A \\ y ) ) )' % ante
    sc = mkst(w, c)
    ya = sc([], 'simprl', 'y C_ A')
    zin = sc([], 'simprr', 'z e. ( A \\ y )')
    za = sc([zin], 'eldifad', 'z e. A'); zny = sc([zin], 'eldifbd', '-. z e. y')
    yf = sc([lift(w, af, c), ya, w.inst('ssfi')], 'syl2anc', 'y e. Fin')
    zv = w.s([w.s([], 'vex', 'z e. _V')], 'a1i', '( %s -> z e. _V )' % c)
    yn = sc([ya, lift(w, an, c)], 'sstrd', 'y C_ NN')
    zn = sc([lift(w, an, c), za], 'sseldd', 'z e. NN')
    ck = '( %s /\\ p e. y )' % c
    pn = w.s([w.s([yn], 'adantr', '( %s -> y C_ NN )' % ck), w.s([], 'simpr', '( %s -> p e. y )' % ck)], 'sseldd', '( %s -> p e. NN )' % ck)
    pc = w.s([pn], 'nncnd', '( %s -> p e. CC )' % ck)
    gp = w.s([w.s([lift(w, gf, c)], 'adantr', '( %s -> G : NN --> CC )' % ck), pn], 'ffvelcdmd', '( %s -> ( G ` p ) e. CC )' % ck)
    nfc = w.s([], 'nfv', 'F/ p %s' % c)
    zc = sc([zn], 'nncnd', 'z e. CC')
    sp1 = w.s([nfc, w.s([], 'nfcv', 'F/_ p z'), yf, zv, zny, pc, w.s([], 'id', '( p = z -> p = z )'), zc], 'fprodsplitsn',
              '( %s -> prod_ p e. ( y u. { z } ) p = ( prod_ p e. y p x. z ) )' % c)
    gz = sc([lift(w, gf, c), zn], 'ffvelcdmd', '( G ` z ) e. CC')
    sp2 = w.s([nfc, w.s([], 'nfcv', 'F/_ p ( G ` z )'), yf, zv, zny, gp, w.s([], 'fveq2', '( p = z -> ( G ` p ) = ( G ` z ) )'), gz], 'fprodsplitsn',
              '( %s -> prod_ p e. ( y u. { z } ) ( G ` p ) = ( prod_ p e. y ( G ` p ) x. ( G ` z ) ) )' % c)
    PY = 'prod_ p e. y p'
    pyn = sc([yf, pn], 'fprodnncl', '%s e. NN' % PY)
    # multiplicativity at ( PY , z )
    MB = lambda i, j: '( G ` ( %s x. %s ) ) = ( ( G ` %s ) x. ( G ` %s ) )' % (i, j, i, j)
    r1 = w.s([w.s([w.s([], 'oveq1', '( i = %s -> ( i x. j ) = ( %s x. j ) )' % (PY, PY))], 'fveq2d', '( i = %s -> ( G ` ( i x. j ) ) = ( G ` ( %s x. j ) ) )' % (PY, PY)),
              w.s([w.s([], 'fveq2', '( i = %s -> ( G ` i ) = ( G ` %s ) )' % (PY, PY))], 'oveq1d', '( i = %s -> ( ( G ` i ) x. ( G ` j ) ) = ( ( G ` %s ) x. ( G ` j ) ) )' % (PY, PY))],
             'eqeq12d', '( i = %s -> ( %s <-> %s ) )' % (PY, MB('i', 'j'), MB(PY, 'j')))
    r2 = w.s([w.s([w.s([], 'oveq2', '( j = z -> ( %s x. j ) = ( %s x. z ) )' % (PY, PY))], 'fveq2d', '( j = z -> ( G ` ( %s x. j ) ) = ( G ` ( %s x. z ) ) )' % (PY, PY)),
              w.s([w.s([], 'fveq2', '( j = z -> ( G ` j ) = ( G ` z ) )')], 'oveq2d', '( j = z -> ( ( G ` %s ) x. ( G ` j ) ) = ( ( G ` %s ) x. ( G ` z ) ) )' % (PY, PY))],
             'eqeq12d', '( j = z -> ( %s <-> %s ) )' % (MB(PY, 'j'), MB(PY, 'z')))
    mz = sc([r1, r2, lift(w, gm, c), pyn, zn], 'rspc2dv', MB(PY, 'z'))
    e1 = sc([sp1], 'fveq2d', '( G ` prod_ p e. ( y u. { z } ) p ) = ( G ` ( %s x. z ) )' % PY)
    e2 = sc([e1, mz], 'eqtrd', '( G ` prod_ p e. ( y u. { z } ) p ) = ( ( G ` %s ) x. ( G ` z ) )' % PY)
    ct = '( %s /\\ %s )' % (c, PS('y'))
    th = w.s([], 'simpr', '( %s -> %s )' % (ct, PS('y')))
    e3 = w.s([th], 'oveq1d', '( %s -> ( ( G ` %s ) x. ( G ` z ) ) = ( prod_ p e. y ( G ` p ) x. ( G ` z ) ) )' % (ct, PY))
    e4 = w.s([lift(w, e2, ct), e3], 'eqtrd', '( %s -> ( G ` prod_ p e. ( y u. { z } ) p ) = ( prod_ p e. y ( G ` p ) x. ( G ` z ) ) )' % ct)
    e5 = w.s([e4, lift(w, sp2, ct)], 'eqtr4d', '( %s -> %s )' % (ct, PS('( y u. { z } )')))
    stp = w.s([e5], 'ex', '( %s -> ( %s -> %s ) )' % (c, PS('y'), PS('( y u. { z } )')))
    w.qed([cgs['(/)'], cgs['y'], cgs['( y u. { z } )'], cgs['A'], base, stp, af], 'findcard2d', STATEMENTS['z5mulprod'])
    return w


def z5cxpprod():
    w = W('z5cxpprod', "Lean natCast_prod_cpow: ( prod_ p e. A p ) ^c S = prod_ p e. A ( p ^c S ) for a finite set A of positive integers "
                       "(z5mulprod at n |-> n ^c S, multiplicative by mulcxp).")
    ante = '( ( A e. Fin /\\ A C_ NN ) /\\ S e. CC )'
    st = mkst(w, ante)
    af = st([], 'simpll', 'A e. Fin'); an = st([], 'simplr', 'A C_ NN'); sc_ = st([], 'simpr', 'S e. CC')
    G = '( n e. NN |-> ( n ^c S ) )'
    a = '( %s /\\ n e. NN )' % ante
    sa = mkst(w, a)
    nc = sa([sa([], 'simpr', 'n e. NN')], 'nncnd', 'n e. CC')
    cx = sa([nc, lift(w, sc_, a)], 'cxpcld', '( n ^c S ) e. CC')
    gf = st([cx], 'fmpttd', '%s : NN --> CC' % G)
    def val(ante_, T, mem):
        return mpv(w, ante_, 'n', 'NN', '( n ^c S )', T, mem)[0]
    one = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % ante)
    g1 = st([val(ante, '1', one), st([sc_, w.inst('1cxp')], 'syl', '( 1 ^c S ) = 1')], 'eqtrd', '( %s ` 1 ) = 1' % G)
    b = '( %s /\\ ( i e. NN /\\ j e. NN ) )' % ante
    sb = mkst(w, b)
    inn = sb([], 'simprl', 'i e. NN'); jnn = sb([], 'simprr', 'j e. NN')
    ijn = sb([inn, jnn], 'nnmulcld', '( i x. j ) e. NN')
    v1 = val(b, '( i x. j )', ijn); vi = val(b, 'i', inn); vj = val(b, 'j', jnn)
    ir = sb([inn], 'nnred', 'i e. RR'); jr = sb([jnn], 'nnred', 'j e. RR')
    i0 = sb([sb([inn], 'nnrpd', 'i e. RR+')], 'rpge0d', '0 <_ i'); j0 = sb([sb([jnn], 'nnrpd', 'j e. RR+')], 'rpge0d', '0 <_ j')
    mc = sb([sb([ir, i0], 'jca', '( i e. RR /\\ 0 <_ i )'), sb([jr, j0], 'jca', '( j e. RR /\\ 0 <_ j )'), lift(w, sc_, b), w.inst('mulcxp')], 'syl3anc',
            '( ( i x. j ) ^c S ) = ( ( i ^c S ) x. ( j ^c S ) )')
    m1 = sb([v1, mc], 'eqtrd', '( %s ` ( i x. j ) ) = ( ( i ^c S ) x. ( j ^c S ) )' % G)
    m2 = sb([m1, sb([vi, vj], 'oveq12d', '( ( %s ` i ) x. ( %s ` j ) ) = ( ( i ^c S ) x. ( j ^c S ) )' % (G, G))], 'eqtr4d',
            '( %s ` ( i x. j ) ) = ( ( %s ` i ) x. ( %s ` j ) )' % (G, G, G))
    gm = st([m2], 'ralrimivva', MUL(G))
    hg = st([gf, g1, gm], '3jca', '( %s : NN --> CC /\\ ( %s ` 1 ) = 1 /\\ %s )' % (G, G, MUL(G)))
    mp = st([hg, st([af, an], 'jca', '( A e. Fin /\\ A C_ NN )'), w.inst('z5mulprod')], 'syl2anc',
            '( %s ` prod_ p e. A p ) = prod_ p e. A ( %s ` p )' % (G, G))
    pnn = st([af, w.s([w.s([an], 'adantr', '( ( %s /\\ p e. A ) -> A C_ NN )' % ante), w.s([], 'simpr', '( ( %s /\\ p e. A ) -> p e. A )' % ante)], 'sseldd',
                      '( ( %s /\\ p e. A ) -> p e. NN )' % ante)], 'fprodnncl', 'prod_ p e. A p e. NN')
    lv = val(ante, 'prod_ p e. A p', pnn)
    c = '( %s /\\ p e. A )' % ante
    pc = w.s([w.s([an], 'adantr', '( %s -> A C_ NN )' % c), w.s([], 'simpr', '( %s -> p e. A )' % c)], 'sseldd', '( %s -> p e. NN )' % c)
    rv = st([val(c, 'p', pc)], 'prodeq2dv', 'prod_ p e. A ( %s ` p ) = prod_ p e. A ( p ^c S )' % G)
    ch = st([st([lv], 'eqcomd', '( prod_ p e. A p ^c S ) = ( %s ` prod_ p e. A p )' % G), mp], 'eqtrd', '( prod_ p e. A p ^c S ) = prod_ p e. A ( %s ` p )' % G)
    w.qed([ch, rv], 'eqtrd', STATEMENTS['z5cxpprod'])
    return w


from cl import split_imp as _si, split_imp
FCH = _si(STATEMENTS['z5fconv'])[0]


def z5fconv():
    w = W('z5fconv', "Lean LSeries_convolution' for a finitely supported first factor: if A vanishes off the finite set F of positive "
                     "integers and B is bounded, then sum_ n ( A * B ) ( n ) n ^ -Z converges to ( sum_ d e. F A ( d ) d ^ -Z ) "
                     "( sum_ k B ( k ) k ^ -Z ) for Re Z > 1 (C7b's dconvlim; the log-average bound and the convergence of the "
                     "A-series come from the finite support).")
    ante = FCH
    st = mkst(w, ante)
    h1 = st([], 'simpll', '( A : NN --> CC /\\ F e. Fin /\\ F C_ NN )')
    af = st([h1], 'simp1d', 'A : NN --> CC'); ff = st([h1], 'simp2d', 'F e. Fin'); fn = st([h1], 'simp3d', 'F C_ NN')
    az = st([], 'simplr', 'A. l e. ( NN \\ F ) ( A ` l ) = 0')
    hb = st([], 'simprl', '( B : NN --> CC /\\ C e. RR /\\ A. m e. NN ( abs ` ( B ` m ) ) <_ C )')
    hz = st([], 'simprr', '( Z e. CC /\\ 1 < ( Re ` Z ) )')
    zc = st([hz], 'simpld', 'Z e. CC')
    T = lambda d: '( ( abs ` ( A ` %s ) ) / %s )' % (d, d)
    K = 'sum_ d e. F %s' % T('d')

    def tfacts(a, dn):
        """( a -> T(d) e. RR ), ( a -> 0 <_ T(d) ) from dn: ( a -> d e. NN )"""
        sa = mkst(w, a)
        ad = sa([lift(w, af, a), dn], 'ffvelcdmd', '( A ` d ) e. CC')
        ab = sa([ad], 'abscld', '( abs ` ( A ` d ) ) e. RR')
        drp = sa([dn], 'nnrpd', 'd e. RR+')
        tr = sa([ab, drp], 'rerpdivcld', '%s e. RR' % T('d'))
        t0 = sa([ab, drp, sa([ad], 'absge0d', '0 <_ ( abs ` ( A ` d ) )')], 'divge0d', '0 <_ %s' % T('d'))
        return tr, t0, ad
    aF = '( %s /\\ d e. F )' % ante
    dnF = w.s([w.s([fn], 'adantr', '( %s -> F C_ NN )' % aF), w.s([], 'simpr', '( %s -> d e. F )' % aF)], 'sseldd', '( %s -> d e. NN )' % aF)
    trF, t0F, adF = tfacts(aF, dnF)
    kr = st([ff, trF], 'fsumrecl', '%s e. RR' % K)
    # the log-average bound
    b = '( ( %s /\\ y e. RR ) /\\ 1 <_ y )' % ante
    sb = mkst(w, b)
    I = '( 1 ... ( |_ ` y ) )'; U = '( %s u. F )' % I
    iss = w.s([w.s([], 'fz1ssnn', '%s C_ NN' % I)], 'a1i', '( %s -> %s C_ NN )' % (b, I))
    un = sb([sb([iss, lift(w, fn, b)], 'jca', '( %s C_ NN /\\ F C_ NN )' % I), w.s([], 'unss', '( ( %s C_ NN /\\ F C_ NN ) <-> %s C_ NN )' % (I, U))], 'sylib', '%s C_ NN' % U)
    uf = sb([sb([], 'fzfid', '%s e. Fin' % I), lift(w, ff, b), w.inst('unfi')], 'syl2anc', '%s e. Fin' % U)
    aU = '( %s /\\ d e. %s )' % (b, U)
    dnU = w.s([w.s([un], 'adantr', '( %s -> %s C_ NN )' % (aU, U)), w.s([], 'simpr', '( %s -> d e. %s )' % (aU, U))], 'sseldd', '( %s -> d e. NN )' % aU)
    trU, t0U, adU = tfacts(aU, dnU)
    s1 = sb([uf, trU, t0U, w.s([w.s([], 'ssun1', '%s C_ %s' % (I, U))], 'a1i', '( %s -> %s C_ %s )' % (b, I, U))], 'fsumless',
            'sum_ d e. %s %s <_ sum_ d e. %s %s' % (I, T('d'), U, T('d')))
    aB = '( %s /\\ d e. F )' % b
    dnB = w.s([w.s([lift(w, fn, b)], 'adantr', '( %s -> F C_ NN )' % aB), w.s([], 'simpr', '( %s -> d e. F )' % aB)], 'sseldd', '( %s -> d e. NN )' % aB)
    trB, t0B, adB = tfacts(aB, dnB)
    aD = '( %s /\\ d e. ( %s \\ F ) )' % (b, U)
    sD = mkst(w, aD)
    dU = sD([sD([], 'simpr', 'd e. ( %s \\ F )' % U)], 'eldifad', 'd e. %s' % U)
    dnF_ = sD([sD([], 'simpr', 'd e. ( %s \\ F )' % U)], 'eldifbd', '-. d e. F')
    dnD = sD([lift(w, un, aD), dU], 'sseldd', 'd e. NN')
    dNF = sD([dnD, dnF_], 'eldifd', 'd e. ( NN \\ F )')
    a0 = sD([w.s([w.s([], 'fveq2', '( l = d -> ( A ` l ) = ( A ` d ) )')], 'eqeq1d', '( l = d -> ( ( A ` l ) = 0 <-> ( A ` d ) = 0 ) )'),
             lift(w, az, aD), dNF], 'rspcdva', '( A ` d ) = 0')
    z1 = sD([sD([a0], 'fveq2d', '( abs ` ( A ` d ) ) = ( abs ` 0 )'), w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % aD)], 'eqtrd',
            '( abs ` ( A ` d ) ) = 0')
    z2 = sD([z1], 'oveq1d', '%s = ( 0 / d )' % T('d'))
    z3 = sD([z2, sD([sD([dnD], 'nncnd', 'd e. CC'), sD([dnD], 'nnne0d', 'd =/= 0')], 'div0d', '( 0 / d ) = 0')], 'eqtrd', '%s = 0' % T('d'))
    s2 = sb([w.s([w.s([], 'ssun2', 'F C_ %s' % U)], 'a1i', '( %s -> F C_ %s )' % (b, U)), w.s([trB], 'recnd', '( %s -> %s e. CC )' % (aB, T('d'))), z3, uf], 'fsumss',
            '%s = sum_ d e. %s %s' % (K, U, T('d')))
    yr = sb([], 'simplr', 'y e. RR'); y1 = sb([], 'simpr', '1 <_ y')
    lg = sb([yr, y1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` y )')
    ypos = sb([sb([], '0red', '0 e. RR'), sb([], '1red', '1 e. RR'), yr, w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % b), y1], 'ltletrd', '0 < y')
    lgr = sb([sb([yr, ypos], 'elrpd', 'y e. RR+')], 'relogcld', '( log ` y ) e. RR')
    s3 = lin.linarith(w, b, [lg], '%s <_ ( ( log ` y ) + %s )' % (K, K), leaves={K: ('RR', lift(w, kr, b)), '( log ` y )': ('RR', lgr)}, atoms=[K, '( log ` y )'])
    s4 = sb([s1, sb([s2], 'eqcomd', 'sum_ d e. %s %s = %s' % (U, T('d'), K))], 'breqtrd', 'sum_ d e. %s %s <_ %s' % (I, T('d'), K))
    aI = '( %s /\\ d e. %s )' % (b, I)
    dnI = w.s([w.s([iss], 'adantr', '( %s -> %s C_ NN )' % (aI, I)), w.s([], 'simpr', '( %s -> d e. %s )' % (aI, I))], 'sseldd', '( %s -> d e. NN )' % aI)
    trI, t0I, adI = tfacts(aI, dnI)
    sIr = sb([sb([], 'fzfid', '%s e. Fin' % I), trI], 'fsumrecl', 'sum_ d e. %s %s e. RR' % (I, T('d')))
    krb = lift(w, kr, b)
    s5 = sb([sIr, krb, sb([lgr, krb], 'readdcld', '( ( log ` y ) + %s ) e. RR' % K), s4, s3], 'letrd', 'sum_ d e. %s %s <_ ( ( log ` y ) + %s )' % (I, T('d'), K))
    LAVb = '( 1 <_ y -> sum_ d e. %s %s <_ ( ( log ` y ) + %s ) )' % (I, T('d'), K)
    lav = st([w.s([s5], 'ex', '( ( %s /\\ y e. RR ) -> %s )' % (ante, LAVb))], 'ralrimiva', 'A. y e. RR %s' % LAVb)
    # the A-series converges
    X = lambda k: '( ( A ` %s ) x. ( %s ^c -u Z ) )' % (k, k)
    MA = '( n e. NN |-> %s )' % X('n')
    ak = '( %s /\\ k e. NN )' % ante
    sk = mkst(w, ak)
    knn = sk([], 'simpr', 'k e. NN')
    mv, _v = mpv(w, ak, 'n', 'NN', X('n'), 'k', knn)
    xk = sk([sk([lift(w, af, ak), knn], 'ffvelcdmd', '( A ` k ) e. CC'), sk([sk([knn], 'nncnd', 'k e. CC'), sk([lift(w, zc, ak)], 'negcld', '-u Z e. CC')], 'cxpcld',
                                                                                                              '( k ^c -u Z ) e. CC')], 'mulcld', '%s e. CC' % X('k'))
    IFX = 'if ( k e. F , %s , 0 )' % X('k')
    at = '( %s /\\ k e. F )' % ak
    it = w.s([w.s([], 'simpr', '( %s -> k e. F )' % at)], 'iftrued', '( %s -> %s = %s )' % (at, IFX, X('k')))
    ct = w.s([w.s([mv], 'adantr', '( %s -> ( %s ` k ) = %s )' % (at, MA, X('k'))), it], 'eqtr4d', '( %s -> ( %s ` k ) = %s )' % (at, MA, IFX))
    af_ = '( %s /\\ -. k e. F )' % ak
    sf = mkst(w, af_)
    kNF = sf([sf([], 'simplr', 'k e. NN'), sf([], 'simpr', '-. k e. F')], 'eldifd', 'k e. ( NN \\ F )')
    # ( A ` k ) = 0 for k e. ( NN \ F ): r19.21bi on the restricted quantifier
    ak0 = sf([w.s([w.s([], 'fveq2', '( l = k -> ( A ` l ) = ( A ` k ) )')], 'eqeq1d', '( l = k -> ( ( A ` l ) = 0 <-> ( A ` k ) = 0 ) )'), lift(w, az, af_), kNF], 'rspcdva', '( A ` k ) = 0')
    xf = sf([sf([ak0], 'oveq1d', '%s = ( 0 x. ( k ^c -u Z ) )' % X('k')), sf([lift(w, sk([sk([knn], 'nncnd', 'k e. CC'), sk([lift(w, zc, ak)], 'negcld', '-u Z e. CC')],
                                                                                   'cxpcld', '( k ^c -u Z ) e. CC'), af_)], 'mul02d', '( 0 x. ( k ^c -u Z ) ) = 0')],
            'eqtrd', '%s = 0' % X('k'))
    if_ = sf([sf([], 'simpr', '-. k e. F')], 'iffalsed', '%s = 0' % IFX)
    cf = sf([sf([lift(w, mv, af_), xf], 'eqtrd', '( %s ` k ) = 0' % MA), if_], 'eqtr4d', '( %s ` k ) = %s' % (MA, IFX))
    mvif = w.s([ct, cf], 'pm2.61dan', '( %s -> ( %s ` k ) = %s )' % (ak, MA, IFX))
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ante)
    akF = '( %s /\\ k e. F )' % ante
    kF = w.s([w.s([fn], 'adantr', '( %s -> F C_ NN )' % akF), w.s([], 'simpr', '( %s -> k e. F )' % akF)], 'sseldd', '( %s -> k e. NN )' % akF)
    xkF = w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % akF), kF], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % akF),
               w.s([w.s([kF], 'nncnd', '( %s -> k e. CC )' % akF), w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % akF)], 'negcld', '( %s -> -u Z e. CC )' % akF)],
                   'cxpcld', '( %s -> ( k ^c -u Z ) e. CC )' % akF)], 'mulcld', '( %s -> %s e. CC )' % (akF, X('k')))
    acv = w.s([nnz, one, ff, fn, mvif, xkF], 'fsumcvg3', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ante, MA))
    # dconvlim
    LAV = '( A : NN --> CC /\\ %s e. RR /\\ A. y e. RR %s )' % (K, LAVb)
    hl = st([af, kr, lav], '3jca', LAV)
    hh = st([st([hl, hb], 'jca', '( %s /\\ ( B : NN --> CC /\\ C e. RR /\\ A. m e. NN ( abs ` ( B ` m ) ) <_ C ) )' % LAV),
             st([hz, acv], 'jca', '( ( Z e. CC /\\ 1 < ( Re ` Z ) ) /\\ seq 1 ( + , %s ) e. dom ~~> )' % MA)], 'jca',
            '( ( %s /\\ ( B : NN --> CC /\\ C e. RR /\\ A. m e. NN ( abs ` ( B ` m ) ) <_ C ) ) /\\ ( ( Z e. CC /\\ 1 < ( Re ` Z ) ) /\\ seq 1 ( + , %s ) e. dom ~~> ) )' % (LAV, MA))
    MC = '( n e. NN |-> %s )' % CV('n')
    SA = 'sum_ k e. NN %s' % X('k'); SBs = 'sum_ k e. NN ( ( B ` k ) x. ( k ^c -u Z ) )'
    dc = st([hh, w.inst('dconvlim')], 'syl', '( seq 1 ( + , %s ) e. dom ~~> /\\ sum_ k e. NN %s = ( %s x. %s ) )' % (MC, CV('k'), SA, SBs))
    cvg = st([dc], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % MC)
    val = st([dc], 'simprd', 'sum_ k e. NN %s = ( %s x. %s )' % (CV('k'), SA, SBs))
    # values of the convolution series
    mvc, _ = mpv(w, ak, 'n', 'NN', CV('n'), 'k', knn)
    ad_ = '( %s /\\ d e. %s )' % (ak, DV('k'))
    dnd, ddk = dvparts(w, ad_, w.s([], 'simpr', '( %s -> d e. %s )' % (ad_, DV('k'))), 'k')
    kd = w.s([ddk, w.s([w.s([], 'simplr', '( %s -> k e. NN )' % ad_), dnd, w.inst('nndivdvds')], 'syl2anc', '( %s -> ( d || k <-> ( k / d ) e. NN ) )' % ad_)], 'mpbid',
             '( %s -> ( k / d ) e. NN )' % ad_)
    hbB = w.s([w.s([hb], 'adantr', '( %s -> ( B : NN --> CC /\\ C e. RR /\\ A. m e. NN ( abs ` ( B ` m ) ) <_ C ) )' % ak)], 'simp1d', '( %s -> B : NN --> CC )' % ak)
    tcd = w.s([w.s([lift(w, af, ad_), dnd], 'ffvelcdmd', '( %s -> ( A ` d ) e. CC )' % ad_), w.s([lift(w, hbB, ad_), kd], 'ffvelcdmd', '( %s -> ( B ` ( k / d ) ) e. CC )' % ad_)],
              'mulcld', '( %s -> ( ( A ` d ) x. ( B ` ( k / d ) ) ) e. CC )' % ad_)
    fc = sk([sk([knn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DV('k')), tcd], 'fsumcl', 'sum_ d e. %s ( ( A ` d ) x. ( B ` ( k / d ) ) ) e. CC' % DV('k'))
    cvc = sk([fc, sk([sk([knn], 'nncnd', 'k e. CC'), sk([lift(w, zc, ak)], 'negcld', '-u Z e. CC')], 'cxpcld', '( k ^c -u Z ) e. CC')], 'mulcld', '%s e. CC' % CV('k'))
    lim = w.s([nnz, one, mvc, cvc, cvg], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> sum_ k e. NN %s )' % (ante, MC, CV('k')))
    # sum over NN of the A-series = sum over F
    aNF = '( %s /\\ k e. ( NN \\ F ) )' % ante
    rb2 = w.s([w.s([w.s([], 'fveq2', '( l = k -> ( A ` l ) = ( A ` k ) )')], 'eqeq1d', '( l = k -> ( ( A ` l ) = 0 <-> ( A ` k ) = 0 ) )'), lift(w, az, aNF), w.s([], 'simpr', '( %s -> k e. ( NN \\ F ) )' % aNF)], 'rspcdva', '( %s -> ( A ` k ) = 0 )' % aNF)
    knf = w.s([w.s([], 'simpr', '( %s -> k e. ( NN \\ F ) )' % aNF)], 'eldifad', '( %s -> k e. NN )' % aNF)
    x0 = w.s([w.s([rb2], 'oveq1d', '( %s -> %s = ( 0 x. ( k ^c -u Z ) ) )' % (aNF, X('k'))),
              w.s([w.s([w.s([knf], 'nncnd', '( %s -> k e. CC )' % aNF), w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % aNF)], 'negcld', '( %s -> -u Z e. CC )' % aNF)], 'cxpcld',
                       '( %s -> ( k ^c -u Z ) e. CC )' % aNF)], 'mul02d', '( %s -> ( 0 x. ( k ^c -u Z ) ) = 0 )' % aNF)], 'eqtrd', '( %s -> %s = 0 )' % (aNF, X('k')))
    nns = w.s([w.s([nnz], 'eqimssi', 'NN C_ ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN C_ ( ZZ>= ` 1 ) )' % ante)
    ss = st([fn, xkF, x0, nns], 'sumss', 'sum_ k e. F %s = %s' % (X('k'), SA))
    cb = w.s([w.s([w.s([], 'fveq2', '( k = d -> ( A ` k ) = ( A ` d ) )'), w.s([w.s([], 'id', '( k = d -> k = d )')], 'oveq1d', '( k = d -> ( k ^c -u Z ) = ( d ^c -u Z ) )')],
                  'oveq12d', '( k = d -> %s = %s )' % (X('k'), X('d')))], 'cbvsumv', 'sum_ k e. F %s = sum_ d e. F %s' % (X('k'), X('d')))
    sf2 = st([w.s([cb], 'a1i', '( %s -> sum_ k e. F %s = sum_ d e. F %s )' % (ante, X('k'), X('d'))), ss], 'eqtr3d', 'sum_ d e. F %s = %s' % (X('d'), SA))
    v2 = st([val, st([sf2], 'oveq1d', '( sum_ d e. F %s x. %s ) = ( %s x. %s )' % (X('d'), SBs, SA, SBs))], 'eqtr4d',
            'sum_ k e. NN %s = ( sum_ d e. F %s x. %s )' % (CV('k'), X('d'), SBs))
    w.qed([lim, v2], 'breqtrd', STATEMENTS['z5fconv'])
    return w


def kl(w, ante, stp, X, G):
    """( ante -> A. l e. X ( G ` l ) = 0 ) from stp: ( ante -> A. k e. X ( G ` k ) = 0 )"""
    c = w.s([w.s([w.s([], 'fveq2', '( k = l -> ( %s ` k ) = ( %s ` l ) )' % (G, G))], 'eqeq1d', '( k = l -> ( ( %s ` k ) = 0 <-> ( %s ` l ) = 0 ) )' % (G, G))],
            'cbvralvw', '( A. k e. %s ( %s ` k ) = 0 <-> A. l e. %s ( %s ` l ) = 0 )' % (X, G, X, G))
    return w.s([stp, c], 'sylib', '( %s -> A. l e. %s ( %s ` l ) = 0 )' % (ante, X, G))


BB = lambda p: '( ( ( %s - 1 ) x. ( C ` %s ) ) x. ( %s ^c -u S ) )' % (FMP(p), p, p)


def bbc(w, a, pnn, cf, sc, p='p'):
    """( a -> BB(p) e. CC ) from pnn: ( a -> p e. NN ), cf: ( a -> C : NN --> CC ), sc: ( a -> S e. CC )"""
    sa = mkst(w, a)
    f1 = sa([sa([fmpre(w, a, pnn, p)], 'recnd', '%s e. CC' % FMP(p)), sa([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % FMP(p))
    c = sa([cf, pnn], 'ffvelcdmd', '( C ` %s ) e. CC' % p)
    x = sa([sa([pnn], 'nncnd', '%s e. CC' % p), sa([sc], 'negcld', '-u S e. CC')], 'cxpcld', '( %s ^c -u S ) e. CC' % p)
    return sa([sa([f1, c], 'mulcld', '( ( %s - 1 ) x. ( C ` %s ) ) e. CC' % (FMP(p), p)), x], 'mulcld', '%s e. CC' % BB(p))


def z5gkeul():
    w = W('z5gkeul', "Lean LSeries_Gker_char (its finite sum): sum_ d | T G_T ( d ) chi ( d ) d ^ -S = prod_ p | T ( 1 + ( f ( p ) - 1 ) chi ( p ) p ^ -S ) "
                     "for squarefree T and a completely multiplicative chi (every divisor d of T is squarefree, d = prod_ p | d p; the engine z5sqfeul).")
    ante = '( %s /\\ ( %s /\\ S e. CC ) )' % (SQF('T'), CHR)
    st = mkst(w, ante)
    tn = st([], 'simpll', 'T e. NN'); t0 = st([], 'simplr', '( mmu ` T ) =/= 0'); chr_ = st([], 'simprl', CHR); sc = st([], 'simprr', 'S e. CC')
    cf, c1, cm = chrparts(w, ante, chr_)
    PD = 'prod_ p e. %s ( %s - 1 )' % (PF('d'), FMP('p'))
    PC = 'prod_ p e. %s ( C ` p )' % PF('d')
    PX = 'prod_ p e. %s ( p ^c -u S )' % PF('d')
    PB = 'prod_ p e. %s %s' % (PF('d'), BB('p'))
    TM = '( ( %s x. ( C ` d ) ) x. ( d ^c -u S ) )' % GK('T', 'd')
    a = '( %s /\\ d e. %s )' % (ante, DV('T'))
    sa = mkst(w, a)
    dn, ddT = dvparts(w, a, sa([], 'simpr', 'd e. %s' % DV('T')), 'T')
    mud = sa([lift(w, tn, a), lift(w, t0, a), dn, ddT, w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` d ) =/= 0')
    g1 = sa([ddT], 'iftrued', '%s = %s' % (GK('T', 'd'), PD))
    sid = sa([dn, mud, w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = d' % PF('d'))
    pfin = sy(w, a, dn, 'pffinq', '%s e. Fin' % PF('d'))
    pnn = w.s([w.s([], 'ssrab2', '%s C_ Prime' % PF('d')), w.s([], 'prmssnn', 'Prime C_ NN')], 'sstri', '%s C_ NN' % PF('d'))
    pnnd = w.s([pnn], 'a1i', '( %s -> %s C_ NN )' % (a, PF('d')))
    hfa = sa([pfin, pnnd], 'jca', '( %s e. Fin /\\ %s C_ NN )' % (PF('d'), PF('d')))
    cp = sa([lift(w, chr_, a), hfa, w.inst('z5mulprod')], 'syl2anc', '( C ` prod_ p e. %s p ) = %s' % (PF('d'), PC))
    cd = sa([sa([sid], 'fveq2d', '( C ` prod_ p e. %s p ) = ( C ` d )' % PF('d')), cp], 'eqtr3d', '( C ` d ) = %s' % PC)
    ns = sa([lift(w, sc, a)], 'negcld', '-u S e. CC')
    xp = sa([hfa, ns, w.inst('z5cxpprod')], 'syl2anc', '( prod_ p e. %s p ^c -u S ) = %s' % (PF('d'), PX))
    xd = sa([sa([sid], 'oveq1d', '( prod_ p e. %s p ^c -u S ) = ( d ^c -u S )' % PF('d')), xp], 'eqtr3d', '( d ^c -u S ) = %s' % PX)
    tm1 = sa([sa([g1, cd], 'oveq12d', '( %s x. ( C ` d ) ) = ( %s x. %s )' % (GK('T', 'd'), PD, PC)), xd], 'oveq12d', '%s = ( ( %s x. %s ) x. %s )' % (TM, PD, PC, PX))
    b = '( %s /\\ p e. %s )' % (a, PF('d'))
    pb = sy(w, b, pp(w, b, w.s([], 'simpr', '( %s -> p e. %s )' % (b, PF('d')))), 'prmnn', 'p e. NN')
    sbb = mkst(w, b)
    f1 = sbb([sbb([fmpre(w, b, pb)], 'recnd', '%s e. CC' % FMP('p')), sbb([], '1cnd', '1 e. CC')], 'subcld', '( %s - 1 ) e. CC' % FMP('p'))
    cpb = sbb([lift(w, cf, b), pb], 'ffvelcdmd', '( C ` p ) e. CC')
    xpb = sbb([sbb([pb], 'nncnd', 'p e. CC'), lift(w, ns, b)], 'cxpcld', '( p ^c -u S ) e. CC')
    fc = sbb([f1, cpb], 'mulcld', '( ( %s - 1 ) x. ( C ` p ) ) e. CC' % FMP('p'))
    m1 = sa([pfin, f1, cpb], 'fprodmul', 'prod_ p e. %s ( ( %s - 1 ) x. ( C ` p ) ) = ( %s x. %s )' % (PF('d'), FMP('p'), PD, PC))
    m2 = sa([pfin, fc, xpb], 'fprodmul', '%s = ( prod_ p e. %s ( ( %s - 1 ) x. ( C ` p ) ) x. %s )' % (PB, PF('d'), FMP('p'), PX))
    m12 = sa([m2, sa([m1], 'oveq1d', '( prod_ p e. %s ( ( %s - 1 ) x. ( C ` p ) ) x. %s ) = ( ( %s x. %s ) x. %s )' % (PF('d'), FMP('p'), PX, PD, PC, PX))], 'eqtrd',
             '%s = ( ( %s x. %s ) x. %s )' % (PB, PD, PC, PX))
    IFB = 'if ( ( mmu ` d ) =/= 0 , %s , 0 )' % PB
    ib = sa([mud], 'iftrued', '%s = %s' % (IFB, PB))
    tv = sa([tm1, sa([ib, m12], 'eqtrd', '%s = ( ( %s x. %s ) x. %s )' % (IFB, PD, PC, PX))], 'eqtr4d', '%s = %s' % (TM, IFB))
    se = st([tv], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (DV('T'), TM, DV('T'), IFB))
    bp = '( %s /\\ p e. Prime )' % ante
    pnp = sy(w, bp, w.s([], 'simpr', '( %s -> p e. Prime )' % bp), 'prmnn', 'p e. NN')
    bc = bbc(w, bp, pnp, lift(w, cf, bp), lift(w, sc, bp))
    eng = w.s([tn, bc], 'z5sqfeul', '( %s -> sum_ d e. %s %s = prod_ p e. %s ( 1 + %s ) )' % (ante, DV('T'), IFB, PF('T'), BB('p')))
    w.qed([se, eng], 'eqtrd', STATEMENTS['z5gkeul'])
    return w


AG = '( e e. NN |-> ( %s x. ( C ` e ) ) )' % GK('T', 'e')


def z5chpsi():
    w = W('z5chpsi', "Step A of blueprint Lemma 3.1 (Lean LSeries_char_psi_eq, LSeriesSummable_char_psi): for squarefree T and Re S > 1, "
                     "sum_ n chi ( n ) psi_T ( n ) n ^ -S converges to eulerT ( T ) L ( S , chi ): chi psi_T = ( G_T chi ) * chi (z5psigk) and "
                     "the finite-support convolution z5fconv with the Euler value z5gkeul.")
    ante = '( %s /\\ ( ( %s /\\ %s ) /\\ %s ) )' % (SQF('T'), CHR, CB, SRE1)
    st = mkst(w, ante)
    sqt = st([], 'simpl', SQF('T'))
    tn = st([sqt], 'simpld', 'T e. NN'); t0 = st([sqt], 'simprd', '( mmu ` T ) =/= 0')
    chr_ = st([], 'simprll', CHR); cb = st([], 'simprlr', CB); hs = st([], 'simprr', SRE1)
    sc = st([hs], 'simpld', 'S e. CC')
    cf, c1, cm = chrparts(w, ante, chr_)
    # AG : NN --> CC
    ae = '( %s /\\ e e. NN )' % ante
    sae = mkst(w, ae)
    en = sae([], 'simpr', 'e e. NN')
    fin = sy(w, ae, en, 'pffinq', '%s e. Fin' % PF('e'))
    be = '( %s /\\ p e. %s )' % (ae, PF('e'))
    pbe = sy(w, be, pp(w, be, w.s([], 'simpr', '( %s -> p e. %s )' % (be, PF('e')))), 'prmnn', 'p e. NN')
    fbe = w.s([w.s([fmpre(w, be, pbe)], 'recnd', '( %s -> %s e. CC )' % (be, FMP('p'))), w.s([], '1cnd', '( %s -> 1 e. CC )' % be)], 'subcld',
              '( %s -> ( %s - 1 ) e. CC )' % (be, FMP('p')))
    pde = sae([fin, fbe], 'fprodcl', 'prod_ p e. %s ( %s - 1 ) e. CC' % (PF('e'), FMP('p')))
    gke = sae([pde, sae([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % GK('T', 'e'))
    age = sae([gke, sae([lift(w, cf, ae), en], 'ffvelcdmd', '( C ` e ) e. CC')], 'mulcld', '( %s x. ( C ` e ) ) e. CC' % GK('T', 'e'))
    agf = st([age], 'fmpttd', '%s : NN --> CC' % AG)
    dvf = sy(w, ante, tn, 'dvdsfi', '%s e. Fin' % DV('T'))
    dvn = w.s([w.s([], 'ssrab2', '%s C_ NN' % DV('T'))], 'a1i', '( %s -> %s C_ NN )' % (ante, DV('T')))
    # zero off DV(T)
    ak = '( %s /\\ k e. ( NN \\ %s ) )' % (ante, DV('T'))
    sk = mkst(w, ak)
    kn = sk([sk([], 'simpr', 'k e. ( NN \\ %s )' % DV('T'))], 'eldifad', 'k e. NN')
    knd = sk([sk([], 'simpr', 'k e. ( NN \\ %s )' % DV('T'))], 'eldifbd', '-. k e. %s' % DV('T'))
    e_ = '( %s /\\ k || T )' % ak
    ind = w.s([lift(w, kn, e_), w.s([], 'simpr', '( %s -> k || T )' % e_), w.s([eldv(w, 'T', 'k')], 'a1i', '( %s -> ( k e. %s <-> ( k e. NN /\\ k || T ) ) )' % (e_, DV('T')))],
              'mpbir2and', '( %s -> k e. %s )' % (e_, DV('T')))
    nkt = w.s([ind, lift(w, knd, e_)], 'pm2.65da', '( %s -> -. k || T )' % ak)
    gk0 = sk([nkt], 'iffalsed', '%s = 0' % GK('T', 'k'))
    agv, _ = mpv(w, ak, 'e', 'NN', '( %s x. ( C ` e ) )' % GK('T', 'e'), 'k', kn)
    ag0 = sk([agv, sk([sk([gk0], 'oveq1d', '( %s x. ( C ` k ) ) = ( 0 x. ( C ` k ) )' % GK('T', 'k')),
                       sk([sk([lift(w, cf, ak), kn], 'ffvelcdmd', '( C ` k ) e. CC')], 'mul02d', '( 0 x. ( C ` k ) ) = 0')], 'eqtrd', '( %s x. ( C ` k ) ) = 0' % GK('T', 'k'))],
             'eqtrd', '( %s ` k ) = 0' % AG)
    z0 = kl(w, ante, st([ag0], 'ralrimiva', 'A. k e. ( NN \\ %s ) ( %s ` k ) = 0' % (DV('T'), AG)), '( NN \\ %s )' % DV('T'), AG)
    cbm = w.s([w.s([w.s([w.s([], 'fveq2', '( j = m -> ( C ` j ) = ( C ` m ) )')], 'fveq2d', '( j = m -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` m ) ) )')], 'breq1d',
                   '( j = m -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` m ) ) <_ 1 ) )')], 'cbvralvw', '( %s <-> A. m e. NN ( abs ` ( C ` m ) ) <_ 1 )' % CB)
    cbm2 = st([cb, cbm], 'sylib', 'A. m e. NN ( abs ` ( C ` m ) ) <_ 1')
    H1 = '( ( %s : NN --> CC /\\ %s e. Fin /\\ %s C_ NN ) /\\ A. l e. ( NN \\ %s ) ( %s ` l ) = 0 )' % (AG, DV('T'), DV('T'), DV('T'), AG)
    H2 = '( ( C : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( C ` m ) ) <_ 1 ) /\\ %s )' % SRE1
    h1 = st([st([agf, dvf, dvn], '3jca', '( %s : NN --> CC /\\ %s e. Fin /\\ %s C_ NN )' % (AG, DV('T'), DV('T'))), z0], 'jca', H1)
    h2 = st([st([cf, st([], '1red', '1 e. RR'), cbm2], '3jca', '( C : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( C ` m ) ) <_ 1 )'), hs], 'jca', H2)
    CVg = lambda n: '( sum_ d e. %s ( ( %s ` d ) x. ( C ` ( %s / d ) ) ) x. ( %s ^c -u S ) )' % (DV(n), AG, n, n)
    SAd = 'sum_ d e. %s ( ( %s ` d ) x. ( d ^c -u S ) )' % (DV('T'), AG)
    fcv = st([st([h1, h2], 'jca', '( %s /\\ %s )' % (H1, H2)), w.inst('z5fconv')], 'syl',
             'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s )' % (CVg('n'), SAd, LS()))
    # the convolution is chi psi_T
    an = '( %s /\\ n e. NN )' % ante
    sn = mkst(w, an)
    nn = sn([], 'simpr', 'n e. NN')
    ad = '( %s /\\ d e. %s )' % (an, DV('n'))
    sd = mkst(w, ad)
    dn, ddn = dvparts(w, ad, sd([], 'simpr', 'd e. %s' % DV('n')), 'n')
    nd = sd([ddn, sd([lift(w, nn, ad), dn, w.inst('nndivdvds')], 'syl2anc', '( d || n <-> ( n / d ) e. NN )')], 'mpbid', '( n / d ) e. NN')
    agd, _ = mpv(w, ad, 'e', 'NN', '( %s x. ( C ` e ) )' % GK('T', 'e'), 'd', dn)
    mi = mulinst(w, ad, 'C', 'd', '( n / d )', lift(w, cm, ad), dn, nd)
    dc_ = sd([dn], 'nncnd', 'd e. CC'); nc_ = sd([lift(w, nn, ad)], 'nncnd', 'n e. CC')
    dcan = sd([nc_, dc_, sd([dn], 'nnne0d', 'd =/= 0')], 'divcan2d', '( d x. ( n / d ) ) = n')
    cn = sd([sd([sd([dcan], 'fveq2d', '( C ` ( d x. ( n / d ) ) ) = ( C ` n )'), mi], 'eqtr3d', '( C ` n ) = ( ( C ` d ) x. ( C ` ( n / d ) ) )')], 'eqcomd',
            '( ( C ` d ) x. ( C ` ( n / d ) ) ) = ( C ` n )')
    # G_T ( d ) in CC
    findd = sy(w, ad, dn, 'pffinq', '%s e. Fin' % PF('d'))
    bd = '( %s /\\ p e. %s )' % (ad, PF('d'))
    pbd = sy(w, bd, pp(w, bd, w.s([], 'simpr', '( %s -> p e. %s )' % (bd, PF('d')))), 'prmnn', 'p e. NN')
    fbd = w.s([w.s([fmpre(w, bd, pbd)], 'recnd', '( %s -> %s e. CC )' % (bd, FMP('p'))), w.s([], '1cnd', '( %s -> 1 e. CC )' % bd)], 'subcld', '( %s -> ( %s - 1 ) e. CC )' % (bd, FMP('p')))
    gkd = sd([sd([findd, fbd], 'fprodcl', 'prod_ p e. %s ( %s - 1 ) e. CC' % (PF('d'), FMP('p'))), sd([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % GK('T', 'd'))
    cdc = sd([lift(w, cf, ad), dn], 'ffvelcdmd', '( C ` d ) e. CC'); cndc = sd([lift(w, cf, ad), nd], 'ffvelcdmd', '( C ` ( n / d ) ) e. CC')
    t1 = sd([agd], 'oveq1d', '( ( %s ` d ) x. ( C ` ( n / d ) ) ) = ( ( %s x. ( C ` d ) ) x. ( C ` ( n / d ) ) )' % (AG, GK('T', 'd')))
    t2 = sd([gkd, cdc, cndc], 'mulassd', '( ( %s x. ( C ` d ) ) x. ( C ` ( n / d ) ) ) = ( %s x. ( ( C ` d ) x. ( C ` ( n / d ) ) ) )' % (GK('T', 'd'), GK('T', 'd')))
    t3 = sd([cn], 'oveq2d', '( %s x. ( ( C ` d ) x. ( C ` ( n / d ) ) ) ) = ( %s x. ( C ` n ) )' % (GK('T', 'd'), GK('T', 'd')))
    tt = sd([sd([t1, t2], 'eqtrd', '( ( %s ` d ) x. ( C ` ( n / d ) ) ) = ( %s x. ( ( C ` d ) x. ( C ` ( n / d ) ) ) )' % (AG, GK('T', 'd'))), t3], 'eqtrd',
            '( ( %s ` d ) x. ( C ` ( n / d ) ) ) = ( %s x. ( C ` n ) )' % (AG, GK('T', 'd')))
    s1 = sn([tt], 'sumeq2dv', 'sum_ d e. %s ( ( %s ` d ) x. ( C ` ( n / d ) ) ) = sum_ d e. %s ( %s x. ( C ` n ) )' % (DV('n'), AG, DV('n'), GK('T', 'd')))
    cnc = sn([lift(w, cf, an), nn], 'ffvelcdmd', '( C ` n ) e. CC')
    s2 = sn([sn([nn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DV('n')), cnc, gkd], 'fsummulc1',
            '( sum_ d e. %s %s x. ( C ` n ) ) = sum_ d e. %s ( %s x. ( C ` n ) )' % (DV('n'), GK('T', 'd'), DV('n'), GK('T', 'd')))
    pg = sn([lift(w, sqt, an), nn, w.inst('z5psigk')], 'syl2anc', '%s = sum_ d e. %s %s' % (PSI('T', 'n'), DV('n'), GK('T', 'd')))
    s3 = sn([pg], 'oveq1d', '( %s x. ( C ` n ) ) = ( sum_ d e. %s %s x. ( C ` n ) )' % (PSI('T', 'n'), DV('n'), GK('T', 'd')))
    gn_ = sn([lift(w, tn, an), nn, w.inst('gcdnncl')], 'syl2anc', '( T gcd n ) e. NN')
    psc = sn([fmpre(w, an, gn_, '( T gcd n )')], 'recnd', '%s e. CC' % PSI('T', 'n'))
    s4 = sn([psc, cnc], 'mulcomd', '( %s x. ( C ` n ) ) = ( ( C ` n ) x. %s )' % (PSI('T', 'n'), PSI('T', 'n')))
    SUMn = 'sum_ d e. %s ( ( %s ` d ) x. ( C ` ( n / d ) ) )' % (DV('n'), AG)
    c1_ = sn([s1, sn([sn([s2], 'eqcomd', 'sum_ d e. %s ( %s x. ( C ` n ) ) = ( sum_ d e. %s %s x. ( C ` n ) )' % (DV('n'), GK('T', 'd'), DV('n'), GK('T', 'd'))), s3], 'eqtr4d', 'sum_ d e. %s ( %s x. ( C ` n ) ) = ( %s x. ( C ` n ) )' % (DV('n'), GK('T', 'd'), PSI('T', 'n')))], 'eqtrd',
             '%s = ( %s x. ( C ` n ) )' % (SUMn, PSI('T', 'n')))
    c2_ = sn([c1_, s4], 'eqtrd', '%s = ( ( C ` n ) x. %s )' % (SUMn, PSI('T', 'n')))
    c3_ = sn([c2_], 'oveq1d', '%s = %s' % (CVg('n'), CPS('T', 'n')))
    me = st([c3_], 'mpteq2dva', '( n e. NN |-> %s ) = ( n e. NN |-> %s )' % (CVg('n'), CPS('T', 'n')))
    se = st([me], 'seqeq3d', 'seq 1 ( + , ( n e. NN |-> %s ) ) = seq 1 ( + , ( n e. NN |-> %s ) )' % (CVg('n'), CPS('T', 'n')))
    # the Euler value
    adT = '( %s /\\ d e. %s )' % (ante, DV('T'))
    dnT, _dd = dvparts(w, adT, w.s([], 'simpr', '( %s -> d e. %s )' % (adT, DV('T'))), 'T')
    agdT, _ = mpv(w, adT, 'e', 'NN', '( %s x. ( C ` e ) )' % GK('T', 'e'), 'd', dnT)
    sv = st([w.s([agdT], 'oveq1d', '( %s -> ( ( %s ` d ) x. ( d ^c -u S ) ) = ( ( %s x. ( C ` d ) ) x. ( d ^c -u S ) ) )' % (adT, AG, GK('T', 'd')))], 'sumeq2dv',
            '%s = sum_ d e. %s ( ( %s x. ( C ` d ) ) x. ( d ^c -u S ) )' % (SAd, DV('T'), GK('T', 'd')))
    gku = st([sqt, chr_, sc, w.inst('z5gkeul')], 'syl12anc', 'sum_ d e. %s ( ( %s x. ( C ` d ) ) x. ( d ^c -u S ) ) = %s' % (DV('T'), GK('T', 'd'), EU(PF('T'))))
    ev = st([st([sv, gku], 'eqtrd', '%s = %s' % (SAd, EU(PF('T'))))], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (SAd, LS(), EU(PF('T')), LS()))
    l1 = st([fcv, st([se], 'breq1d', '( seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s ) <-> seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s ) )'
                     % (CVg('n'), SAd, LS(), CPS('T', 'n'), SAd, LS()))], 'mpbid', 'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s )' % (CPS('T', 'n'), SAd, LS()))
    w.qed([l1, ev], 'breqtrd', STATEMENTS['z5chpsi'])
    return w


PMX = '( m e. NN |-> if ( m = D , X , 0 ) )'


def z5pmconv():
    w = W('z5pmconv', "Lean pointMass_convolution: the Dirichlet convolution of the point mass X at D with G at N is "
                      "if ( D | N , X G ( N / D ) , 0 ).")
    ante = '( ( D e. NN /\\ N e. NN ) /\\ ( X e. CC /\\ G : NN --> CC ) )'
    st = mkst(w, ante)
    dn = st([], 'simpll', 'D e. NN'); nn = st([], 'simplr', 'N e. NN'); xc = st([], 'simprl', 'X e. CC'); gf = st([], 'simprr', 'G : NN --> CC')
    Y = '( X x. ( G ` ( N / D ) ) )'
    IFd = 'if ( d = D , %s , 0 )' % Y
    a = '( %s /\\ d e. %s )' % (ante, DV('N'))
    sa = mkst(w, a)
    ddn, dvd = dvparts(w, a, sa([], 'simpr', 'd e. %s' % DV('N')), 'N')
    nd = sa([dvd, sa([lift(w, nn, a), ddn, w.inst('nndivdvds')], 'syl2anc', '( d || N <-> ( N / d ) e. NN )')], 'mpbid', '( N / d ) e. NN')
    ifc = sa([lift(w, xc, a), sa([], '0cnd', '0 e. CC')], 'ifcld', 'if ( d = D , X , 0 ) e. CC')
    pv, _ = mpv(w, a, 'm', 'NN', 'if ( m = D , X , 0 )', 'd', ddn, exs=sa([ifc], 'elexd', 'if ( d = D , X , 0 ) e. _V'))
    gnd = sa([lift(w, gf, a), nd], 'ffvelcdmd', '( G ` ( N / d ) ) e. CC')
    L = '( if ( d = D , X , 0 ) x. ( G ` ( N / d ) ) )'
    # case d = D
    at = '( %s /\\ d = D )' % a
    s_t = mkst(w, at)
    e1 = s_t([s_t([], 'simpr', 'd = D')], 'iftrued', 'if ( d = D , X , 0 ) = X')
    e2 = s_t([s_t([s_t([], 'simpr', 'd = D')], 'oveq2d', '( N / d ) = ( N / D )')], 'fveq2d', '( G ` ( N / d ) ) = ( G ` ( N / D ) )')
    e3 = s_t([e1, e2], 'oveq12d', '%s = %s' % (L, Y))
    e4 = s_t([s_t([], 'simpr', 'd = D')], 'iftrued', '%s = %s' % (IFd, Y))
    ct = s_t([e3, e4], 'eqtr4d', '%s = %s' % (L, IFd))
    af_ = '( %s /\\ -. d = D )' % a
    s_f = mkst(w, af_)
    f1 = s_f([s_f([], 'simpr', '-. d = D')], 'iffalsed', 'if ( d = D , X , 0 ) = 0')
    f2 = s_f([f1], 'oveq1d', '%s = ( 0 x. ( G ` ( N / d ) ) )' % L)
    f3 = s_f([f2, s_f([lift(w, gnd, af_)], 'mul02d', '( 0 x. ( G ` ( N / d ) ) ) = 0')], 'eqtrd', '%s = 0' % L)
    f4 = s_f([s_f([], 'simpr', '-. d = D')], 'iffalsed', '%s = 0' % IFd)
    cf = s_f([f3, f4], 'eqtr4d', '%s = %s' % (L, IFd))
    tv = w.s([ct, cf], 'pm2.61dan', '( %s -> %s = %s )' % (a, L, IFd))
    PMd = '( ( %s ` d ) x. ( G ` ( N / d ) ) )' % PMX
    tv2 = sa([sa([pv], 'oveq1d', '%s = %s' % (PMd, L)), tv], 'eqtrd', '%s = %s' % (PMd, IFd))
    se = st([tv2], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (DV('N'), PMd, DV('N'), IFd))
    dvf = sy(w, ante, nn, 'dvdsfi', '%s e. Fin' % DV('N'))
    RHS = 'if ( D || N , %s , 0 )' % Y
    # case D || N
    b = '( %s /\\ D || N )' % ante
    sb = mkst(w, b)
    dnd = sb([lift(w, nn, b), lift(w, dn, b), w.inst('nndivdvds')], 'syl2anc', '( D || N <-> ( N / D ) e. NN )')
    ndD = sb([sb([], 'simpr', 'D || N'), dnd], 'mpbid', '( N / D ) e. NN')
    yc = sb([lift(w, xc, b), sb([lift(w, gf, b), ndD], 'ffvelcdmd', '( G ` ( N / D ) ) e. CC')], 'mulcld', '%s e. CC' % Y)
    dind = sb([lift(w, dn, b), sb([], 'simpr', 'D || N'), w.s([eldv(w, 'N', 'D')], 'a1i', '( %s -> ( D e. %s <-> ( D e. NN /\\ D || N ) ) )' % (b, DV('N')))],
              'mpbir2and', 'D e. %s' % DV('N'))
    si = sb([w.s([], 'eqidd', '( d = D -> %s = %s )' % (Y, Y)), lift(w, dvf, b), dind, yc], 'sumite', 'sum_ d e. %s %s = %s' % (DV('N'), IFd, Y))
    rt = sb([sb([], 'simpr', 'D || N')], 'iftrued', '%s = %s' % (RHS, Y))
    cT = sb([si, rt], 'eqtr4d', 'sum_ d e. %s %s = %s' % (DV('N'), IFd, RHS))
    # case -. D || N
    c = '( %s /\\ -. D || N )' % ante
    sc = mkst(w, c)
    ac = '( %s /\\ d e. %s )' % (c, DV('N'))
    s_ac = mkst(w, ac)
    dnc, dvc = dvparts(w, ac, s_ac([], 'simpr', 'd e. %s' % DV('N')), 'N')
    ed = '( %s /\\ d = D )' % ac
    dD = w.s([lift(w, dvc, ed), w.s([w.s([], 'simpr', '( %s -> d = D )' % ed)], 'breq1d', '( %s -> ( d || N <-> D || N ) )' % ed)], 'mpbid', '( %s -> D || N )' % ed)
    ndD2 = w.s([dD, lift(w, sc([], 'simpr', '-. D || N'), ed)], 'pm2.65da', '( %s -> -. d = D )' % ac)
    z = s_ac([ndD2], 'iffalsed', '%s = 0' % IFd)
    s0 = sc([z], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s 0' % (DV('N'), IFd, DV('N')))
    sz = sc([sc([lift(w, dvf, c)], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (DV('N'), DV('N'))), w.inst('sumz')], 'syl', 'sum_ d e. %s 0 = 0' % DV('N'))
    rf = sc([sc([], 'simpr', '-. D || N')], 'iffalsed', '%s = 0' % RHS)
    cF = sc([sc([s0, sz], 'eqtrd', 'sum_ d e. %s %s = 0' % (DV('N'), IFd)), rf], 'eqtr4d', 'sum_ d e. %s %s = %s' % (DV('N'), IFd, RHS))
    cs = w.s([cT, cF], 'pm2.61dan', '( %s -> sum_ d e. %s %s = %s )' % (ante, DV('N'), IFd, RHS))
    w.qed([se, cs], 'eqtrd', STATEMENTS['z5pmconv'])
    return w


TTR = lambda D: TT(D, 'R')


def z5stepb():
    w = W('z5stepb', "Step B of blueprint Lemma 3.1 for one delta = D (Lean hpiece, LSeries_pointMass, LSeries_convolution'): the series of "
                     "the point mass chi ( D ) at D convolved with chi psi_t, t = t ( D ; R ), converges to chi ( D ) D ^ -S eulerT ( t ) L ( S , chi ).")
    ante = '( ( R e. NN /\\ D e. NN ) /\\ ( ( %s /\\ %s ) /\\ %s ) )' % (CHR, CB, SRE1)
    st = mkst(w, ante)
    rn = st([], 'simpll', 'R e. NN'); dn = st([], 'simplr', 'D e. NN')
    chr_ = st([], 'simprll', CHR); cb = st([], 'simprlr', CB); hs = st([], 'simprr', SRE1)
    sc = st([hs], 'simpld', 'S e. CC')
    cf, c1, cm = chrparts(w, ante, chr_)
    T = TTR('D')
    tq = st([rn, w.inst('z5tofsq')], 'syl', cns('z5tofsq'))
    tn = st([tq], 'simplld', '%s e. NN' % T); t0 = st([tq], 'simplrd', '( mmu ` %s ) =/= 0' % T)
    pfe = st([tq], 'simprd', '%s = %s' % (PF(T), QS('D', 'R')))
    cD = st([cf, dn], 'ffvelcdmd', '( C ` D ) e. CC')
    PMD = '( m e. NN |-> if ( m = D , ( C ` D ) , 0 ) )'
    BT = '( e e. NN |-> ( ( C ` e ) x. %s ) )' % PSI(T, 'e')
    # the point mass
    am = '( %s /\\ m e. NN )' % ante
    pmc = w.s([w.s([cD], 'adantr', '( %s -> ( C ` D ) e. CC )' % am), w.s([], '0cnd', '( %s -> 0 e. CC )' % am)], 'ifcld', '( %s -> if ( m = D , ( C ` D ) , 0 ) e. CC )' % am)
    pmf = st([pmc], 'fmpttd', '%s : NN --> CC' % PMD)
    snf = w.s([w.s([], 'snfi', '{ D } e. Fin')], 'a1i', '( %s -> { D } e. Fin )' % ante)
    sns = st([dn], 'snssd', '{ D } C_ NN')
    ak = '( %s /\\ k e. ( NN \\ { D } ) )' % ante
    sk = mkst(w, ak)
    kparts = sk([sk([], 'simpr', 'k e. ( NN \\ { D } )'), w.s([], 'eldifsn', '( k e. ( NN \\ { D } ) <-> ( k e. NN /\\ k =/= D ) )')], 'sylib', '( k e. NN /\\ k =/= D )')
    kn = sk([kparts], 'simpld', 'k e. NN'); kne = sk([kparts], 'simprd', 'k =/= D')
    ifk = sk([lift(w, cD, ak), sk([], '0cnd', '0 e. CC')], 'ifcld', 'if ( k = D , ( C ` D ) , 0 ) e. CC')
    pv, _ = mpv(w, ak, 'm', 'NN', 'if ( m = D , ( C ` D ) , 0 )', 'k', kn, exs=sk([ifk], 'elexd', 'if ( k = D , ( C ` D ) , 0 ) e. _V'))
    pk0 = sk([pv, sk([sk([kne], 'neneqd', '-. k = D')], 'iffalsed', 'if ( k = D , ( C ` D ) , 0 ) = 0')], 'eqtrd', '( %s ` k ) = 0' % PMD)
    z0 = kl(w, ante, st([pk0], 'ralrimiva', 'A. k e. ( NN \\ { D } ) ( %s ` k ) = 0' % PMD), '( NN \\ { D } )', PMD)
    # B = chi psi_t, bounded by t
    ae = '( %s /\\ e e. NN )' % ante
    se = mkst(w, ae)
    en = se([], 'simpr', 'e e. NN')
    gte = se([lift(w, tn, ae), en, w.inst('gcdnncl')], 'syl2anc', '( %s gcd e ) e. NN' % T)
    pse = se([fmpre(w, ae, gte, '( %s gcd e )' % T)], 'recnd', '%s e. CC' % PSI(T, 'e'))
    cee = se([lift(w, cf, ae), en], 'ffvelcdmd', '( C ` e ) e. CC')
    bte = se([cee, pse], 'mulcld', '( ( C ` e ) x. %s ) e. CC' % PSI(T, 'e'))
    btf = st([bte], 'fmpttd', '%s : NN --> CC' % BT)
    tr = st([tn], 'nnred', '%s e. RR' % T)
    amm = '( %s /\\ m e. NN )' % ante
    sm = mkst(w, amm)
    mn = sm([], 'simpr', 'm e. NN')
    bv, _ = mpv(w, amm, 'e', 'NN', '( ( C ` e ) x. %s )' % PSI(T, 'e'), 'm', mn)
    gtm = sm([lift(w, tn, amm), mn, w.inst('gcdnncl')], 'syl2anc', '( %s gcd m ) e. NN' % T)
    psm = sm([fmpre(w, amm, gtm, '( %s gcd m )' % T)], 'recnd', '%s e. CC' % PSI(T, 'm'))
    cmm = sm([lift(w, cf, amm), mn], 'ffvelcdmd', '( C ` m ) e. CC')
    ab = sm([sm([bv], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` ( ( C ` m ) x. %s ) )' % (BT, PSI(T, 'm'))), sm([cmm, psm], 'absmuld',
             '( abs ` ( ( C ` m ) x. %s ) ) = ( ( abs ` ( C ` m ) ) x. ( abs ` %s ) )' % (PSI(T, 'm'), PSI(T, 'm')))], 'eqtrd',
            '( abs ` ( %s ` m ) ) = ( ( abs ` ( C ` m ) ) x. ( abs ` %s ) )' % (BT, PSI(T, 'm')))
    cjm = w.s([w.s([w.s([], 'fveq2', '( j = m -> ( C ` j ) = ( C ` m ) )')], 'fveq2d', '( j = m -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` m ) ) )')], 'breq1d',
              '( j = m -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` m ) ) <_ 1 ) )')
    cm1 = sm([cjm, lift(w, cb, amm), mn], 'rspcdva', '( abs ` ( C ` m ) ) <_ 1')
    pst = sm([lift(w, tn, amm), mn, w.inst('z5psiabs')], 'syl2anc', '( abs ` %s ) <_ %s' % (PSI(T, 'm'), T))
    lm = sm([sm([cmm], 'abscld', '( abs ` ( C ` m ) ) e. RR'), sm([], '1red', '1 e. RR'), sm([psm], 'abscld', '( abs ` %s ) e. RR' % PSI(T, 'm')), lift(w, tr, amm),
             sm([cmm], 'absge0d', '0 <_ ( abs ` ( C ` m ) )'), sm([psm], 'absge0d', '0 <_ ( abs ` %s )' % PSI(T, 'm')), cm1, pst], 'lemul12ad',
            '( ( abs ` ( C ` m ) ) x. ( abs ` %s ) ) <_ ( 1 x. %s )' % (PSI(T, 'm'), T))
    lm2 = sm([sm([ab, lm], 'eqbrtrd', '( abs ` ( %s ` m ) ) <_ ( 1 x. %s )' % (BT, T)), sm([sm([lift(w, tr, amm)], 'recnd', '%s e. CC' % T)], 'mullidd', '( 1 x. %s ) = %s' % (T, T))],
             'breqtrd', '( abs ` ( %s ` m ) ) <_ %s' % (BT, T))
    bb = st([lm2], 'ralrimiva', 'A. m e. NN ( abs ` ( %s ` m ) ) <_ %s' % (BT, T))
    H1 = '( ( %s : NN --> CC /\\ { D } e. Fin /\\ { D } C_ NN ) /\\ A. l e. ( NN \\ { D } ) ( %s ` l ) = 0 )' % (PMD, PMD)
    H2 = '( ( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s ) /\\ %s )' % (BT, T, BT, T, SRE1)
    h1 = st([st([pmf, snf, sns], '3jca', '( %s : NN --> CC /\\ { D } e. Fin /\\ { D } C_ NN )' % PMD), z0], 'jca', H1)
    h2 = st([st([btf, tr, bb], '3jca', '( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (BT, T, BT, T)), hs], 'jca', H2)
    CVb = lambda n: '( sum_ d e. %s ( ( %s ` d ) x. ( %s ` ( %s / d ) ) ) x. ( %s ^c -u S ) )' % (DV(n), PMD, BT, n, n)
    SAd = 'sum_ d e. { D } ( ( %s ` d ) x. ( d ^c -u S ) )' % PMD
    SBk = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u S ) )' % BT
    fcv = st([st([h1, h2], 'jca', '( %s /\\ %s )' % (H1, H2)), w.inst('z5fconv')], 'syl', 'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s )' % (CVb('n'), SAd, SBk))
    # the convolution values
    an = '( %s /\\ n e. NN )' % ante
    sn = mkst(w, an)
    nn = sn([], 'simpr', 'n e. NN')
    pmc2 = sn([lift(w, dn, an), nn, lift(w, cD, an), lift(w, btf, an), w.inst('z5pmconv')], 'syl22anc',
              'sum_ d e. %s ( ( %s ` d ) x. ( %s ` ( n / d ) ) ) = if ( D || n , ( ( C ` D ) x. ( %s ` ( n / D ) ) ) , 0 )' % (DV('n'), PMD, BT, BT))
    bdn = '( %s /\\ D || n )' % an
    sbd = mkst(w, bdn)
    ndD = sbd([sbd([], 'simpr', 'D || n'), sbd([lift(w, nn, bdn), lift(w, dn, bdn), w.inst('nndivdvds')], 'syl2anc', '( D || n <-> ( n / D ) e. NN )')], 'mpbid', '( n / D ) e. NN')
    bvd, _ = mpv(w, bdn, 'e', 'NN', '( ( C ` e ) x. %s )' % PSI(T, 'e'), '( n / D )', ndD)
    mi = mulinst(w, bdn, 'C', 'D', '( n / D )', lift(w, cm, bdn), lift(w, dn, bdn), ndD)
    dcan = sbd([sbd([lift(w, nn, bdn)], 'nncnd', 'n e. CC'), sbd([lift(w, dn, bdn)], 'nncnd', 'D e. CC'), sbd([lift(w, dn, bdn)], 'nnne0d', 'D =/= 0')], 'divcan2d',
               '( D x. ( n / D ) ) = n')
    cnn = sbd([sbd([sbd([dcan], 'fveq2d', '( C ` ( D x. ( n / D ) ) ) = ( C ` n )'), mi], 'eqtr3d', '( C ` n ) = ( ( C ` D ) x. ( C ` ( n / D ) ) )')], 'eqcomd',
              '( ( C ` D ) x. ( C ` ( n / D ) ) ) = ( C ` n )')
    gtd = sbd([lift(w, tn, bdn), ndD, w.inst('gcdnncl')], 'syl2anc', '( %s gcd ( n / D ) ) e. NN' % T)
    psd = sbd([fmpre(w, bdn, gtd, '( %s gcd ( n / D ) )' % T)], 'recnd', '%s e. CC' % PSI(T, '( n / D )'))
    cnd = sbd([lift(w, cf, bdn), ndD], 'ffvelcdmd', '( C ` ( n / D ) ) e. CC')
    u1 = sbd([bvd], 'oveq2d', '( ( C ` D ) x. ( %s ` ( n / D ) ) ) = ( ( C ` D ) x. ( ( C ` ( n / D ) ) x. %s ) )' % (BT, PSI(T, '( n / D )')))
    u2 = sbd([sbd([lift(w, cD, bdn), cnd, psd], 'mulassd', '( ( ( C ` D ) x. ( C ` ( n / D ) ) ) x. %s ) = ( ( C ` D ) x. ( ( C ` ( n / D ) ) x. %s ) )'
                  % (PSI(T, '( n / D )'), PSI(T, '( n / D )')))], 'eqcomd',
             '( ( C ` D ) x. ( ( C ` ( n / D ) ) x. %s ) ) = ( ( ( C ` D ) x. ( C ` ( n / D ) ) ) x. %s )' % (PSI(T, '( n / D )'), PSI(T, '( n / D )')))
    u3 = sbd([cnn], 'oveq1d', '( ( ( C ` D ) x. ( C ` ( n / D ) ) ) x. %s ) = ( ( C ` n ) x. %s )' % (PSI(T, '( n / D )'), PSI(T, '( n / D )')))
    uu = sbd([sbd([u1, u2], 'eqtrd', '( ( C ` D ) x. ( %s ` ( n / D ) ) ) = ( ( ( C ` D ) x. ( C ` ( n / D ) ) ) x. %s )' % (BT, PSI(T, '( n / D )'))), u3], 'eqtrd',
             '( ( C ` D ) x. ( %s ` ( n / D ) ) ) = ( ( C ` n ) x. %s )' % (BT, PSI(T, '( n / D )')))
    ifx = sn([uu], 'ifeq1da', 'if ( D || n , ( ( C ` D ) x. ( %s ` ( n / D ) ) ) , 0 ) = if ( D || n , ( ( C ` n ) x. %s ) , 0 )' % (BT, PSI(T, '( n / D )')))
    cvv = sn([sn([pmc2, ifx], 'eqtrd', 'sum_ d e. %s ( ( %s ` d ) x. ( %s ` ( n / d ) ) ) = if ( D || n , ( ( C ` n ) x. %s ) , 0 )' % (DV('n'), PMD, BT, PSI(T, '( n / D )')))],
             'oveq1d', '%s = %s' % (CVb('n'), SB('D', 'n')))
    me = st([cvv], 'mpteq2dva', '( n e. NN |-> %s ) = ( n e. NN |-> %s )' % (CVb('n'), SB('D', 'n')))
    sq = st([me], 'seqeq3d', 'seq 1 ( + , ( n e. NN |-> %s ) ) = seq 1 ( + , ( n e. NN |-> %s ) )' % (CVb('n'), SB('D', 'n')))
    l1 = st([fcv, st([sq], 'breq1d', '( seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s ) <-> seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s ) )'
                     % (CVb('n'), SAd, SBk, SB('D', 'n'), SAd, SBk))], 'mpbid', 'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s )' % (SB('D', 'n'), SAd, SBk))
    # the point-mass sum
    ifD = st([cD, st([], '0cnd', '0 e. CC')], 'ifcld', 'if ( D = D , ( C ` D ) , 0 ) e. CC')
    pvD, _ = mpv(w, ante, 'm', 'NN', 'if ( m = D , ( C ` D ) , 0 )', 'D', dn, exs=st([ifD], 'elexd', 'if ( D = D , ( C ` D ) , 0 ) e. _V'))
    pDD = st([pvD, st([st([], 'eqidd', 'D = D')], 'iftrued', 'if ( D = D , ( C ` D ) , 0 ) = ( C ` D )')], 'eqtrd', '( %s ` D ) = ( C ` D )' % PMD)
    xD = st([st([dn], 'nncnd', 'D e. CC'), st([sc], 'negcld', '-u S e. CC')], 'cxpcld', '( D ^c -u S ) e. CC')
    vD = st([pDD], 'oveq1d', '( ( %s ` D ) x. ( D ^c -u S ) ) = ( ( C ` D ) x. ( D ^c -u S ) )' % PMD)
    vDc = st([vD, st([cD, xD], 'mulcld', '( ( C ` D ) x. ( D ^c -u S ) ) e. CC')], 'eqeltrd', '( ( %s ` D ) x. ( D ^c -u S ) ) e. CC' % PMD)
    cgd = w.s([w.s([], 'fveq2', '( d = D -> ( %s ` d ) = ( %s ` D ) )' % (PMD, PMD)), w.s([w.s([], 'id', '( d = D -> d = D )')], 'oveq1d', '( d = D -> ( d ^c -u S ) = ( D ^c -u S ) )')],
            'oveq12d', '( d = D -> ( ( %s ` d ) x. ( d ^c -u S ) ) = ( ( %s ` D ) x. ( D ^c -u S ) ) )' % (PMD, PMD))
    sumsn_i = w.s([cgd], 'sumsn', '( ( D e. NN /\\ ( ( %s ` D ) x. ( D ^c -u S ) ) e. CC ) -> %s = ( ( %s ` D ) x. ( D ^c -u S ) ) )' % (PMD, SAd, PMD))
    ssn = st([dn, vDc, sumsn_i], 'syl2anc', '%s = ( ( %s ` D ) x. ( D ^c -u S ) )' % (SAd, PMD))
    va = st([ssn, vD], 'eqtrd', '%s = ( ( C ` D ) x. ( D ^c -u S ) )' % SAd)
    # the chi psi_t series
    sqT = st([tn, t0], 'jca', SQF(T))
    ch = st([sqT, st([st([chr_, cb], 'jca', '( %s /\\ %s )' % (CHR, CB)), hs], 'jca', '( ( %s /\\ %s ) /\\ %s )' % (CHR, CB, SRE1)), w.inst('z5chpsi')], 'syl2anc',
            'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s )' % (CPS(T, 'n'), EU(PF(T)), LS()))
    akk = '( %s /\\ k e. NN )' % ante
    skk = mkst(w, akk)
    kk = skk([], 'simpr', 'k e. NN')
    mvk, _ = mpv(w, akk, 'n', 'NN', CPS(T, 'n'), 'k', kk)
    gtk = skk([lift(w, tn, akk), kk, w.inst('gcdnncl')], 'syl2anc', '( %s gcd k ) e. NN' % T)
    psk = skk([fmpre(w, akk, gtk, '( %s gcd k )' % T)], 'recnd', '%s e. CC' % PSI(T, 'k'))
    ckk = skk([lift(w, cf, akk), kk], 'ffvelcdmd', '( C ` k ) e. CC')
    xkk = skk([skk([kk], 'nncnd', 'k e. CC'), skk([lift(w, sc, akk)], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')
    cpk = skk([skk([ckk, psk], 'mulcld', '( ( C ` k ) x. %s ) e. CC' % PSI(T, 'k')), xkk], 'mulcld', '%s e. CC' % CPS(T, 'k'))
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    isc = w.s([nnz, w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ante), mvk, cpk, ch], 'isumclim', '( %s -> sum_ k e. NN %s = ( %s x. %s ) )' % (ante, CPS(T, 'k'), EU(PF(T)), LS()))
    bvk, _ = mpv(w, akk, 'e', 'NN', '( ( C ` e ) x. %s )' % PSI(T, 'e'), 'k', kk)
    sb2 = st([skk([bvk], 'oveq1d', '( ( %s ` k ) x. ( k ^c -u S ) ) = %s' % (BT, CPS(T, 'k')))], 'sumeq2dv', '%s = sum_ k e. NN %s' % (SBk, CPS(T, 'k')))
    euq = st([pfe], 'prodeq1d', '%s = %s' % (EU(PF(T)), EU(QS('D', 'R'))))
    vb = st([st([sb2, isc], 'eqtrd', '%s = ( %s x. %s )' % (SBk, EU(PF(T)), LS())), st([euq], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (EU(PF(T)), LS(), EU(QS('D', 'R')), LS()))],
            'eqtrd', '%s = ( %s x. %s )' % (SBk, EU(QS('D', 'R')), LS()))
    vv = st([va, vb], 'oveq12d', '( %s x. %s ) = ( ( ( C ` D ) x. ( D ^c -u S ) ) x. ( %s x. %s ) )' % (SAd, SBk, EU(QS('D', 'R')), LS()))
    w.qed([l1, vv], 'breqtrd', STATEMENTS['z5stepb'])
    return w



def z5finser():
    w = W('z5finser', "A finite sum of convergent series (Lean Summable.tsum_finsetSum with tsum_mul_left): if each seq 1 ( + , G ) "
                      "converges to L for k in the finite A, then seq 1 ( + , m |-> sum_ k e. A ( E G ( m ) ) ) converges to "
                      "sum_ k e. A ( E L ) (climfsum, isermulc2, fsumser, fsumcom).")
    h1, h2, h3, h4 = hyps_of(w, 'z5finser')
    Gp = '( m e. NN |-> ( E x. ( G ` m ) ) )'
    HM = '( m e. NN |-> sum_ k e. A ( E x. ( G ` m ) ) )'
    pk = '( ph /\\ k e. A )'
    # ( pk -> A. m e. NN ( G ` m ) e. CC )
    h2a = w.s([h2], 'anassrs', '( ( %s /\\ m e. NN ) -> ( G ` m ) e. CC )' % pk)
    ral = w.s([h2a], 'ralrimiva', '( %s -> A. m e. NN ( G ` m ) e. CC )' % pk)

    def gat(a, v, mem):
        c = w.s([w.s([], 'fveq2', '( m = %s -> ( G ` m ) = ( G ` %s ) )' % (v, v))], 'eleq1d', '( m = %s -> ( ( G ` m ) e. CC <-> ( G ` %s ) e. CC ) )' % (v, v))
        return w.s([c, lift(w, ral, a), mem], 'rspcdva', '( %s -> ( G ` %s ) e. CC )' % (a, v))
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    # per k: seq 1 ( + , Gp ) ~~> ( E x. L )
    a = '( %s /\\ j e. NN )' % pk
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % a)
    gj = gat(a, 'j', jn)
    ej = w.s([lift(w, h4, a), gj], 'mulcld', '( %s -> ( E x. ( G ` j ) ) e. CC )' % a)
    gpv, _ = mpv(w, a, 'm', 'NN', '( E x. ( G ` m ) )', 'j', jn, exs=w.s([ej], 'elexd', '( %s -> ( E x. ( G ` j ) ) e. _V )' % a))
    im = w.s([nnz, w.s([], '1zzd', '( %s -> 1 e. ZZ )' % pk), h4, h3, gj, gpv], 'isermulc2', '( %s -> seq 1 ( + , %s ) ~~> ( E x. L ) )' % (pk, Gp))
    # partial sums
    q = '( ph /\\ j e. NN )'
    r = '( %s /\\ i e. ( 1 ... j ) )' % q
    inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... j ) )' % r), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % r)
    rk = '( %s /\\ k e. A )' % r
    rk_pk = w.s([w.s([], 'simplll', '( %s -> ph )' % rk), w.s([], 'simpr', '( %s -> k e. A )' % rk)], 'jca', '( %s -> %s )' % (rk, pk))
    # E x. ( G ` i ) in CC under ( q /\ ( i e. ( 1 ... j ) /\ k e. A ) )
    qik = '( %s /\\ ( i e. ( 1 ... j ) /\\ k e. A ) )' % q
    qpk = w.s([w.s([], 'simpll', '( %s -> ph )' % qik), w.s([], 'simprr', '( %s -> k e. A )' % qik)], 'jca', '( %s -> %s )' % (qik, pk))
    qin = w.s([w.s([], 'simprl', '( %s -> i e. ( 1 ... j ) )' % qik), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % qik)
    rsn = w.s([qpk, ral], 'syl', '( %s -> A. m e. NN ( G ` m ) e. CC )' % qik)
    cgi = w.s([w.s([], 'fveq2', '( m = i -> ( G ` m ) = ( G ` i ) )')], 'eleq1d', '( m = i -> ( ( G ` m ) e. CC <-> ( G ` i ) e. CC ) )')
    gi = w.s([cgi, rsn, qin], 'rspcdva', '( %s -> ( G ` i ) e. CC )' % qik)
    ei = w.s([w.s([qpk, h4], 'syl', '( %s -> E e. CC )' % qik), gi], 'mulcld', '( %s -> ( E x. ( G ` i ) ) e. CC )' % qik)
    # H ` j = sum_ k ( seq 1 ( + , Gp ) ` j )
    sq = mkst(w, q)
    j1 = sq([sq([], 'simpr', 'j e. NN'), w.s([], 'elnnuz', '( j e. NN <-> j e. ( ZZ>= ` 1 ) )')], 'sylib', 'j e. ( ZZ>= ` 1 )')
    fin = lift(w, h1, q)
    # values of HM at i
    rr = mkst(w, r)
    ea = '( %s /\\ k e. A )' % r
    ei_r = w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (ea, q)), w.s([w.s([], 'simplr', '( %s -> i e. ( 1 ... j ) )' % ea), w.s([], 'simpr', '( %s -> k e. A )' % ea)], 'jca',
                                                                         '( %s -> ( i e. ( 1 ... j ) /\\ k e. A ) )' % ea)], 'jca', '( %s -> %s )' % (ea, qik)), ei], 'syl',
               '( %s -> ( E x. ( G ` i ) ) e. CC )' % ea)
    sumc = rr([lift(w, fin, r), ei_r], 'fsumcl', 'sum_ k e. A ( E x. ( G ` i ) ) e. CC')
    hv, _ = mpv(w, r, 'm', 'NN', 'sum_ k e. A ( E x. ( G ` m ) )', 'i', inn, exs=rr([sumc], 'elexd', 'sum_ k e. A ( E x. ( G ` i ) ) e. _V'))
    hvc = rr([hv, sumc], 'eqeltrd', '( %s ` i ) e. CC' % HM)
    fs1 = sq([rr([], 'eqidd', '( %s ` i ) = ( %s ` i )' % (HM, HM)), j1, hvc], 'fsumser', 'sum_ i e. ( 1 ... j ) ( %s ` i ) = ( seq 1 ( + , %s ) ` j )' % (HM, HM))
    s1 = sq([hv], 'sumeq2dv', 'sum_ i e. ( 1 ... j ) ( %s ` i ) = sum_ i e. ( 1 ... j ) sum_ k e. A ( E x. ( G ` i ) )' % HM)
    com = sq([sq([], 'fzfid', '( 1 ... j ) e. Fin'), fin, ei], 'fsumcom',
             'sum_ i e. ( 1 ... j ) sum_ k e. A ( E x. ( G ` i ) ) = sum_ k e. A sum_ i e. ( 1 ... j ) ( E x. ( G ` i ) )')
    qk = '( %s /\\ k e. A )' % q
    sqk = mkst(w, qk)
    qk_pk = w.s([w.s([], 'simpll', '( %s -> ph )' % qk), w.s([], 'simpr', '( %s -> k e. A )' % qk)], 'jca', '( %s -> %s )' % (qk, pk))
    qki = '( %s /\\ i e. ( 1 ... j ) )' % qk
    ikq = w.s([w.s([w.s([], 'simplll', '( %s -> ph )' % qki), w.s([], 'simpllr', '( %s -> j e. NN )' % qki)], 'jca', '( %s -> %s )' % (qki, q)),
               w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... j ) )' % qki), w.s([], 'simplr', '( %s -> k e. A )' % qki)], 'jca', '( %s -> ( i e. ( 1 ... j ) /\\ k e. A ) )' % qki)],
              'jca', '( %s -> %s )' % (qki, qik))
    eqki = w.s([ikq, ei], 'syl', '( %s -> ( E x. ( G ` i ) ) e. CC )' % qki)
    iqk = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... j ) )' % qki), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % qki)
    gpi, _ = mpv(w, qki, 'm', 'NN', '( E x. ( G ` m ) )', 'i', iqk, exs=w.s([eqki], 'elexd', '( %s -> ( E x. ( G ` i ) ) e. _V )' % qki))
    fs2 = sqk([gpi, lift(w, j1, qk), eqki], 'fsumser',
              'sum_ i e. ( 1 ... j ) ( E x. ( G ` i ) ) = ( seq 1 ( + , %s ) ` j )' % Gp)
    s3 = sq([fs2], 'sumeq2dv', 'sum_ k e. A sum_ i e. ( 1 ... j ) ( E x. ( G ` i ) ) = sum_ k e. A ( seq 1 ( + , %s ) ` j )' % Gp)
    hj = sq([sq([fs1], 'eqcomd', '( seq 1 ( + , %s ) ` j ) = sum_ i e. ( 1 ... j ) ( %s ` i )' % (HM, HM)), s1], 'eqtrd',
            '( seq 1 ( + , %s ) ` j ) = sum_ i e. ( 1 ... j ) sum_ k e. A ( E x. ( G ` i ) )' % HM)
    hj = sq([sq([hj, com], 'eqtrd', '( seq 1 ( + , %s ) ` j ) = sum_ k e. A sum_ i e. ( 1 ... j ) ( E x. ( G ` i ) )' % HM), s3], 'eqtrd',
            '( seq 1 ( + , %s ) ` j ) = sum_ k e. A ( seq 1 ( + , %s ) ` j )' % (HM, Gp))
    # the partial sums of each Gp are complex
    pj = '( ph /\\ ( k e. A /\\ j e. NN ) )'
    pji = '( %s /\\ i e. ( 1 ... j ) )' % pj
    pjiq = w.s([w.s([w.s([], 'simpll', '( %s -> ph )' % pji), w.s([], 'simplrr', '( %s -> j e. NN )' % pji)], 'jca', '( %s -> %s )' % (pji, q)),
                w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... j ) )' % pji), w.s([], 'simplrl', '( %s -> k e. A )' % pji)], 'jca', '( %s -> ( i e. ( 1 ... j ) /\\ k e. A ) )' % pji)],
               'jca', '( %s -> %s )' % (pji, qik))
    epji = w.s([pjiq, ei], 'syl', '( %s -> ( E x. ( G ` i ) ) e. CC )' % pji)
    ipj = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... j ) )' % pji), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % pji)
    gpj, _ = mpv(w, pji, 'm', 'NN', '( E x. ( G ` m ) )', 'i', ipj, exs=w.s([epji], 'elexd', '( %s -> ( E x. ( G ` i ) ) e. _V )' % pji))
    spj = mkst(w, pj)
    j1p = spj([spj([], 'simprr', 'j e. NN'), w.s([], 'elnnuz', '( j e. NN <-> j e. ( ZZ>= ` 1 ) )')], 'sylib', 'j e. ( ZZ>= ` 1 )')
    fs3 = spj([gpj, j1p, epji], 'fsumser', 'sum_ i e. ( 1 ... j ) ( E x. ( G ` i ) ) = ( seq 1 ( + , %s ) ` j )' % Gp)
    scc = spj([spj([], 'fzfid', '( 1 ... j ) e. Fin'), epji], 'fsumcl', 'sum_ i e. ( 1 ... j ) ( E x. ( G ` i ) ) e. CC')
    sjc = spj([fs3, scc], 'eqeltrrd', '( seq 1 ( + , %s ) ` j ) e. CC' % Gp)
    hex = w.s([w.s([], 'seqex', 'seq 1 ( + , %s ) e. _V' % HM)], 'a1i', '( ph -> seq 1 ( + , %s ) e. _V )' % HM)
    w.qed([nnz, w.s([], '1zzd', '( ph -> 1 e. ZZ )'), h1, im, hex, sjc, hj], 'climfsum', STATEMENTS['z5finser'])
    return w


MRB = lambda u, v: ('( s e. CC |-> sum_ d e. ( 1 ... ( |_ ` ( 2nd ` %s ) ) ) ( ( ( ( ( ( ( 1st ` %s ) bvLam ( 2nd ` %s ) ) ` d ) x. '
                    '( ( mmu ` ( ( 2nd ` %s ) gcd d ) ) x. ( phi ` ( ( 2nd ` %s ) gcd d ) ) ) ) x. ( ( 1st ` %s ) ` d ) ) x. ( d ^c -u s ) ) x. '
                    'prod_ p e. { q e. Prime | ( q || ( 2nd ` %s ) /\\ -. q || d ) } ( 1 + ( ( ( ( ( mmu ` p ) x. ( phi ` p ) ) - 1 ) x. ( ( 1st ` %s ) ` p ) ) '
                    'x. ( p ^c -u s ) ) ) ) )' % (u, u, u, v, v, v, v, v))


def z5mrval():
    w = W('z5mrval', "Value of the mollifier (Lean Mr, Detector.lean 832): ( ( <. A , B >. Mr <. C , R >. ) ` S ) = sum_ ( d <_ B ) "
                     "lambda_d f ( ( R , d ) ) C ( d ) d ^ -S prod_ ( p | R , -. p | d ) ( 1 + ( f ( p ) - 1 ) C ( p ) p ^ -S ).")
    ante = '( ( ( A e. U /\\ B e. V ) /\\ ( C e. W /\\ R e. X ) ) /\\ S e. CC )'
    st = mkst(w, ante)
    sa = st([], 'simplll', 'A e. U'); sb = st([], 'simpllr', 'B e. V'); sc = st([], 'simplrl', 'C e. W'); sr = st([], 'simplrr', 'R e. X')
    OP = '<. A , B >.'; OQ = '<. C , R >.'
    both = st([a1(w, ante, w.s([], 'opex', '%s e. _V' % OP), '%s e. _V' % OP), a1(w, ante, w.s([], 'opex', '%s e. _V' % OQ), '%s e. _V' % OQ)], 'jca',
              '( %s e. _V /\\ %s e. _V )' % (OP, OQ))
    mk = w.s([w.s([], 'cnex', 'CC e. _V')], 'mptex', '%s e. _V' % MRB(OP, OQ))
    e1 = cg(w, MRB('u', 'v'), 'u', OP)
    e2 = cg(w, MRB(OP, 'v'), 'v', OQ)
    df = w.s([], 'df-moll', 'Mr = ( u e. _V , v e. _V |-> %s )' % MRB('u', 'v'))
    ov = w.s([e1, e2, df, mk], 'ovmpo', '( ( %s e. _V /\\ %s e. _V ) -> ( %s Mr %s ) = %s )' % (OP, OQ, OP, OQ, MRB(OP, OQ)))
    pv = st([both, ov], 'syl', '( %s Mr %s ) = %s' % (OP, OQ, MRB(OP, OQ)))
    body = MRB(OP, OQ)[len('( s e. CC |-> '):-2]
    bS = body.replace('-u s )', '-u S )')
    val, v = mpv(w, ante, 's', 'CC', body, 'S', st([], 'simpr', 'S e. CC'), exs=a1(w, ante, w.s([], 'sumex', '%s e. _V' % bS), '%s e. _V' % bS))
    r = {}
    r['( 1st ` %s )' % OP] = ('A', st([sa, sb, w.inst('op1stg')], 'syl2anc', '( 1st ` %s ) = A' % OP))
    r['( 2nd ` %s )' % OP] = ('B', st([sa, sb, w.inst('op2ndg')], 'syl2anc', '( 2nd ` %s ) = B' % OP))
    r['( 1st ` %s )' % OQ] = ('C', st([sc, sr, w.inst('op1stg')], 'syl2anc', '( 1st ` %s ) = C' % OQ))
    r['( 2nd ` %s )' % OQ] = ('R', st([sc, sr, w.inst('op2ndg')], 'syl2anc', '( 2nd ` %s ) = R' % OQ))
    rw, new = w.rewrite(v, r, ante)
    assert new == 'sum_ d e. ( 1 ... ( |_ ` B ) ) %s' % MRT('d'), new
    w.qed([st([st([pv], 'fveq1d', '( ( %s Mr %s ) ` S ) = ( %s ` S )' % (OP, OQ, MRB(OP, OQ))), val], 'eqtrd', '( ( %s Mr %s ) ` S ) = %s' % (OP, OQ, v)), rw], 'eqtrd',
          STATEMENTS['z5mrval'])
    return w



def habfacts(w, ante, hab):
    """steps A e. RR, 0 < A, B e. RR, A < B, ( A e. RR+ /\\ B e. RR+ /\\ A < B ) under ante from hab: ( ante -> HAB0 )"""
    st = mkst(w, ante)
    h1_ = st([hab], 'simpld', '( A e. RR /\\ 0 < A )'); h2_ = st([hab], 'simprd', '( B e. RR /\\ A < B )')
    Ar = st([h1_], 'simpld', 'A e. RR'); A0 = st([h1_], 'simprd', '0 < A'); Br = st([h2_], 'simpld', 'B e. RR'); AB_ = st([h2_], 'simprd', 'A < B')
    arp = st([Ar, A0], 'elrpd', 'A e. RR+')
    brp = st([Br, lin.linarith(w, ante, [A0, AB_], '0 < B', leaves={'A': ('RR', Ar), 'B': ('RR', Br)})], 'elrpd', 'B e. RR+')
    abr = st([arp, brp, AB_], '3jca', '( A e. RR+ /\\ B e. RR+ /\\ A < B )')
    return Ar, A0, Br, AB_, abr


def up(w, a, b, dn, step, f):
    """( b -> f ) from step: ( ( a /\\ d e. NN ) -> f ), with dn: ( b -> d e. NN ) and b = ( a /\\ ... )"""
    return w.s([w.s([], 'simpl', '( %s -> %s )' % (b, a)), dn, w.s([step], 'ex', '( %s -> ( d e. NN -> %s ) )' % (a, f))], 'sylc', '( %s -> %s )' % (b, f))


def z5pwise():
    w = W('z5pwise', "Step B of blueprint Lemma 3.1, pointwise (Lean bvA_psi_char_eq_sum): a ( N ) psi_R ( N ) chi ( N ) = "
                     "sum_ ( d <_ z2 ) lambda_d f ( ( R , d ) ) [ d | N ] chi ( N ) psi_t ( N / d ), t = t ( d ; R ) (psi_mul_split on each "
                     "divisor; lambda_d = 0 beyond z2).")
    ante = split_imp(STATEMENTS['z5pwise'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpl', HAB0)
    sqr = st([], 'simprll', SQF('R')); cf = st([], 'simprlr', 'C : NN --> CC'); nn = st([], 'simprr', 'N e. NN')
    rn = st([sqr], 'simpld', 'R e. NN')
    Ar, A0, Br, AB_, abr = habfacts(w, ante, hab)
    LAM = '( ( A bvLam B ) ` d )'
    FG = FMP('( R gcd d )')
    PT = PSI(TT('d', 'R'), '( N / d )')
    PS = PSI('R', 'N'); CN = '( C ` N )'
    IF = 'if ( d || N , ( %s x. %s ) , 0 )' % (CN, PT)
    Y = '( ( %s x. %s ) x. %s )' % (LAM, FG, IF)
    I = '( 1 ... ( |_ ` B ) )'; U = '( %s u. %s )' % (DV('N'), I)
    cnc = st([cf, nn], 'ffvelcdmd', '%s e. CC' % CN)
    # Y in CC for d e. NN
    ad = '( %s /\\ d e. NN )' % ante
    sd = mkst(w, ad)
    dn = sd([], 'simpr', 'd e. NN')
    lr = sd([lift(w, abr, ad), dn, w.inst('bvlamre')], 'syl2anc', '%s e. RR' % LAM)
    gn = sd([lift(w, rn, ad), dn, w.inst('gcdnncl')], 'syl2anc', '( R gcd d ) e. NN')
    fgr = fmpre(w, ad, gn, '( R gcd d )')
    lfc = sd([sd([lr, fgr], 'remulcld', '( %s x. %s ) e. RR' % (LAM, FG))], 'recnd', '( %s x. %s ) e. CC' % (LAM, FG))
    at = '( %s /\\ d || N )' % ad
    s_t = mkst(w, at)
    ndt = s_t([s_t([], 'simpr', 'd || N'), s_t([lift(w, nn, at), lift(w, dn, at), w.inst('nndivdvds')], 'syl2anc', '( d || N <-> ( N / d ) e. NN )')], 'mpbid', '( N / d ) e. NN')
    tq = s_t([lift(w, rn, at), w.inst('z5tofsq')], 'syl', '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )' % (TT('d', 'R'), TT('d', 'R'), PF(TT('d', 'R')), QS('d', 'R')))
    ttn = s_t([tq], 'simplld', '%s e. NN' % TT('d', 'R'))
    gtn = s_t([ttn, ndt, w.inst('gcdnncl')], 'syl2anc', '( %s gcd ( N / d ) ) e. NN' % TT('d', 'R'))
    ptc = s_t([fmpre(w, at, gtn, '( %s gcd ( N / d ) )' % TT('d', 'R'))], 'recnd', '%s e. CC' % PT)
    tb = s_t([lift(w, cnc, at), ptc], 'mulcld', '( %s x. %s ) e. CC' % (CN, PT))
    fb = w.s([], '0cnd', '( ( %s /\\ -. d || N ) -> 0 e. CC )' % ad)
    ifc = sd([tb, fb], 'ifclda', '%s e. CC' % IF)
    yc = sd([lfc, ifc], 'mulcld', '%s e. CC' % Y)
    # on DV(N): the summand of the left side is Y
    a = '( %s /\\ d e. %s )' % (ante, DV('N'))
    sa = mkst(w, a)
    dna, dda = dvparts(w, a, sa([], 'simpr', 'd e. %s' % DV('N')), 'N')
    nda = sa([dda, sa([lift(w, nn, a), dna, w.inst('nndivdvds')], 'syl2anc', '( d || N <-> ( N / d ) e. NN )')], 'mpbid', '( N / d ) e. NN')
    psp = sa([lift(w, sqr, a), dna, nda, w.inst('z5psispl')], 'syl12anc', '%s = ( %s x. %s )' % (PSI('R', '( d x. ( N / d ) )'), FG, PT))
    dcan = sa([sa([lift(w, nn, a)], 'nncnd', 'N e. CC'), sa([dna], 'nncnd', 'd e. CC'), sa([dna], 'nnne0d', 'd =/= 0')], 'divcan2d', '( d x. ( N / d ) ) = N')
    rwp, newp = w.rewrite(PSI('R', '( d x. ( N / d ) )'), {'( d x. ( N / d ) )': ('N', dcan)}, a)
    psn = sa([rwp, psp], 'eqtr3d', '%s = ( %s x. %s )' % (PS, FG, PT))
    lra = up(w, ante, a, dna, lr, '%s e. RR' % LAM)
    fga = up(w, ante, a, dna, fgr, '%s e. RR' % FG)
    tqa = sa([lift(w, rn, a), w.inst('z5tofsq')], 'syl', '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )' % (TT('d', 'R'), TT('d', 'R'), PF(TT('d', 'R')), QS('d', 'R')))
    gta = sa([sa([tqa], 'simplld', '%s e. NN' % TT('d', 'R')), nda, w.inst('gcdnncl')], 'syl2anc', '( %s gcd ( N / d ) ) e. NN' % TT('d', 'R'))
    pta = sa([fmpre(w, a, gta, '( %s gcd ( N / d ) )' % TT('d', 'R'))], 'recnd', '%s e. CC' % PT)
    lc = sa([lra], 'recnd', '%s e. CC' % LAM); fc = sa([fga], 'recnd', '%s e. CC' % FG); cna = lift(w, cnc, a)
    L0 = '( ( %s x. %s ) x. %s )' % (LAM, PS, CN)
    l1 = sa([sa([psn], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (LAM, PS, LAM, FG, PT))], 'oveq1d', '%s = ( ( %s x. ( %s x. %s ) ) x. %s )' % (L0, LAM, FG, PT, CN))
    l2 = sa([sa([sa([lc, fc, pta], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (LAM, FG, PT, LAM, FG, PT))], 'eqcomd',
                '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (LAM, FG, PT, LAM, FG, PT))], 'oveq1d',
            '( ( %s x. ( %s x. %s ) ) x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (LAM, FG, PT, CN, LAM, FG, PT, CN))
    lfa = sa([lc, fc], 'mulcld', '( %s x. %s ) e. CC' % (LAM, FG))
    l3 = sa([lfa, pta, cna], 'mulassd', '( ( ( %s x. %s ) x. %s ) x. %s ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (LAM, FG, PT, CN, LAM, FG, PT, CN))
    l4 = sa([sa([pta, cna], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (PT, CN, CN, PT))], 'oveq2d',
            '( ( %s x. %s ) x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (LAM, FG, PT, CN, LAM, FG, CN, PT))
    Yp = '( ( %s x. %s ) x. ( %s x. %s ) )' % (LAM, FG, CN, PT)
    l5 = sa([sa([dda], 'iftrued', '%s = ( %s x. %s )' % (IF, CN, PT))], 'oveq2d', '%s = %s' % (Y, Yp))
    lch = sa([l1, l2], 'eqtrd', '%s = ( ( ( %s x. %s ) x. %s ) x. %s )' % (L0, LAM, FG, PT, CN))
    lch = sa([lch, l3], 'eqtrd', '%s = ( ( %s x. %s ) x. ( %s x. %s ) )' % (L0, LAM, FG, PT, CN))
    lch = sa([lch, l4], 'eqtrd', '%s = %s' % (L0, Yp))
    lch = sa([lch, l5], 'eqtr4d', '%s = %s' % (L0, Y))
    # the left side as a divisor sum
    dvf = sy(w, ante, nn, 'dvdsfi', '%s e. Fin' % DV('N'))
    bva = st([Ar, Br, nn, w.inst('bvaval')], 'syl21anc', '( ( A bvA B ) ` N ) = sum_ d e. %s %s' % (DV('N'), LAM))
    gnN = st([rn, nn, w.inst('gcdnncl')], 'syl2anc', '( R gcd N ) e. NN')
    psc = st([fmpre(w, ante, gnN, '( R gcd N )')], 'recnd', '%s e. CC' % PS)
    m1 = st([dvf, psc, lc], 'fsummulc1', '( sum_ d e. %s %s x. %s ) = sum_ d e. %s ( %s x. %s )' % (DV('N'), LAM, PS, DV('N'), LAM, PS))
    lpc = sa([lc, lift(w, psc, a)], 'mulcld', '( %s x. %s ) e. CC' % (LAM, PS))
    m2 = st([dvf, cnc, lpc], 'fsummulc1', '( sum_ d e. %s ( %s x. %s ) x. %s ) = sum_ d e. %s %s' % (DV('N'), LAM, PS, CN, DV('N'), L0))
    AN = '( ( A bvA B ) ` N )'
    e1 = st([st([bva], 'oveq1d', '( %s x. %s ) = ( sum_ d e. %s %s x. %s )' % (AN, PS, DV('N'), LAM, PS)), m1], 'eqtrd',
            '( %s x. %s ) = sum_ d e. %s ( %s x. %s )' % (AN, PS, DV('N'), LAM, PS))
    e2 = st([st([e1], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( sum_ d e. %s ( %s x. %s ) x. %s )' % (AN, PS, CN, DV('N'), LAM, PS, CN)), m2], 'eqtrd',
            '( ( %s x. %s ) x. %s ) = sum_ d e. %s %s' % (AN, PS, CN, DV('N'), L0))
    e3 = st([lch], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (DV('N'), L0, DV('N'), Y))
    LHS = '( ( %s x. %s ) x. %s )' % (AN, PS, CN)
    e4 = st([e2, e3], 'eqtrd', '%s = sum_ d e. %s %s' % (LHS, DV('N'), Y))
    # the union
    uns = st([st([w.s([w.s([], 'ssrab2', '%s C_ NN' % DV('N'))], 'a1i', '( %s -> %s C_ NN )' % (ante, DV('N'))),
                   w.s([w.s([], 'fz1ssnn', '%s C_ NN' % I)], 'a1i', '( %s -> %s C_ NN )' % (ante, I))], 'jca', '( %s C_ NN /\\ %s C_ NN )' % (DV('N'), I)),
              w.s([], 'unss', '( ( %s C_ NN /\\ %s C_ NN ) <-> %s C_ NN )' % (DV('N'), I, U))], 'sylib', '%s C_ NN' % U)
    uf = st([dvf, st([], 'fzfid', '%s e. Fin' % I), w.inst('unfi')], 'syl2anc', '%s e. Fin' % U)
    # Y in CC on DV(N) and on I
    yca = up(w, ante, a, dna, yc, '%s e. CC' % Y)
    ai = '( %s /\\ d e. %s )' % (ante, I)
    dni = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (ai, I)), w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % ai)
    yci = up(w, ante, ai, dni, yc, '%s e. CC' % Y)
    # zero on U \ DV(N)
    z1 = '( %s /\\ d e. ( %s \\ %s ) )' % (ante, U, DV('N'))
    s1 = mkst(w, z1)
    du1 = s1([s1([], 'simpr', 'd e. ( %s \\ %s )' % (U, DV('N')))], 'eldifad', 'd e. %s' % U)
    nd1 = s1([s1([], 'simpr', 'd e. ( %s \\ %s )' % (U, DV('N')))], 'eldifbd', '-. d e. %s' % DV('N'))
    dn1 = s1([lift(w, uns, z1), du1], 'sseldd', 'd e. NN')
    e_ = '( %s /\\ d || N )' % z1
    ind = w.s([lift(w, dn1, e_), w.s([], 'simpr', '( %s -> d || N )' % e_), w.s([eldv(w, 'N')], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ d || N ) ) )' % (e_, DV('N')))],
              'mpbir2and', '( %s -> d e. %s )' % (e_, DV('N')))
    ndn = w.s([ind, lift(w, nd1, e_)], 'pm2.65da', '( %s -> -. d || N )' % z1)
    if0 = s1([ndn], 'iffalsed', '%s = 0' % IF)
    lf1 = up(w, ante, z1, dn1, lfc, '( %s x. %s ) e. CC' % (LAM, FG))
    y01 = s1([s1([if0], 'oveq2d', '%s = ( ( %s x. %s ) x. 0 )' % (Y, LAM, FG)), s1([lf1], 'mul01d', '( ( %s x. %s ) x. 0 ) = 0' % (LAM, FG))], 'eqtrd', '%s = 0' % Y)
    fsA = st([w.s([w.s([], 'ssun1', '%s C_ %s' % (DV('N'), U))], 'a1i', '( %s -> %s C_ %s )' % (ante, DV('N'), U)), yca, y01, uf], 'fsumss',
             'sum_ d e. %s %s = sum_ d e. %s %s' % (DV('N'), Y, U, Y))
    # zero on U \ I
    z2 = '( %s /\\ d e. ( %s \\ %s ) )' % (ante, U, I)
    s2 = mkst(w, z2)
    du2 = s2([s2([], 'simpr', 'd e. ( %s \\ %s )' % (U, I))], 'eldifad', 'd e. %s' % U)
    nd2 = s2([s2([], 'simpr', 'd e. ( %s \\ %s )' % (U, I))], 'eldifbd', '-. d e. %s' % I)
    dn2 = s2([lift(w, uns, z2), du2], 'sseldd', 'd e. NN')
    flz = s2([lift(w, Br, z2)], 'flcld', '( |_ ` B ) e. ZZ')
    e2_ = '( %s /\\ d <_ ( |_ ` B ) )' % z2
    ini = w.s([lift(w, dn2, e2_), w.s([], 'simpr', '( %s -> d <_ ( |_ ` B ) )' % e2_), w.s([lift(w, flz, e2_), w.inst('fznn')], 'syl', '( %s -> ( d e. %s <-> ( d e. NN /\\ d <_ ( |_ ` B ) ) ) )' % (e2_, I))],
              'mpbir2and', '( %s -> d e. %s )' % (e2_, I))
    nle = w.s([ini, lift(w, nd2, e2_)], 'pm2.65da', '( %s -> -. d <_ ( |_ ` B ) )' % z2)
    dr2 = s2([dn2], 'nnred', 'd e. RR')
    flr = s2([flz], 'zred', '( |_ ` B ) e. RR')
    fl_lt = s2([nle, s2([flr, dr2], 'ltnled', '( ( |_ ` B ) < d <-> -. d <_ ( |_ ` B ) )')], 'mpbird', '( |_ ` B ) < d')
    blt = s2([fl_lt, s2([lift(w, Br, z2), s2([dn2], 'nnzd', 'd e. ZZ'), w.inst('fllt')], 'syl2anc', '( B < d <-> ( |_ ` B ) < d )')], 'mpbird', 'B < d')
    ble = s2([lift(w, Br, z2), dr2, blt], 'ltled', 'B <_ d')
    l0 = s2([lift(w, hab, z2), dn2, ble, w.inst('z5lam0')], 'syl12anc', '%s = 0' % LAM)
    fg2 = up(w, ante, z2, dn2, fgr, '%s e. RR' % FG)
    if2 = up(w, ante, z2, dn2, ifc, '%s e. CC' % IF)
    y02 = s2([s2([s2([l0], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (LAM, FG, FG)), s2([s2([fg2], 'recnd', '%s e. CC' % FG)], 'mul02d', '( 0 x. %s ) = 0' % FG)], 'eqtrd',
                  '( %s x. %s ) = 0' % (LAM, FG))], 'oveq1d', '%s = ( 0 x. %s )' % (Y, IF))
    y02 = s2([y02, s2([if2], 'mul02d', '( 0 x. %s ) = 0' % IF)], 'eqtrd', '%s = 0' % Y)
    fsB = st([w.s([w.s([], 'ssun2', '%s C_ %s' % (I, U))], 'a1i', '( %s -> %s C_ %s )' % (ante, I, U)), yci, y02, uf], 'fsumss',
             'sum_ d e. %s %s = sum_ d e. %s %s' % (I, Y, U, Y))
    w.qed([st([e4, fsA], 'eqtrd', '%s = sum_ d e. %s %s' % (LHS, U, Y)), fsB], 'eqtr4d', STATEMENTS['z5pwise'])
    return w




def z5lser():
    w = W('z5lser', "Blueprint Lemma 3.1 (Lean LSeries_bvA_psi_eq_LFunction_mul_Mr, Jutila Lemma 1): for Re S > 1 and squarefree R, "
                    "sum_ n a ( n ) psi_R ( n ) chi ( n ) n ^ -S converges to L ( S , chi ) M_R ( S , chi ): the coefficient is a finite "
                    "combination over d <_ z2 of point masses convolved with chi psi_t (z5pwise), each series converges (z5stepb), and "
                    "the finite sum of the limits is L M_R (z5finser, z5mrval).")
    ante = split_imp(STATEMENTS['z5lser'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); sqr = st([], 'simplr', SQF('R'))
    chr_ = st([], 'simprll', CHR); cb = st([], 'simprlr', CB); hs = st([], 'simprr', SRE1)
    rn = st([sqr], 'simpld', 'R e. NN'); sc = st([hs], 'simpld', 'S e. CC')
    cf, c1, cm = chrparts(w, ante, chr_)
    Ar, A0, Br, AB_, abr = habfacts(w, ante, hab)
    I = '( 1 ... ( |_ ` B ) )'
    LAM = '( ( A bvLam B ) ` d )'; FG = FMP('( R gcd d )')
    CD = '( %s x. %s )' % (LAM, FG)
    SBe = lambda e: SB('d', e)
    Gd = '( e e. NN |-> %s )' % SBe('e')
    Gn = '( n e. NN |-> %s )' % SBe('n')
    EUd = EU(QS('d', 'R'))
    LSs = LS()
    Cd = '( C ` d )'; Xd = '( d ^c -u S )'
    Ld = '( ( %s x. %s ) x. ( %s x. %s ) )' % (Cd, Xd, EUd, LSs)
    # d e. I
    ad = '( %s /\\ d e. %s )' % (ante, I)
    sd = mkst(w, ad)
    dn = sd([sd([], 'simpr', 'd e. %s' % I), w.inst('elfznn')], 'syl', 'd e. NN')
    lr = sd([lift(w, abr, ad), dn, w.inst('bvlamre')], 'syl2anc', '%s e. RR' % LAM)
    gn = sd([lift(w, rn, ad), dn, w.inst('gcdnncl')], 'syl2anc', '( R gcd d ) e. NN')
    fgr = fmpre(w, ad, gn, '( R gcd d )')
    cdc = sd([sd([lr, fgr], 'remulcld', '%s e. RR' % CD)], 'recnd', '%s e. CC' % CD)
    hyp3 = st([st([chr_, cb], 'jca', '( %s /\\ %s )' % (CHR, CB)), hs], 'jca', '( ( %s /\\ %s ) /\\ %s )' % (CHR, CB, SRE1))
    sb_ = sd([sd([lift(w, rn, ad), dn], 'jca', '( R e. NN /\\ d e. NN )'), lift(w, hyp3, ad), w.inst('z5stepb')], 'syl2anc', 'seq 1 ( + , %s ) ~~> %s' % (Gn, Ld))
    cbm = w.s([cg(w, SBe('n'), 'n', 'e')], 'cbvmptv', '%s = %s' % (Gn, Gd))
    seqe = w.s([cbm, w.s([], 'seqeq3', '( %s = %s -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (Gn, Gd, Gn, Gd))], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (Gn, Gd))
    brq = w.s([seqe], 'breq1i', '( seq 1 ( + , %s ) ~~> %s <-> seq 1 ( + , %s ) ~~> %s )' % (Gn, Ld, Gd, Ld))
    sbd = sd([sb_, w.s([brq], 'a1i', '( %s -> ( seq 1 ( + , %s ) ~~> %s <-> seq 1 ( + , %s ) ~~> %s ) )' % (ad, Gn, Ld, Gd, Ld))], 'mpbid', 'seq 1 ( + , %s ) ~~> %s' % (Gd, Ld))
    # the values of Gd are complex
    adm = '( %s /\\ ( d e. %s /\\ n e. NN ) )' % (ante, I)
    sm = mkst(w, adm)
    dnm = sm([sm([], 'simprl', 'd e. %s' % I), w.inst('elfznn')], 'syl', 'd e. NN')
    mn = sm([], 'simprr', 'n e. NN')

    def ifc(a, v, dnv, vn):
        """( a -> IF(d,v) e. CC ) and ( a -> SB(d,v) e. CC )"""
        sa = mkst(w, a)
        PT = PSI(TT('d', 'R'), '( %s / d )' % v)
        at = '( %s /\\ d || %s )' % (a, v)
        s_t = mkst(w, at)
        vd = s_t([s_t([], 'simpr', 'd || %s' % v), s_t([lift(w, vn, at), lift(w, dnv, at), w.inst('nndivdvds')], 'syl2anc', '( d || %s <-> ( %s / d ) e. NN )' % (v, v))],
                 'mpbid', '( %s / d ) e. NN' % v)
        tq = s_t([lift(w, rn, at), w.inst('z5tofsq')], 'syl', '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )' % (TT('d', 'R'), TT('d', 'R'), PF(TT('d', 'R')), QS('d', 'R')))
        gt = s_t([s_t([tq], 'simplld', '%s e. NN' % TT('d', 'R')), vd, w.inst('gcdnncl')], 'syl2anc', '( %s gcd ( %s / d ) ) e. NN' % (TT('d', 'R'), v))
        pt = s_t([fmpre(w, at, gt, '( %s gcd ( %s / d ) )' % (TT('d', 'R'), v))], 'recnd', '%s e. CC' % PT)
        tb = s_t([s_t([lift(w, cf, at), lift(w, vn, at)], 'ffvelcdmd', '( C ` %s ) e. CC' % v), pt], 'mulcld', '( ( C ` %s ) x. %s ) e. CC' % (v, PT))
        IFv = 'if ( d || %s , ( ( C ` %s ) x. %s ) , 0 )' % (v, v, PT)
        ic = sa([tb, w.s([], '0cnd', '( ( %s /\\ -. d || %s ) -> 0 e. CC )' % (a, v))], 'ifclda', '%s e. CC' % IFv)
        xv = sa([sa([vn], 'nncnd', '%s e. CC' % v), sa([lift(w, sc, a)], 'negcld', '-u S e. CC')], 'cxpcld', '( %s ^c -u S ) e. CC' % v)
        return ic, sa([ic, xv], 'mulcld', '%s e. CC' % SBe(v)), xv, IFv
    _i, sbm, _x, _f = ifc(adm, 'n', dnm, mn)
    gvm, _ = mpv(w, adm, 'e', 'NN', SBe('e'), 'n', mn, exs=sm([sbm], 'elexd', '%s e. _V' % SBe('n')))
    gmc = sm([gvm, sbm], 'eqeltrd', '( %s ` n ) e. CC' % Gd)
    ifin = st([], 'fzfid', '%s e. Fin' % I)
    fsr = w.s([ifin, gmc, sbd, cdc], 'z5finser', '( %s -> seq 1 ( + , ( n e. NN |-> sum_ d e. %s ( %s x. ( %s ` n ) ) ) ) ~~> sum_ d e. %s ( %s x. %s ) )'
              % (ante, I, CD, Gd, I, CD, Ld))
    # the mapping is the Lemma 3.1 series
    an = '( %s /\\ n e. NN )' % ante
    sn = mkst(w, an)
    nn = sn([], 'simpr', 'n e. NN')
    pwh = sn([lift(w, hab, an), sn([sn([lift(w, sqr, an), lift(w, cf, an)], 'jca', '( %s /\\ C : NN --> CC )' % SQF('R')), nn], 'jca',
                                   '( ( %s /\\ C : NN --> CC ) /\\ n e. NN )' % SQF('R'))],
             'jca', '( %s /\\ ( ( %s /\\ C : NN --> CC ) /\\ n e. NN ) )' % (HAB0, SQF('R')))
    PTn = PSI(TT('d', 'R'), '( n / d )')
    IFn = 'if ( d || n , ( ( C ` n ) x. %s ) , 0 )' % PTn
    P0 = '( ( ( ( A bvA B ) ` n ) x. %s ) x. ( C ` n ) )' % PSI('R', 'n')
    pw = sn([pwh, w.inst('z5pwise')], 'syl', '%s = sum_ d e. %s ( %s x. %s )' % (P0, I, CD, IFn))
    adn = '( %s /\\ d e. %s )' % (an, I)
    sdn = mkst(w, adn)
    dnn = sdn([sdn([], 'simpr', 'd e. %s' % I), w.inst('elfznn')], 'syl', 'd e. NN')
    adn_a = w.s([w.s([], 'simpll', '( %s -> %s )' % (adn, ante)), w.s([], 'simpr', '( %s -> d e. %s )' % (adn, I))], 'jca', '( %s -> %s )' % (adn, ad))
    cdn = w.s([adn_a, cdc], 'syl', '( %s -> %s e. CC )' % (adn, CD))
    ifn, sbn, xnd, _f = ifc(adn, 'n', dnn, lift(w, nn, adn))
    cif = sdn([cdn, ifn], 'mulcld', '( %s x. %s ) e. CC' % (CD, IFn))
    xn = sn([sn([nn], 'nncnd', 'n e. CC'), sn([lift(w, sc, an)], 'negcld', '-u S e. CC')], 'cxpcld', '( n ^c -u S ) e. CC')
    m1 = sn([lift(w, ifin, an), xn, cif], 'fsummulc1', '( sum_ d e. %s ( %s x. %s ) x. ( n ^c -u S ) ) = sum_ d e. %s ( ( %s x. %s ) x. ( n ^c -u S ) )'
            % (I, CD, IFn, I, CD, IFn))
    ma = sdn([cdn, ifn, xnd], 'mulassd', '( ( %s x. %s ) x. ( n ^c -u S ) ) = ( %s x. %s )' % (CD, IFn, CD, SBe('n')))
    gvn, _ = mpv(w, adn, 'e', 'NN', SBe('e'), 'n', lift(w, nn, adn), exs=sdn([sbn], 'elexd', '%s e. _V' % SBe('n')))
    mb = sdn([ma, sdn([sdn([gvn], 'eqcomd', '%s = ( %s ` n )' % (SBe('n'), Gd))], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s ` n ) )' % (CD, SBe('n'), CD, Gd))], 'eqtrd',
             '( ( %s x. %s ) x. ( n ^c -u S ) ) = ( %s x. ( %s ` n ) )' % (CD, IFn, CD, Gd))
    m2 = sn([mb], 'sumeq2dv', 'sum_ d e. %s ( ( %s x. %s ) x. ( n ^c -u S ) ) = sum_ d e. %s ( %s x. ( %s ` n ) )' % (I, CD, IFn, I, CD, Gd))
    lt = sn([sn([sn([pw], 'oveq1d', '%s = ( sum_ d e. %s ( %s x. %s ) x. ( n ^c -u S ) )' % (LT('n'), I, CD, IFn)), m1], 'eqtrd',
                '%s = sum_ d e. %s ( ( %s x. %s ) x. ( n ^c -u S ) )' % (LT('n'), I, CD, IFn)), m2], 'eqtrd', '%s = sum_ d e. %s ( %s x. ( %s ` n ) )' % (LT('n'), I, CD, Gd))
    me = st([lt], 'mpteq2dva', '( n e. NN |-> %s ) = ( n e. NN |-> sum_ d e. %s ( %s x. ( %s ` n ) ) )' % (LT('n'), I, CD, Gd))
    sqe = st([me], 'seqeq3d', 'seq 1 ( + , ( n e. NN |-> %s ) ) = seq 1 ( + , ( n e. NN |-> sum_ d e. %s ( %s x. ( %s ` n ) ) ) )' % (LT('n'), I, CD, Gd))
    VAL = 'sum_ d e. %s ( %s x. %s )' % (I, CD, Ld)
    lim = st([fsr, st([sqe], 'breq1d', '( seq 1 ( + , ( n e. NN |-> %s ) ) ~~> %s <-> seq 1 ( + , ( n e. NN |-> sum_ d e. %s ( %s x. ( %s ` n ) ) ) ) ~~> %s )'
                      % (LT('n'), VAL, I, CD, Gd, VAL))], 'mpbird', 'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> %s' % (LT('n'), VAL))
    # L ( S , chi ) is a complex number
    cbm1 = w.s([w.s([w.s([w.s([], 'fveq2', '( j = m -> ( C ` j ) = ( C ` m ) )')], 'fveq2d', '( j = m -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` m ) ) )')], 'breq1d',
                    '( j = m -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` m ) ) <_ 1 ) )')], 'cbvralvw', '( %s <-> A. m e. NN ( abs ` ( C ` m ) ) <_ 1 )' % CB)
    cbm2 = st([cb, cbm1], 'sylib', 'A. m e. NN ( abs ` ( C ` m ) ) <_ 1')
    LM = '( n e. NN |-> ( ( C ` n ) x. ( n ^c -u S ) ) )'
    dsc = st([st([cf, st([], '1red', '1 e. RR'), cbm2], '3jca', '( C : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( C ` m ) ) <_ 1 )'), hs, w.inst('dsercvg')], 'syl2anc',
             'seq 1 ( + , %s ) e. dom ~~>' % LM)
    ak = '( %s /\\ k e. NN )' % ante
    sk = mkst(w, ak)
    kn = sk([], 'simpr', 'k e. NN')
    xk = sk([sk([lift(w, cf, ak), kn], 'ffvelcdmd', '( C ` k ) e. CC'), sk([sk([kn], 'nncnd', 'k e. CC'), sk([lift(w, sc, ak)], 'negcld', '-u S e. CC')], 'cxpcld',
                                                                                                             '( k ^c -u S ) e. CC')], 'mulcld', '( ( C ` k ) x. ( k ^c -u S ) ) e. CC')
    lv, _ = mpv(w, ak, 'n', 'NN', '( ( C ` n ) x. ( n ^c -u S ) )', 'k', kn)
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    lsc = w.s([nnz, w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ante), lv, xk, dsc], 'isumcl', '( %s -> %s e. CC )' % (ante, LSs))
    # c_d L_d = MRT(d) L
    cdd = sd([lift(w, cf, ad), dn], 'ffvelcdmd', '%s e. CC' % Cd)
    xd = sd([sd([dn], 'nncnd', 'd e. CC'), sd([lift(w, sc, ad)], 'negcld', '-u S e. CC')], 'cxpcld', '%s e. CC' % Xd)
    qss = w.s([w.s([w.s([], 'simpl', '( ( q || R /\\ -. q || d ) -> q || R )')], 'a1i', '( q e. Prime -> ( ( q || R /\\ -. q || d ) -> q || R ) )')], 'ss2rabi',
              '%s C_ %s' % (QS('d', 'R'), PF('R')))
    qfin = sd([sd([lift(w, rn, ad), w.inst('pffinq')], 'syl', '%s e. Fin' % PF('R')), w.s([qss], 'a1i', '( %s -> %s C_ %s )' % (ad, QS('d', 'R'), PF('R')))], 'ssfid',
              '%s e. Fin' % QS('d', 'R'))
    bq = '( %s /\\ p e. %s )' % (ad, QS('d', 'R'))
    pbq = sy(w, bq, pp(w, bq, w.s([], 'simpr', '( %s -> p e. %s )' % (bq, QS('d', 'R')))), 'prmnn', 'p e. NN')
    efc = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % bq), bbc(w, bq, pbq, lift(w, cf, bq), lift(w, sc, bq))], 'addcld', '( %s -> %s e. CC )' % (bq, EF('p')))
    euc = sd([qfin, efc], 'fprodcl', '%s e. CC' % EUd)
    lsd = lift(w, lsc, ad)
    X = CD; Y = Cd; Z = Xd; E = EUd; L = LSs
    yz = '( %s x. %s )' % (Y, Z); el = '( %s x. %s )' % (E, L)
    yzc = sd([cdd, xd], 'mulcld', '%s e. CC' % yz); elc = sd([euc, lsd], 'mulcld', '%s e. CC' % el)
    r1 = sd([sd([cdc, yzc, elc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (X, yz, el, X, yz, el))], 'eqcomd',
            '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (X, yz, el, X, yz, el))
    r2 = sd([sd([sd([cdc, cdd, xd], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (X, Y, Z, X, yz))], 'eqcomd', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (X, yz, X, Y, Z))],
            'oveq1d', '( ( %s x. %s ) x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (X, yz, el, X, Y, Z, el))
    XYZ = '( ( %s x. %s ) x. %s )' % (X, Y, Z)
    xyzc = sd([sd([cdc, cdd], 'mulcld', '( %s x. %s ) e. CC' % (X, Y)), xd], 'mulcld', '%s e. CC' % XYZ)
    r3 = sd([sd([xyzc, euc, lsd], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (XYZ, E, L, XYZ, E, L))], 'eqcomd',
            '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (XYZ, E, L, XYZ, E, L))
    rr = sd([sd([r1, r2], 'eqtrd', '( %s x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (X, Ld, X, Y, Z, el)), r3], 'eqtrd', '( %s x. %s ) = ( %s x. %s )' % (X, Ld, MRT('d'), L))
    sv = st([rr], 'sumeq2dv', '%s = sum_ d e. %s ( %s x. %s )' % (VAL, I, MRT('d'), L))
    mrc = sd([xyzc, euc], 'mulcld', '%s e. CC' % MRT('d'))
    fm = st([ifin, lsc, mrc], 'fsummulc1', '( sum_ d e. %s %s x. %s ) = sum_ d e. %s ( %s x. %s )' % (I, MRT('d'), L, I, MRT('d'), L))
    cvx = st([cf, w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ante), w.inst('fex')], 'syl2anc', 'C e. _V')
    mrv = st([st([st([Ar, Br], 'jca', '( A e. RR /\\ B e. RR )'), st([cvx, rn], 'jca', '( C e. _V /\\ R e. NN )')], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ R e. NN ) )'),
              sc, w.inst('z5mrval')], 'syl2anc', '%s = sum_ d e. %s %s' % (MR(), I, MRT('d')))
    v1 = st([sv, st([fm], 'eqcomd', 'sum_ d e. %s ( %s x. %s ) = ( sum_ d e. %s %s x. %s )' % (I, MRT('d'), L, I, MRT('d'), L))], 'eqtrd',
            '%s = ( sum_ d e. %s %s x. %s )' % (VAL, I, MRT('d'), L))
    v2 = st([v1, st([mrv], 'oveq1d', '( %s x. %s ) = ( sum_ d e. %s %s x. %s )' % (MR(), L, I, MRT('d'), L))], 'eqtr4d', '%s = ( %s x. %s )' % (VAL, MR(), L))
    mrcc = st([mrv, st([ifin, mrc], 'fsumcl', 'sum_ d e. %s %s e. CC' % (I, MRT('d')))], 'eqeltrd', '%s e. CC' % MR())
    v3 = st([v2, st([mrcc, lsc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (MR(), L, L, MR()))], 'eqtrd', '%s = ( %s x. %s )' % (VAL, L, MR()))
    lim2 = st([lim, v3], 'breqtrd', 'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s )' % (LT('n'), L, MR()))
    # convergence and value
    cvg = st([w.s([w.s([], 'climrel', 'Rel ~~>')], 'a1i', '( %s -> Rel ~~> )' % ante), lim2, w.inst('releldm')], 'syl2anc', 'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % LT('n'))
    aj = '( %s /\\ k e. NN )' % ante
    sj = mkst(w, aj)
    jn = sj([], 'simpr', 'k e. NN')
    # LT(j) in CC
    ajc = '( %s /\\ k e. NN )' % ante
    gj = sj([lift(w, rn, aj), jn, w.inst('gcdnncl')], 'syl2anc', '( R gcd k ) e. NN')
    abr_ = lift(w, abr, aj)
    bvj = sj([abr_, jn, w.inst('bvare')], 'syl2anc', '( ( A bvA B ) ` k ) e. RR')
    AJ = '( ( A bvA B ) ` k )'
    t1 = sj([sj([bvj], 'recnd', '%s e. CC' % AJ), sj([fmpre(w, aj, gj, '( R gcd k )')], 'recnd', '%s e. CC' % PSI('R', 'k'))], 'mulcld', '( %s x. %s ) e. CC' % (AJ, PSI('R', 'k')))
    t2 = sj([t1, sj([lift(w, cf, aj), jn], 'ffvelcdmd', '( C ` k ) e. CC')], 'mulcld', '( ( %s x. %s ) x. ( C ` k ) ) e. CC' % (AJ, PSI('R', 'k')))
    t3 = sj([sj([jn], 'nncnd', 'k e. CC'), sj([lift(w, sc, aj)], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')
    ltc = sj([t2, t3], 'mulcld', '%s e. CC' % LT('k'))
    ltv, _ = mpv(w, aj, 'n', 'NN', LT('n'), 'k', jn)
    isv = w.s([nnz, w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ante), ltv, ltc, lim2], 'isumclim', '( %s -> sum_ k e. NN %s = ( %s x. %s ) )' % (ante, LT('k'), L, MR()))
    cbs = w.s([cg(w, LT('k'), 'k', 'n')], 'cbvsumv', 'sum_ k e. NN %s = sum_ n e. NN %s' % (LT('k'), LT('n')))
    val = st([w.s([cbs], 'a1i', '( %s -> sum_ k e. NN %s = sum_ n e. NN %s )' % (ante, LT('k'), LT('n'))), isv], 'eqtr3d', 'sum_ n e. NN %s = ( %s x. %s )' % (LT('n'), L, MR()))
    w.qed([cvg, val], 'jca', STATEMENTS['z5lser'])
    return w


if __name__ == '__main__':
    import z5clib
    for f in sys.argv[1:]:
        z5clib.run(globals()[f]())
