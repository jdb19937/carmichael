"""Sortie v2: squarefree products are coprime (sqfcop) and the truncated Moebius inversion."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))


def sqfcop():
    w = W('sqfcop', 'The factors of a squarefree product are coprime.')
    A = '( A e. NN /\\ B e. NN /\\ ( mmu ` ( A x. B ) ) =/= 0 )'
    G = '( A gcd B )'
    st = mkst(w, A)
    a = st([], 'simp1', 'A e. NN')
    b = st([], 'simp2', 'B e. NN')
    sq = st([], 'simp3', '( mmu ` ( A x. B ) ) =/= 0')
    az = st([a], 'nnzd', 'A e. ZZ')
    bz = st([b], 'nnzd', 'B e. ZZ')
    abn = st([a, b], 'nnmulcld', '( A x. B ) e. NN')
    gnn = st([st([az, bz], 'jca', '( A e. ZZ /\\ B e. ZZ )'),
              st([st([st([b], 'nnne0d', 'B =/= 0')], 'neneqd', '-. B = 0')], 'intnand',
                 '-. ( A = 0 /\\ B = 0 )'), w.inst('gcdn0cl')], 'syl2anc', '%s e. NN' % G)
    gda = st([az, bz, w.inst('gcddvds')], 'syl2anc', '( %s || A /\\ %s || B )' % (G, G))
    gdA = st([gda], 'simpld', '%s || A' % G)
    gdB = st([gda], 'simprd', '%s || B' % G)
    # suppose the gcd is not 1: it has a prime divisor
    C = '( %s /\\ %s =/= 1 )' % (A, G)
    sc = mkst(w, C)
    gne = sc([], 'simpr', '%s =/= 1' % G)
    gnnc = sc([gnn], 'adantr', '%s e. NN' % G)
    guz = sc([sc([gnnc, gne], 'jca', '( %s e. NN /\\ %s =/= 1 )' % (G, G)),
              sc([w.s([], 'eluz2b3', '( %s e. ( ZZ>= ` 2 ) <-> ( %s e. NN /\\ %s =/= 1 ) )' % (G, G, G))],
                 'a1i', '( %s e. ( ZZ>= ` 2 ) <-> ( %s e. NN /\\ %s =/= 1 ) )' % (G, G, G))],
             'mpbird', '%s e. ( ZZ>= ` 2 )' % G)
    ex = sc([guz, w.inst('exprmfct')], 'syl', 'E. q e. Prime q || %s' % G)
    # for such a prime q, q ^ 2 divides A x. B, so the product is not squarefree
    CQ = '( %s /\\ q e. Prime )' % C
    D = '( %s /\\ q || %s )' % (CQ, G)
    sq2 = mkst(w, CQ)
    sd = mkst(w, D)
    qprmq = sq2([], 'simpr', 'q e. Prime')
    qprm = sd([qprmq], 'adantr', 'q e. Prime')
    qdg = sd([], 'simpr', 'q || %s' % G)
    qz = sd([qprm, w.inst('prmz')], 'syl', 'q e. ZZ')
    azd = sd([sq2([sc([az], 'adantr', 'A e. ZZ')], 'adantr', 'A e. ZZ')], 'adantr', 'A e. ZZ')
    bzd = sd([sq2([sc([bz], 'adantr', 'B e. ZZ')], 'adantr', 'B e. ZZ')], 'adantr', 'B e. ZZ')
    gnnd = sd([sq2([gnnc], 'adantr', '%s e. NN' % G)], 'adantr', '%s e. NN' % G)
    gzd = sd([gnnd], 'nnzd', '%s e. ZZ' % G)
    abnd = sd([sq2([sc([abn], 'adantr', '( A x. B ) e. NN')], 'adantr', '( A x. B ) e. NN')],
              'adantr', '( A x. B ) e. NN')
    gdAd = sd([sq2([sc([gdA], 'adantr', '%s || A' % G)], 'adantr', '%s || A' % G)], 'adantr',
              '%s || A' % G)
    gdBd = sd([sq2([sc([gdB], 'adantr', '%s || B' % G)], 'adantr', '%s || B' % G)], 'adantr',
              '%s || B' % G)
    qdA = sd([sd([qz, gzd, azd, w.inst('dvdstr')], 'syl3anc',
                 '( ( q || %s /\\ %s || A ) -> q || A )' % (G, G)),
              sd([qdg, gdAd], 'jca', '( q || %s /\\ %s || A )' % (G, G))], 'mpd', 'q || A')
    qdB = sd([sd([qz, gzd, bzd, w.inst('dvdstr')], 'syl3anc',
                 '( ( q || %s /\\ %s || B ) -> q || B )' % (G, G)),
              sd([qdg, gdBd], 'jca', '( q || %s /\\ %s || B )' % (G, G))], 'mpd', 'q || B')
    s1 = sd([sd([qz, azd, qz, w.inst('dvdsmulc')], 'syl3anc',
                '( q || A -> ( q x. q ) || ( A x. q ) )'), qdA], 'mpd',
            '( q x. q ) || ( A x. q )')
    s2 = sd([sd([qz, bzd, azd, w.inst('dvdscmul')], 'syl3anc',
                '( q || B -> ( A x. q ) || ( A x. B ) )'), qdB], 'mpd',
            '( A x. q ) || ( A x. B )')
    qqz = sd([qz, qz], 'zmulcld', '( q x. q ) e. ZZ')
    aqz = sd([azd, qz], 'zmulcld', '( A x. q ) e. ZZ')
    abz = sd([abnd], 'nnzd', '( A x. B ) e. ZZ')
    s3 = sd([sd([qqz, aqz, abz, w.inst('dvdstr')], 'syl3anc',
                '( ( ( q x. q ) || ( A x. q ) /\\ ( A x. q ) || ( A x. B ) ) -> ( q x. q ) || ( A x. B ) )'),
             sd([s1, s2], 'jca',
                '( ( q x. q ) || ( A x. q ) /\\ ( A x. q ) || ( A x. B ) )')], 'mpd',
            '( q x. q ) || ( A x. B )')
    sqv = sd([sd([qz], 'zcnd', 'q e. CC'), w.inst('sqval')], 'syl', '( q ^ 2 ) = ( q x. q )')
    s4 = sd([sqv, s3], 'eqbrtrd', '( q ^ 2 ) || ( A x. B )')
    quz = sd([qprm, w.inst('prmuz2')], 'syl', 'q e. ( ZZ>= ` 2 )')
    mu0 = sd([abnd, quz, s4, w.inst('muval1')], 'syl3anc', '( mmu ` ( A x. B ) ) = 0')
    sqd = sd([sq2([sc([sq], 'adantr', '( mmu ` ( A x. B ) ) =/= 0')], 'adantr',
                  '( mmu ` ( A x. B ) ) =/= 0')], 'adantr', '( mmu ` ( A x. B ) ) =/= 0')
    con = sd([mu0, sqd], 'pm2.21ddne', '%s = 1' % G)
    exd = w.s([con], 'ex', '( %s -> ( q || %s -> %s = 1 ) )' % (CQ, G, G))
    rl = w.s([exd], 'rexlimdva', '( %s -> ( E. q e. Prime q || %s -> %s = 1 ) )' % (C, G, G))
    g1 = sc([ex, rl], 'mpd', '%s = 1' % G)
    triv = w.s([], 'simpr', '( ( %s /\\ %s = 1 ) -> %s = 1 )' % (A, G, G))
    w.qed([triv, g1], 'pm2.61dane', '( %s -> %s = 1 )' % (A, G))
    return w


DVL = '{ x e. NN | x || L }'
DVK = '{ x e. NN | x || K }'


def muinvlem0():
    w = W('muinvlem0',
          'The product identity behind the truncated Moebius inversion.')
    A = ('( ( L e. NN /\\ K e. NN /\\ ( L gcd K ) = 1 ) /\\ '
         '( j e. %s /\\ k e. %s ) )' % (DVL, DVK))
    LHS = '( if ( L || j , ( mmu ` j ) , 0 ) x. ( mmu ` k ) )'
    RHS = 'if ( L || ( j x. k ) , ( mmu ` ( j x. k ) ) , 0 )'
    st = mkst(w, A)
    l = st([], 'simpl1', 'L e. NN')
    kk = st([], 'simpl2', 'K e. NN')
    cop = st([], 'simpl3', '( L gcd K ) = 1')
    jin = st([], 'simprl', 'j e. %s' % DVL)
    kin = st([], 'simprr', 'k e. %s' % DVK)
    jnn = st([jin, w.inst('elrabi')], 'syl', 'j e. NN')
    knn = st([kin, w.inst('elrabi')], 'syl', 'k e. NN')
    eljl = w.s([w.s([], 'breq1', '( x = j -> ( x || L <-> j || L ) )')], 'elrab',
               '( j e. %s <-> ( j e. NN /\\ j || L ) )' % DVL)
    elkk = w.s([w.s([], 'breq1', '( x = k -> ( x || K <-> k || K ) )')], 'elrab',
               '( k e. %s <-> ( k e. NN /\\ k || K ) )' % DVK)
    jdl = st([st([st([eljl], 'a1i', '( j e. %s <-> ( j e. NN /\\ j || L ) )' % DVL), jin],
                 'mpbid', '( j e. NN /\\ j || L )')], 'simprd', 'j || L')
    kdk = st([st([st([elkk], 'a1i', '( k e. %s <-> ( k e. NN /\\ k || K ) )' % DVK), kin],
                 'mpbid', '( k e. NN /\\ k || K )')], 'simprd', 'k || K')
    lz = st([l], 'nnzd', 'L e. ZZ')
    kz = st([kk], 'nnzd', 'K e. ZZ')
    jz = st([jnn], 'nnzd', 'j e. ZZ')
    kkz = st([knn], 'nnzd', 'k e. ZZ')
    muk = st([st([knn, w.inst('mucl')], 'syl', '( mmu ` k ) e. ZZ')], 'zcnd', '( mmu ` k ) e. CC')
    # ( L gcd k ) = 1 and ( j gcd k ) = 1
    lk1 = st([st([lz, kkz, kz], '3jca', '( L e. ZZ /\\ k e. ZZ /\\ K e. ZZ )'),
              st([cop, kdk], 'jca', '( ( L gcd K ) = 1 /\\ k || K )'), w.inst('rpdvds')],
             'syl2anc', '( L gcd k ) = 1')
    kl1 = st([st([lz, kkz], 'gcdcomd', '( L gcd k ) = ( k gcd L )'), lk1], 'eqtr3d',
             '( k gcd L ) = 1')
    kj1 = st([st([kkz, jz, lz], '3jca', '( k e. ZZ /\\ j e. ZZ /\\ L e. ZZ )'),
              st([kl1, jdl], 'jca', '( ( k gcd L ) = 1 /\\ j || L )'), w.inst('rpdvds')],
             'syl2anc', '( k gcd j ) = 1')
    jk1 = st([st([jz, kkz], 'gcdcomd', '( j gcd k ) = ( k gcd j )'), kj1], 'eqtrd',
             '( j gcd k ) = 1')
    mumul = st([st([jnn, knn, jk1], '3jca', '( j e. NN /\\ k e. NN /\\ ( j gcd k ) = 1 )'),
                w.inst('mumul')], 'syl',
               '( mmu ` ( j x. k ) ) = ( ( mmu ` j ) x. ( mmu ` k ) )')
    # case L || j
    C1 = '( %s /\\ L || j )' % A
    s1 = mkst(w, C1)
    ldj = s1([], 'simpr', 'L || j')
    jnn1 = s1([jnn], 'adantr', 'j e. NN')
    l1 = s1([l], 'adantr', 'L e. NN')
    jeq = s1([s1([s1([jnn1], 'nnnn0d', 'j e. NN0'), s1([l1], 'nnnn0d', 'L e. NN0')], 'jca',
                 '( j e. NN0 /\\ L e. NN0 )'),
              s1([s1([jdl], 'adantr', 'j || L'), ldj], 'jca', '( j || L /\\ L || j )'),
              w.inst('dvdseq')], 'syl2anc', 'j = L')
    jdjk = s1([s1([jz], 'adantr', 'j e. ZZ'), s1([kkz], 'adantr', 'k e. ZZ'),
               w.inst('dvdsmul1')], 'syl2anc', 'j || ( j x. k )')
    ldjk = s1([s1([jeq], 'eqcomd', 'L = j'), jdjk], 'eqbrtrd', 'L || ( j x. k )')
    lhs1 = s1([s1([ldj], 'iftrued', 'if ( L || j , ( mmu ` j ) , 0 ) = ( mmu ` j )')], 'oveq1d',
              '%s = ( ( mmu ` j ) x. ( mmu ` k ) )' % LHS)
    rhs1 = s1([ldjk], 'iftrued', '%s = ( mmu ` ( j x. k ) )' % RHS)
    case1 = s1([lhs1, s1([rhs1, s1([mumul], 'adantr',
               '( mmu ` ( j x. k ) ) = ( ( mmu ` j ) x. ( mmu ` k ) )')], 'eqtrd',
               '%s = ( ( mmu ` j ) x. ( mmu ` k ) )' % RHS)], 'eqtr4d', '%s = %s' % (LHS, RHS))
    # case -. L || j
    C2 = '( %s /\\ -. L || j )' % A
    s2 = mkst(w, C2)
    nldj = s2([], 'simpr', '-. L || j')
    lhs2a = s2([s2([nldj], 'iffalsed', 'if ( L || j , ( mmu ` j ) , 0 ) = 0')], 'oveq1d',
               '%s = ( 0 x. ( mmu ` k ) )' % LHS)
    lhs2 = s2([lhs2a, s2([s2([muk], 'adantr', '( mmu ` k ) e. CC')], 'mul02d',
                         '( 0 x. ( mmu ` k ) ) = 0')], 'eqtrd', '%s = 0' % LHS)
    C3 = '( %s /\\ L || ( j x. k ) )' % C2
    s3 = mkst(w, C3)
    ldjk3 = s3([], 'simpr', 'L || ( j x. k )')
    jzc = s3([s3([s2([jz], 'adantr', 'j e. ZZ')], 'adantr', 'j e. ZZ')], 'zcnd', 'j e. CC')
    kzc = s3([s3([s2([kkz], 'adantr', 'k e. ZZ')], 'adantr', 'k e. ZZ')], 'zcnd', 'k e. CC')
    cmm = s3([jzc, kzc], 'mulcomd', '( j x. k ) = ( k x. j )')
    ldkj = s3([ldjk3, cmm], 'breqtrd', 'L || ( k x. j )')
    lz3 = s3([s2([lz], 'adantr', 'L e. ZZ')], 'adantr', 'L e. ZZ')
    kz3 = s3([s2([kkz], 'adantr', 'k e. ZZ')], 'adantr', 'k e. ZZ')
    jz3 = s3([s2([jz], 'adantr', 'j e. ZZ')], 'adantr', 'j e. ZZ')
    lk13 = s3([s2([lk1], 'adantr', '( L gcd k ) = 1')], 'adantr', '( L gcd k ) = 1')
    cd = s3([lz3, kz3, jz3, w.inst('coprmdvds')], 'syl3anc',
            '( ( L || ( k x. j ) /\\ ( L gcd k ) = 1 ) -> L || j )')
    ldj3 = s3([cd, s3([ldkj, lk13], 'jca', '( L || ( k x. j ) /\\ ( L gcd k ) = 1 )')], 'mpd',
              'L || j')
    nl3 = s3([nldj], 'adantr', '-. L || j')
    ndv = s2([nldj, w.s([ldj3], 'ex', '( %s -> ( L || ( j x. k ) -> L || j ) )' % C2)], 'mtod',
             '-. L || ( j x. k )')
    rhs2 = s2([ndv], 'iffalsed', '%s = 0' % RHS)
    case2 = s2([lhs2, rhs2], 'eqtr4d', '%s = %s' % (LHS, RHS))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s = %s )' % (A, LHS, RHS))
    return w


def IFM(v): return 'if ( L || %s , ( mmu ` %s ) , 0 )' % (v, v)
DVM = '{ x e. NN | x || M }'
MDL = '( M / L )'
DVQ = '{ x e. NN | x || %s }' % MDL
DVZ = '{ x e. NN | x || ( L x. %s ) }' % MDL


def muinvlem1():
    w = W('muinvlem1', 'The truncated Moebius inversion when L divides M.')
    A = '( ( M e. NN /\\ ( mmu ` M ) =/= 0 /\\ L e. NN ) /\\ L || M )'
    SJ = 'sum_ j e. %s %s' % (DVL, IFM('j'))
    SK = 'sum_ k e. %s ( mmu ` k ) ' % DVQ
    SK = SK.strip()
    SD = 'sum_ d e. %s %s' % (DVM, IFM('d'))
    SZ = 'sum_ d e. %s %s' % (DVZ, IFM('d'))
    st = mkst(w, A)
    m = st([], 'simpl1', 'M e. NN')
    sq = st([], 'simpl2', '( mmu ` M ) =/= 0')
    l = st([], 'simpl3', 'L e. NN')
    ldm = st([], 'simpr', 'L || M')
    mc = st([m], 'nncnd', 'M e. CC')
    lc = st([l], 'nncnd', 'L e. CC')
    lne = st([l], 'nnne0d', 'L =/= 0')
    lz = st([l], 'nnzd', 'L e. ZZ')
    knn = st([st([m, l, w.inst('nndivdvds')], 'syl2anc',
                 '( L || M <-> %s e. NN )' % MDL), ldm], 'mpbid', '%s e. NN' % MDL)
    mul = st([mc, lc, lne, w.inst('divcan2')], 'syl3anc', '( L x. %s ) = M' % MDL)
    sqlk = st([st([mul], 'fveq2d', '( mmu ` ( L x. %s ) ) = ( mmu ` M )' % MDL), sq], 'eqnetrd',
              '( mmu ` ( L x. %s ) ) =/= 0' % MDL)
    cop = st([st([l, knn, sqlk], '3jca',
                 '( L e. NN /\\ %s e. NN /\\ ( mmu ` ( L x. %s ) ) =/= 0 )' % (MDL, MDL)),
              w.inst('sqfcop')], 'syl', '( L gcd %s ) = 1' % MDL)
    # the multiplicative splitting of the divisor sum
    xdef = w.s([], 'eqid', '%s = %s' % (DVL, DVL))
    ydef = w.s([], 'eqid', '%s = %s' % (DVQ, DVQ))
    zdef = w.s([], 'eqid', '%s = %s' % (DVZ, DVZ))
    BJ = '( %s /\\ j e. %s )' % (A, DVL)
    fj = mkst(w, BJ)
    jnn = fj([fj([], 'simpr', 'j e. %s' % DVL), w.inst('elrabi')], 'syl', 'j e. NN')
    mujc = fj([fj([jnn, w.inst('mucl')], 'syl', '( mmu ` j ) e. ZZ')], 'zcnd', '( mmu ` j ) e. CC')
    zc = fj([], '0cnd', '0 e. CC')
    h4 = fj([mujc, zc], 'ifcld', '%s e. CC' % IFM('j'))
    BK = '( %s /\\ k e. %s )' % (A, DVQ)
    fk = mkst(w, BK)
    knn2 = fk([fk([], 'simpr', 'k e. %s' % DVQ), w.inst('elrabi')], 'syl', 'k e. NN')
    h5 = fk([fk([knn2, w.inst('mucl')], 'syl', '( mmu ` k ) e. ZZ')], 'zcnd', '( mmu ` k ) e. CC')
    BJK = '( %s /\\ ( j e. %s /\\ k e. %s ) )' % (A, DVL, DVQ)
    fjk = mkst(w, BJK)
    h6 = fjk([fjk([fjk([l], 'adantr', 'L e. NN'), fjk([knn], 'adantr', '%s e. NN' % MDL),
                   fjk([cop], 'adantr', '( L gcd %s ) = 1' % MDL)], '3jca',
                  '( L e. NN /\\ %s e. NN /\\ ( L gcd %s ) = 1 )' % (MDL, MDL)),
              fjk([], 'simpr', '( j e. %s /\\ k e. %s )' % (DVL, DVQ)), w.inst('muinvlem0')],
             'syl2anc',
             '( %s x. ( mmu ` k ) ) = if ( L || ( j x. k ) , ( mmu ` ( j x. k ) ) , 0 )' % IFM('j'))
    h7a = w.s([], 'breq2', '( d = ( j x. k ) -> ( L || d <-> L || ( j x. k ) ) )')
    h7b = w.s([], 'fveq2', '( d = ( j x. k ) -> ( mmu ` d ) = ( mmu ` ( j x. k ) ) )')
    h7 = w.s([h7a, h7b], 'ifbieq1d',
             '( d = ( j x. k ) -> %s = if ( L || ( j x. k ) , ( mmu ` ( j x. k ) ) , 0 ) )' % IFM('d'))
    mul2 = st([l, knn, cop, xdef, ydef, zdef, h4, h5, h6, h7], 'fsumdvdsmul',
              '( %s x. %s ) = %s' % (SJ, SK, SZ))
    # the index set of the right-hand sum is the divisors of M
    zrab = st([st([mul], 'breq2d', '( x || ( L x. %s ) <-> x || M )' % MDL)], 'rabbidv',
              '%s = %s' % (DVZ, DVM))
    szm = st([zrab], 'sumeq1d', '%s = %s' % (SZ, SD))
    prod = st([mul2, szm], 'eqtrd', '( %s x. %s ) = %s' % (SJ, SK, SD))
    # the first factor is the Moebius function of L
    lid = st([lz, w.inst('iddvds')], 'syl', 'L || L')
    ellr = w.s([w.s([], 'breq1', '( x = L -> ( x || L <-> L || L ) )')], 'elrab',
               '( L e. %s <-> ( L e. NN /\\ L || L ) )' % DVL)
    linl = st([st([ellr], 'a1i', '( L e. %s <-> ( L e. NN /\\ L || L ) )' % DVL),
               st([l, lid], 'jca', '( L e. NN /\\ L || L )')], 'mpbird', 'L e. %s' % DVL)
    snss = st([linl], 'snssd', '{ L } C_ %s' % DVL)
    finl = st([l, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVL)
    BJD = '( %s /\\ j e. ( %s \\ { L } ) )' % (A, DVL)
    fjd = mkst(w, BJD)
    jdif = fjd([], 'simpr', 'j e. ( %s \\ { L } )' % DVL)
    jinl = fjd([jdif, w.inst('eldifi')], 'syl', 'j e. %s' % DVL)
    jnel = fjd([jdif, w.inst('eldifsni')], 'syl', 'j =/= L')
    jnnd = fjd([jinl, w.inst('elrabi')], 'syl', 'j e. NN')
    eljl = w.s([w.s([], 'breq1', '( x = j -> ( x || L <-> j || L ) )')], 'elrab',
               '( j e. %s <-> ( j e. NN /\\ j || L ) )' % DVL)
    jdl = fjd([fjd([fjd([eljl], 'a1i', '( j e. %s <-> ( j e. NN /\\ j || L ) )' % DVL), jinl],
                   'mpbid', '( j e. NN /\\ j || L )')], 'simprd', 'j || L')
    CJ2 = '( %s /\\ L || j )' % BJD
    fj2 = mkst(w, CJ2)
    jnn0 = fjd([jnnd], 'nnnn0d', 'j e. NN0')
    lnn0 = fjd([fjd([l], 'adantr', 'L e. NN')], 'nnnn0d', 'L e. NN0')
    jeq = fj2([fj2([fj2([jnn0], 'adantr', 'j e. NN0'), fj2([lnn0], 'adantr', 'L e. NN0')], 'jca',
                   '( j e. NN0 /\\ L e. NN0 )'),
               fj2([fj2([jdl], 'adantr', 'j || L'), fj2([], 'simpr', 'L || j')], 'jca',
                   '( j || L /\\ L || j )'), w.inst('dvdseq')], 'syl2anc', 'j = L')
    nldj = fjd([fjd([jnel], 'neneqd', '-. j = L'), w.s([jeq], 'ex',
               '( %s -> ( L || j -> j = L ) )' % BJD)], 'mtod', '-. L || j')
    vanj = fjd([nldj], 'iffalsed', '%s = 0' % IFM('j'))
    BJS = '( %s /\\ j e. { L } )' % A
    fjs = mkst(w, BJS)
    jsn = fjs([], 'simpr', 'j e. { L }')
    jsnn = fjs([fjs([jsn, w.inst('elsni')], 'syl', 'j = L'), fjs([l], 'adantr', 'L e. NN')],
               'eqeltrd', 'j e. NN')
    mujs = fjs([fjs([jsnn, w.inst('mucl')], 'syl', '( mmu ` j ) e. ZZ')], 'zcnd',
               '( mmu ` j ) e. CC')
    ifcs = fjs([mujs, fjs([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFM('j'))
    ssj = st([snss, ifcs, vanj, finl], 'fsumss', 'sum_ j e. { L } %s = %s' % (IFM('j'), SJ))
    subl = w.s([w.s([], 'breq2', '( j = L -> ( L || j <-> L || L ) )'),
                w.s([], 'fveq2', '( j = L -> ( mmu ` j ) = ( mmu ` L ) )')], 'ifbieq1d',
               '( j = L -> %s = if ( L || L , ( mmu ` L ) , 0 ) )' % IFM('j'))
    muLc = st([st([l, w.inst('mucl')], 'syl', '( mmu ` L ) e. ZZ')], 'zcnd', '( mmu ` L ) e. CC')
    ifLc = st([muLc, st([], '0cnd', '0 e. CC')], 'ifcld', 'if ( L || L , ( mmu ` L ) , 0 ) e. CC')
    lex = st([st([l], 'nncnd', 'L e. CC'), w.inst('elex')], 'syl', 'L e. _V')
    sni = w.s([subl], 'sumsn',
              '( ( L e. _V /\\ if ( L || L , ( mmu ` L ) , 0 ) e. CC ) -> '
              'sum_ j e. { L } %s = if ( L || L , ( mmu ` L ) , 0 ) )' % IFM('j'))
    snval = st([lex, ifLc, sni], 'syl2anc',
               'sum_ j e. { L } %s = if ( L || L , ( mmu ` L ) , 0 )' % IFM('j'))
    iftL = st([lid], 'iftrued', 'if ( L || L , ( mmu ` L ) , 0 ) = ( mmu ` L )')
    sjval = st([st([ssj], 'eqcomd', '%s = sum_ j e. { L } %s' % (SJ, IFM('j'))),
                st([snval, iftL], 'eqtrd', 'sum_ j e. { L } %s = ( mmu ` L )' % IFM('j'))], 'eqtrd',
               '%s = ( mmu ` L )' % SJ)
    # the second factor is the Moebius divisor sum
    cbvq = st([w.s([], 'cbvrabv', '%s = { n e. NN | n || %s }' % (DVQ, MDL))], 'a1i',
              '%s = { n e. NN | n || %s }' % (DVQ, MDL))
    msum = st([knn, w.inst('musum')], 'syl',
              'sum_ k e. { n e. NN | n || %s } ( mmu ` k ) = if ( %s = 1 , 1 , 0 )' % (MDL, MDL))
    skval = st([st([cbvq], 'sumeq1d', '%s = sum_ k e. { n e. NN | n || %s } ( mmu ` k )' % (SK, MDL)),
                msum], 'eqtrd', '%s = if ( %s = 1 , 1 , 0 )' % (SK, MDL))
    # the condition M / L = 1 is L = M
    dq1 = st([mc, lc, lne, w.inst('diveq1')], 'syl3anc', '( %s = 1 <-> M = L )' % MDL)
    eqcm = st([dq1, st([w.s([], 'eqcom', '( M = L <-> L = M )')], 'a1i',
                       '( M = L <-> L = M )')], 'bitrd', '( %s = 1 <-> L = M )' % MDL)
    ifeq = st([eqcm], 'ifbid', 'if ( %s = 1 , 1 , 0 ) = if ( L = M , 1 , 0 )' % MDL)
    skval2 = st([skval, ifeq], 'eqtrd', '%s = if ( L = M , 1 , 0 )' % SK)
    # assemble
    pr2 = st([sjval, skval2], 'oveq12d',
             '( %s x. %s ) = ( ( mmu ` L ) x. if ( L = M , 1 , 0 ) )' % (SJ, SK))
    ov = st([w.s([], 'ovif2',
                 '( ( mmu ` L ) x. if ( L = M , 1 , 0 ) ) = '
                 'if ( L = M , ( ( mmu ` L ) x. 1 ) , ( ( mmu ` L ) x. 0 ) )')], 'a1i',
            '( ( mmu ` L ) x. if ( L = M , 1 , 0 ) ) = '
            'if ( L = M , ( ( mmu ` L ) x. 1 ) , ( ( mmu ` L ) x. 0 ) )')
    b1 = st([muLc], 'mulridd', '( ( mmu ` L ) x. 1 ) = ( mmu ` L )')
    b2 = st([muLc], 'mul01d', '( ( mmu ` L ) x. 0 ) = 0')
    ifv = st([st([], 'biidd', '( L = M <-> L = M )'), b1, b2], 'ifbieq12d',
             'if ( L = M , ( ( mmu ` L ) x. 1 ) , ( ( mmu ` L ) x. 0 ) ) = if ( L = M , ( mmu ` L ) , 0 )')
    rhs = st([ov, ifv], 'eqtrd',
             '( ( mmu ` L ) x. if ( L = M , 1 , 0 ) ) = if ( L = M , ( mmu ` L ) , 0 )')
    w.qed([st([prod], 'eqcomd', '%s = ( %s x. %s )' % (SD, SJ, SK)),
           st([pr2, rhs], 'eqtrd', '( %s x. %s ) = if ( L = M , ( mmu ` L ) , 0 )' % (SJ, SK))],
          'eqtrd', '( %s -> %s = if ( L = M , ( mmu ` L ) , 0 ) )' % (A, SD))
    return w


def muinvdvds():
    w = W('muinvdvds',
          'The truncated Moebius sum over the divisors of a squarefree number that are multiples '
          'of L detects L = M.')
    A = '( M e. NN /\\ ( mmu ` M ) =/= 0 /\\ L e. NN )'
    SD = 'sum_ d e. %s %s' % (DVM, IFM('d'))
    RHS = 'if ( L = M , ( mmu ` L ) , 0 )'
    C1 = '( %s /\\ L || M )' % A
    C2 = '( %s /\\ -. L || M )' % A
    st = mkst(w, A)
    s1 = mkst(w, C1)
    s2 = mkst(w, C2)
    case1 = s1([], 'muinvlem1', '%s = %s' % (SD, RHS))
    # case L does not divide M
    m2 = s2([], 'simpl1', 'M e. NN')
    l2 = s2([], 'simpl3', 'L e. NN')
    nld = s2([], 'simpr', '-. L || M')
    fin = s2([m2, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVM)
    BD = '( %s /\\ d e. %s )' % (C2, DVM)
    fd = mkst(w, BD)
    dinm = fd([], 'simpr', 'd e. %s' % DVM)
    dnn = fd([dinm, w.inst('elrabi')], 'syl', 'd e. NN')
    eldm = w.s([w.s([], 'breq1', '( x = d -> ( x || M <-> d || M ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DVM)
    ddm = fd([fd([fd([eldm], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DVM), dinm],
                 'mpbid', '( d e. NN /\\ d || M )')], 'simprd', 'd || M')
    lz = fd([fd([l2], 'adantr', 'L e. NN')], 'nnzd', 'L e. ZZ')
    dz = fd([dnn], 'nnzd', 'd e. ZZ')
    mz = fd([fd([m2], 'adantr', 'M e. NN')], 'nnzd', 'M e. ZZ')
    tr = fd([lz, dz, mz, w.inst('dvdstr')], 'syl3anc',
            '( ( L || d /\\ d || M ) -> L || M )')
    imp = w.s([tr], 'expd', '( %s -> ( L || d -> ( d || M -> L || M ) ) )' % BD)
    imp2 = fd([imp, ddm], 'mpid', '( L || d -> L || M )')
    nldd = fd([fd([nld], 'adantr', '-. L || M'), imp2], 'mtod', '-. L || d')
    van = fd([nldd], 'iffalsed', '%s = 0' % IFM('d'))
    sz = s2([van], 'sumeq2dv', '%s = sum_ d e. %s 0' % (SD, DVM))
    orr = s2([fin], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (DVM, DVM))
    z0 = s2([orr, w.inst('sumz')], 'syl', 'sum_ d e. %s 0 = 0' % DVM)
    lhs2 = s2([sz, z0], 'eqtrd', '%s = 0' % SD)
    # L =/= M
    lzz = s2([l2], 'nnzd', 'L e. ZZ')
    lid = s2([lzz, w.inst('iddvds')], 'syl', 'L || L')
    CE = '( %s /\\ L = M )' % C2
    se = mkst(w, CE)
    leq = se([], 'simpr', 'L = M')
    ldm2 = se([se([lid], 'adantr', 'L || L'), leq], 'breqtrd', 'L || M')
    lne = s2([nld, w.s([ldm2], 'ex', '( %s -> ( L = M -> L || M ) )' % C2)], 'mtod', '-. L = M')
    rhs2 = s2([lne], 'iffalsed', '%s = 0' % RHS)
    case2 = s2([lhs2, rhs2], 'eqtr4d', '%s = %s' % (SD, RHS))
    w.qed([case1, case2], 'pm2.61dan', '( %s -> %s = %s )' % (A, SD, RHS))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['sqfcop']:
        globals()[f]().run()
