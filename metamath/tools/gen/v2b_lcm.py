"""Sortie v2b: the lcm fibre count, 3 ^ omega.

hashdv    ( # ` divisors of D ) = 2 ^ omega( D ) for squarefree D
lcmequiv  for D, E || N squarefree: N = ( D lcm E ) <-> ( N / D ) || E
lcmfib    the fibre sum over the divisors of N with ( N / D ) || e is ( # ` DV ( D ) )
lcmcnt    the number of divisor pairs with least common multiple N is 3 ^ omega( N )
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *


def hashdv():
    w = W('hashdv', 'The number of divisors of a squarefree number is two to the number of its '
                    'prime divisors.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    st = mkst(w, A)
    DVD = DV('D')
    SD = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || D ) }'
    PFP = PF('D', 'p')
    PFR = PF('D', 'r')
    FF = '( n e. %s |-> { p e. Prime | p || n } )' % SD
    GG = '( m e. NN |-> ( r e. Prime |-> ( r pCnt m ) ) )'
    dnn = st([], 'simpl', 'D e. NN')
    dsq = st([], 'simpr', '( mmu ` D ) =/= 0')
    # the divisors of a squarefree number are squarefree
    BX = '( %s /\\ x e. NN )' % A
    bx = mkst(w, BX)
    xnn = bx([], 'simpr', 'x e. NN')
    triple = '( D e. NN /\\ x e. NN /\\ x || D )'
    CX = '( %s /\\ x || D )' % BX
    cx = mkst(w, CX)
    imp1 = cx([cx([cx([bx([dnn], 'adantr', 'D e. NN')], 'adantr', 'D e. NN'),
                   cx([xnn], 'adantr', 'x e. NN'), cx([], 'simpr', 'x || D')], '3jca', triple),
               w.inst('dvdssqf')], 'syl',
              '( ( mmu ` D ) =/= 0 -> ( mmu ` x ) =/= 0 )')
    imp2 = cx([imp1, cx([bx([dsq], 'adantr', '( mmu ` D ) =/= 0')], 'adantr',
                        '( mmu ` D ) =/= 0')], 'mpd', '( mmu ` x ) =/= 0')
    conj = cx([imp2, cx([], 'simpr', 'x || D')], 'jca',
              '( ( mmu ` x ) =/= 0 /\\ x || D )')
    f1 = bx([conj], 'ex', '( x || D -> ( ( mmu ` x ) =/= 0 /\\ x || D ) )')
    b1 = bx([w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || D ) -> x || D )')], 'a1i',
            '( ( ( mmu ` x ) =/= 0 /\\ x || D ) -> x || D )')
    bi = bx([f1, b1], 'impbid', '( x || D <-> ( ( mmu ` x ) =/= 0 /\\ x || D ) )')
    same = st([bi], 'rabbidva', '%s = %s' % (DVD, SD))
    # the powerset bijection
    hS = w.s([], 'eqid', '%s = %s' % (SD, SD))
    hF = w.s([], 'eqid', '%s = %s' % (FF, FF))
    q1 = w.s([], 'oveq1', '( r = p -> ( r pCnt m ) = ( p pCnt m ) )')
    g1 = w.s([q1], 'cbvmptv',
             '( r e. Prime |-> ( r pCnt m ) ) = ( p e. Prime |-> ( p pCnt m ) )')
    g2 = w.s([g1], 'mpteq2i',
             '( m e. NN |-> ( r e. Prime |-> ( r pCnt m ) ) ) = '
             '( m e. NN |-> ( p e. Prime |-> ( p pCnt m ) ) )')
    q2 = w.s([], 'oveq2', '( m = n -> ( p pCnt m ) = ( p pCnt n ) )')
    q3 = w.s([q2], 'mpteq2dv',
             '( m = n -> ( p e. Prime |-> ( p pCnt m ) ) = ( p e. Prime |-> ( p pCnt n ) ) )')
    g3 = w.s([q3], 'cbvmptv',
             '( m e. NN |-> ( p e. Prime |-> ( p pCnt m ) ) ) = '
             '( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )')
    hG = w.s([g2, g3], 'eqtri',
             '%s = ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )' % GG)
    inst = w.s([hS, hF, hG], 'sqff1o',
               '( D e. NN -> %s : %s -1-1-onto-> ~P %s )' % (FF, SD, PFP))
    f1o = st([dnn, inst], 'syl', '%s : %s -1-1-onto-> ~P %s' % (FF, SD, PFP))
    finD = st([dnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVD)
    finS = st([same, finD], 'eqeltrd', '%s e. Fin' % SD) if False else \
        st([st([same], 'eqcomd', '%s = %s' % (SD, DVD)), finD], 'eqeltrd', '%s e. Fin' % SD)
    en = st([st([finS, f1o], 'jca', '( %s e. Fin /\\ %s : %s -1-1-onto-> ~P %s )'
                % (SD, FF, SD, PFP)), w.inst('f1oeng')], 'syl', '%s ~~ ~P %s' % (SD, PFP))
    heq = st([en, w.inst('hasheni')], 'syl', '( # ` %s ) = ( # ` ~P %s )' % (SD, PFP))
    finP = st([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PFP)
    hpw = st([finP, w.inst('hashpw')], 'syl',
             '( # ` ~P %s ) = ( 2 ^ ( # ` %s ) )' % (PFP, PFP))
    cbv = st([st([w.s([], 'cbvrabv', '%s = %s' % (PFP, PFR))], 'a1i', '%s = %s' % (PFP, PFR))],
             'fveq2d', '( # ` %s ) = ( # ` %s )' % (PFP, PFR))
    rhs = st([hpw, st([cbv], 'oveq2d',
                      '( 2 ^ ( # ` %s ) ) = ( 2 ^ ( # ` %s ) )' % (PFP, PFR))], 'eqtrd',
             '( # ` ~P %s ) = ( 2 ^ ( # ` %s ) )' % (PFP, PFR))
    lhs = st([same], 'fveq2d', '( # ` %s ) = ( # ` %s )' % (DVD, SD))
    w.qed([lhs, st([heq, rhs], 'eqtrd', '( # ` %s ) = ( 2 ^ ( # ` %s ) )' % (SD, PFR))],
          'eqtrd', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` %s ) ) )' % (A, DVD, PFR))
    return w


def lcmequiv():
    w = W('lcmequiv', 'For divisors D and E of a squarefree number N, the least common multiple '
                      'of D and E is N if and only if N / D divides E.')
    A = ('( ( N e. NN /\ ( mmu ` N ) =/= 0 ) /\ ( D e. NN /\ D || N ) /\ '
         '( E e. NN /\ E || N ) )')
    Q = '( N / D )'
    LC = '( D lcm E )'
    st = mkst(w, A)
    nnn = st([], 'simp1l', 'N e. NN')
    nsq = st([], 'simp1r', '( mmu ` N ) =/= 0')
    dnn = st([], 'simp2l', 'D e. NN')
    ddn = st([], 'simp2r', 'D || N')
    enn = st([], 'simp3l', 'E e. NN')
    edn = st([], 'simp3r', 'E || N')
    nz = st([nnn], 'nnzd', 'N e. ZZ')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    ez = st([enn], 'nnzd', 'E e. ZZ')
    ncn = st([nnn], 'nncnd', 'N e. CC')
    dcn = st([dnn], 'nncnd', 'D e. CC')
    ecn = st([enn], 'nncnd', 'E e. CC')
    dne = st([dnn], 'nnne0d', 'D =/= 0')
    qnn = st([st([nnn, dnn, w.inst('nndivdvds')], 'syl2anc',
                 '( D || N <-> %s e. NN )' % Q), ddn], 'mpbid', '%s e. NN' % Q)
    qcn = st([qnn], 'nncnd', '%s e. CC' % Q)
    qz = st([qnn], 'nnzd', '%s e. ZZ' % Q)
    dq = st([ncn, dcn, dne], 'divcan2d', '( D x. %s ) = N' % Q)
    musq = st([st([dq], 'fveq2d', '( mmu ` ( D x. %s ) ) = ( mmu ` N )' % Q), nsq], 'eqnetrd',
              '( mmu ` ( D x. %s ) ) =/= 0' % Q)
    cop = st([st([dnn, qnn, musq], '3jca',
                 '( D e. NN /\ %s e. NN /\ ( mmu ` ( D x. %s ) ) =/= 0 )' % (Q, Q)),
              w.inst('sqfcop')], 'syl', '( D gcd %s ) = 1' % Q)
    # forward
    AF = '( %s /\ N = %s )' % (A, LC)
    sf = mkst(w, AF)
    heq = sf([], 'simpr', 'N = %s' % LC)
    gnn = sf([sf([dnn], 'adantr', 'D e. NN'), sf([enn], 'adantr', 'E e. NN'),
              w.inst('gcdnncl')], 'syl2anc', '( D gcd E ) e. NN')
    gcn = sf([gnn], 'nncnd', '( D gcd E ) e. CC')
    lg = sf([sf([sf([dnn], 'adantr', 'D e. NN'), sf([enn], 'adantr', 'E e. NN')], 'jca',
                '( D e. NN /\ E e. NN )'), w.inst('lcmgcdnn')], 'syl',
            '( %s x. ( D gcd E ) ) = ( D x. E )' % LC)
    lg2 = sf([sf([heq], 'oveq1d', '( N x. ( D gcd E ) ) = ( %s x. ( D gcd E ) )' % LC), lg],
             'eqtrd', '( N x. ( D gcd E ) ) = ( D x. E )')
    lg3 = sf([sf([sf([dq], 'adantr', '( D x. %s ) = N' % Q)], 'oveq1d',
                 '( ( D x. %s ) x. ( D gcd E ) ) = ( N x. ( D gcd E ) )' % Q), lg2], 'eqtrd',
             '( ( D x. %s ) x. ( D gcd E ) ) = ( D x. E )' % Q)
    lg4 = sf([sf([sf([dcn], 'adantr', 'D e. CC'), sf([qcn], 'adantr', '%s e. CC' % Q), gcn],
                 'mulassd',
                 '( ( D x. %s ) x. ( D gcd E ) ) = ( D x. ( %s x. ( D gcd E ) ) )' % (Q, Q)),
              lg3], 'eqtr3d', '( D x. ( %s x. ( D gcd E ) ) ) = ( D x. E )' % Q)
    can = sf([sf([sf([qcn], 'adantr', '%s e. CC' % Q), gcn], 'mulcld',
                 '( %s x. ( D gcd E ) ) e. CC' % Q),
              sf([ecn], 'adantr', 'E e. CC'), sf([dcn], 'adantr', 'D e. CC'),
              sf([dne], 'adantr', 'D =/= 0'), lg4], 'mulcanad',
             '( %s x. ( D gcd E ) ) = E' % Q)
    qdv = sf([sf([sf([qz], 'adantr', '%s e. ZZ' % Q), sf([gnn], 'nnzd', '( D gcd E ) e. ZZ')],
                 'jca', '( %s e. ZZ /\ ( D gcd E ) e. ZZ )' % Q), w.inst('dvdsmul1')], 'syl',
             '%s || ( %s x. ( D gcd E ) )' % (Q, Q))
    fwd = sf([qdv, can], 'breqtrd', '%s || E' % Q)
    # backward
    AB = '( %s /\ %s || E )' % (A, Q)
    sb = mkst(w, AB)
    hdv = sb([], 'simpr', '%s || E' % Q)
    lnn0 = sb([sb([sb([dz], 'adantr', 'D e. ZZ'), sb([ez], 'adantr', 'E e. ZZ')], 'jca',
                  '( D e. ZZ /\ E e. ZZ )'), w.inst('lcmcl')], 'syl', '%s e. NN0' % LC)
    lz = sb([lnn0], 'nn0zd', '%s e. ZZ' % LC)
    ldn = sb([sb([sb([nz], 'adantr', 'N e. ZZ'), sb([dz], 'adantr', 'D e. ZZ'),
                  sb([ez], 'adantr', 'E e. ZZ')], '3jca', '( N e. ZZ /\ D e. ZZ /\ E e. ZZ )'),
              w.inst('lcmdvds')], 'syl',
             '( ( D || N /\ E || N ) -> %s || N )' % LC)
    ldn2 = sb([ldn, sb([sb([ddn], 'adantr', 'D || N'), sb([edn], 'adantr', 'E || N')], 'jca',
                       '( D || N /\ E || N )')], 'mpd', '%s || N' % LC)
    dl = sb([sb([sb([dz], 'adantr', 'D e. ZZ'), sb([ez], 'adantr', 'E e. ZZ')], 'jca',
                '( D e. ZZ /\ E e. ZZ )'), w.inst('dvdslcm')], 'syl',
            '( D || %s /\ E || %s )' % (LC, LC))
    dl1 = sb([dl], 'simpld', 'D || %s' % LC)
    dl2 = sb([dl], 'simprd', 'E || %s' % LC)
    ql = sb([sb([sb([sb([qz], 'adantr', '%s e. ZZ' % Q), sb([ez], 'adantr', 'E e. ZZ'), lz],
                    '3jca', '( %s e. ZZ /\ E e. ZZ /\ %s e. ZZ )' % (Q, LC)),
                 w.inst('dvdstr')], 'syl',
                '( ( %s || E /\ E || %s ) -> %s || %s )' % (Q, LC, Q, LC)),
             sb([hdv, dl2], 'jca', '( %s || E /\ E || %s )' % (Q, LC))], 'mpd',
            '%s || %s' % (Q, LC))
    cd2 = sb([sb([sb([sb([dz], 'adantr', 'D e. ZZ'), sb([qz], 'adantr', '%s e. ZZ' % Q), lz],
                     '3jca', '( D e. ZZ /\ %s e. ZZ /\ %s e. ZZ )' % (Q, LC)),
                  sb([cop], 'adantr', '( D gcd %s ) = 1' % Q)], 'jca',
                 '( ( D e. ZZ /\ %s e. ZZ /\ %s e. ZZ ) /\ ( D gcd %s ) = 1 )' % (Q, LC, Q)),
              w.inst('coprmdvds2')], 'syl',
             '( ( D || %s /\ %s || %s ) -> ( D x. %s ) || %s )' % (LC, Q, LC, Q, LC))
    cd3 = sb([cd2, sb([dl1, ql], 'jca', '( D || %s /\ %s || %s )' % (LC, Q, LC))], 'mpd',
             '( D x. %s ) || %s' % (Q, LC))
    ndl = sb([sb([sb([dq], 'adantr', '( D x. %s ) = N' % Q)], 'eqcomd',
                 'N = ( D x. %s )' % Q), cd3], 'eqbrtrd', 'N || %s' % LC)
    bwd = sb([sb([sb([sb([nnn], 'adantr', 'N e. NN')], 'nnnn0d', 'N e. NN0'), lnn0], 'jca',
                 '( N e. NN0 /\ %s e. NN0 )' % LC),
              sb([ndl, ldn2], 'jca', '( N || %s /\ %s || N )' % (LC, LC)),
              w.inst('dvdseq')], 'syl2anc', 'N = %s' % LC)
    w.qed([st([fwd], 'ex', '( N = %s -> %s || E )' % (LC, Q)),
           st([bwd], 'ex', '( %s || E -> N = %s )' % (Q, LC))], 'impbid',
          '( %s -> ( N = %s <-> %s || E ) )' % (A, LC, Q))
    return w


def lcmfib():
    w = W('lcmfib', 'The number of divisors of a squarefree N that are multiples of N / D is the '
                    'number of divisors of D.')
    A = '( ( N e. NN /\ ( mmu ` N ) =/= 0 ) /\ ( D e. NN /\ D || N ) )'
    Q = '( N / D )'
    DVD = DV('D')
    DVQ = DV(Q)
    DVZ = DV('( D x. %s )' % Q)
    DVN = DV('N')
    IFK = 'if ( k = %s , 1 , 0 )' % Q
    IFE = 'if ( %s || e , 1 , 0 )' % Q
    IFJK = 'if ( %s || ( j x. k ) , 1 , 0 )' % Q
    st = mkst(w, A)
    nnn = st([], 'simpll', 'N e. NN')
    nsq = st([], 'simplr', '( mmu ` N ) =/= 0')
    dnn = st([], 'simprl', 'D e. NN')
    ddn = st([], 'simprr', 'D || N')
    ncn = st([nnn], 'nncnd', 'N e. CC')
    dcn = st([dnn], 'nncnd', 'D e. CC')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    dne = st([dnn], 'nnne0d', 'D =/= 0')
    qnn = st([st([nnn, dnn, w.inst('nndivdvds')], 'syl2anc',
                 '( D || N <-> %s e. NN )' % Q), ddn], 'mpbid', '%s e. NN' % Q)
    qz = st([qnn], 'nnzd', '%s e. ZZ' % Q)
    dq = st([ncn, dcn, dne], 'divcan2d', '( D x. %s ) = N' % Q)
    musq = st([st([dq], 'fveq2d', '( mmu ` ( D x. %s ) ) = ( mmu ` N )' % Q), nsq], 'eqnetrd',
              '( mmu ` ( D x. %s ) ) =/= 0' % Q)
    cop = st([st([dnn, qnn, musq], '3jca',
                 '( D e. NN /\ %s e. NN /\ ( mmu ` ( D x. %s ) ) =/= 0 )' % (Q, Q)),
              w.inst('sqfcop')], 'syl', '( D gcd %s ) = 1' % Q)
    copr = st([st([qz, dz, w.inst('gcdcom')], 'syl2anc',
                  '( %s gcd D ) = ( D gcd %s )' % (Q, Q)), cop], 'eqtrd',
              '( %s gcd D ) = 1' % Q)
    # the hypotheses of fsumdvdsmul
    hx = w.s([], 'eqid', '%s = %s' % (DVD, DVD))
    hy = w.s([], 'eqid', '%s = %s' % (DVQ, DVQ))
    hz = w.s([], 'eqid', '%s = %s' % (DVZ, DVZ))
    AJ = '( %s /\ j e. %s )' % (A, DVD)
    h4 = w.s([], '1cnd', '( %s -> 1 e. CC )' % AJ)
    AK = '( %s /\ k e. %s )' % (A, DVQ)
    sk = mkst(w, AK)
    h5 = sk([w.s([], '1cnd', '( %s -> 1 e. CC )' % AK),
             w.s([], '0cnd', '( %s -> 0 e. CC )' % AK)], 'ifcld', '%s e. CC' % IFK)
    # the key equivalence
    AJK = '( %s /\ ( j e. %s /\ k e. %s ) )' % (A, DVD, DVQ)
    sj = mkst(w, AJK)
    jm = sj([], 'simprl', 'j e. %s' % DVD)
    km = sj([], 'simprr', 'k e. %s' % DVQ)
    eljd = w.s([w.s([], 'breq1', '( x = j -> ( x || D <-> j || D ) )')], 'elrab',
               '( j e. %s <-> ( j e. NN /\ j || D ) )' % DVD)
    jc = sj([sj([eljd], 'a1i', '( j e. %s <-> ( j e. NN /\ j || D ) )' % DVD), jm], 'mpbid',
            '( j e. NN /\ j || D )')
    jnn = sj([jc], 'simpld', 'j e. NN')
    jdD = sj([jc], 'simprd', 'j || D')
    jz = sj([jnn], 'nnzd', 'j e. ZZ')
    elkq = w.s([w.s([], 'breq1', '( x = k -> ( x || %s <-> k || %s ) )' % (Q, Q))], 'elrab',
               '( k e. %s <-> ( k e. NN /\ k || %s ) )' % (DVQ, Q))
    kc = sj([sj([elkq], 'a1i', '( k e. %s <-> ( k e. NN /\ k || %s ) )' % (DVQ, Q)), km],
            'mpbid', '( k e. NN /\ k || %s )' % Q)
    knn = sj([kc], 'simpld', 'k e. NN')
    kdQ = sj([kc], 'simprd', 'k || %s' % Q)
    kz = sj([knn], 'nnzd', 'k e. ZZ')
    qzj = sj([qz], 'adantr', '%s e. ZZ' % Q)
    dzj = sj([dz], 'adantr', 'D e. ZZ')
    gqj = sj([sj([sj([qzj, jz, dzj], '3jca',
                     '( %s e. ZZ /\ j e. ZZ /\ D e. ZZ )' % Q),
                  sj([sj([copr], 'adantr', '( %s gcd D ) = 1' % Q), jdD], 'jca',
                     '( ( %s gcd D ) = 1 /\ j || D )' % Q)], 'jca',
                 '( ( %s e. ZZ /\ j e. ZZ /\ D e. ZZ ) /\ '
                 '( ( %s gcd D ) = 1 /\ j || D ) )' % (Q, Q)),
              w.inst('rpdvds')], 'syl', '( %s gcd j ) = 1' % Q)
    AJKD = '( %s /\ %s || ( j x. k ) )' % (AJK, Q)
    sd = mkst(w, AJKD)
    qdk = sd([sd([sd([sd([qzj], 'adantr', '%s e. ZZ' % Q), sd([jz], 'adantr', 'j e. ZZ'),
                      sd([kz], 'adantr', 'k e. ZZ')], '3jca',
                     '( %s e. ZZ /\ j e. ZZ /\ k e. ZZ )' % Q), w.inst('coprmdvds')], 'syl',
                 '( ( %s || ( j x. k ) /\ ( %s gcd j ) = 1 ) -> %s || k )' % (Q, Q, Q)),
              sd([sd([], 'simpr', '%s || ( j x. k )' % Q),
                  sd([gqj], 'adantr', '( %s gcd j ) = 1' % Q)], 'jca',
                 '( %s || ( j x. k ) /\ ( %s gcd j ) = 1 )' % (Q, Q))], 'mpd', '%s || k' % Q)
    keq = sd([sd([sd([sd([knn], 'adantr', 'k e. NN')], 'nnnn0d', 'k e. NN0'),
                  sd([sd([sj([qnn], 'adantr', '%s e. NN' % Q)], 'adantr',
                          '%s e. NN' % Q)], 'nnnn0d', '%s e. NN0' % Q)], 'jca',
                 '( k e. NN0 /\ %s e. NN0 )' % Q),
              sd([sd([kdQ], 'adantr', 'k || %s' % Q), qdk], 'jca',
                 '( k || %s /\ %s || k )' % (Q, Q)), w.inst('dvdseq')], 'syl2anc', 'k = %s' % Q)
    AJKE = '( %s /\ k = %s )' % (AJK, Q)
    se = mkst(w, AJKE)
    kdjk = se([se([se([jz], 'adantr', 'j e. ZZ'), se([kz], 'adantr', 'k e. ZZ')], 'jca',
                  '( j e. ZZ /\ k e. ZZ )'), w.inst('dvdsmul2')], 'syl', 'k || ( j x. k )')
    qdjk = se([se([se([], 'simpr', 'k = %s' % Q)], 'eqcomd', '%s = k' % Q), kdjk], 'eqbrtrd',
              '%s || ( j x. k )' % Q)
    bi = sj([sj([keq], 'ex', '( %s || ( j x. k ) -> k = %s )' % (Q, Q)),
             sj([qdjk], 'ex', '( k = %s -> %s || ( j x. k ) )' % (Q, Q))], 'impbid',
            '( %s || ( j x. k ) <-> k = %s )' % (Q, Q))
    ifcc = sj([w.s([], '1cnd', '( %s -> 1 e. CC )' % AJK),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % AJK)], 'ifcld', '%s e. CC' % IFK)
    h6 = sj([sj([ifcc], 'mullidd', '( 1 x. %s ) = %s' % (IFK, IFK)),
             sj([sj([bi], 'bicomd', '( k = %s <-> %s || ( j x. k ) )' % (Q, Q))], 'ifbid',
                '%s = %s' % (IFK, IFJK))], 'eqtrd', '( 1 x. %s ) = %s' % (IFK, IFJK))
    h7 = w.s([w.s([], 'breq2', '( e = ( j x. k ) -> ( %s || e <-> %s || ( j x. k ) ) )' % (Q, Q))],
             'ifbid', '( e = ( j x. k ) -> %s = %s )' % (IFE, IFJK))
    mul = st([dnn, qnn, cop, hx, hy, hz, h4, h5, h6, h7], 'fsumdvdsmul',
             '( sum_ j e. %s 1 x. sum_ k e. %s %s ) = sum_ e e. %s %s'
             % (DVD, DVQ, IFK, DVZ, IFE))
    # the left factor
    finD = st([dnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVD)
    hashcn = st([st([finD, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % DVD)], 'nn0cnd',
                '( # ` %s ) e. CC' % DVD)
    sumj = st([st([st([finD, st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'jca',
                      '( %s e. Fin /\ 1 e. CC )' % DVD), w.inst('fsumconst')], 'syl',
                  'sum_ j e. %s 1 = ( ( # ` %s ) x. 1 )' % (DVD, DVD)),
               st([hashcn], 'mulridd', '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (DVD, DVD))],
              'eqtrd', 'sum_ j e. %s 1 = ( # ` %s )' % (DVD, DVD))
    # the right factor
    qdvq = st([w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (Q, Q, Q, Q))],
                   'elrab', '( %s e. %s <-> ( %s e. NN /\ %s || %s ) )' % (Q, DVQ, Q, Q, Q)),
               st([qnn, st([qz, w.inst('iddvds')], 'syl', '%s || %s' % (Q, Q))], 'jca',
                  '( %s e. NN /\ %s || %s )' % (Q, Q, Q))], 'sylibr', '%s e. %s' % (Q, DVQ))
    snq = st([qdvq], 'snssd', '{ %s } C_ %s' % (Q, DVQ))
    finQ = st([qnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVQ)
    ASN = '( %s /\ k e. { %s } )' % (A, Q)
    ssn = mkst(w, ASN)
    cc1 = ssn([w.s([], '1cnd', '( %s -> 1 e. CC )' % ASN),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % ASN)], 'ifcld', '%s e. CC' % IFK)
    ADF = '( %s /\ k e. ( %s \ { %s } ) )' % (A, DVQ, Q)
    sdf = mkst(w, ADF)
    kne = sdf([sdf([], 'simpr', 'k e. ( %s \ { %s } )' % (DVQ, Q)), w.inst('eldifsni')], 'syl',
              'k =/= %s' % Q)
    knq = sdf([kne], 'neneqd', '-. k = %s' % Q)
    zero = sdf([knq], 'iffalsed', '%s = 0' % IFK)
    sss = st([snq, cc1, zero, finQ], 'fsumss',
             'sum_ k e. { %s } %s = sum_ k e. %s %s' % (Q, IFK, DVQ, IFK))
    hsn = w.s([w.s([], 'id', '( k = %s -> k = %s )' % (Q, Q))], 'iftrued',
              '( k = %s -> %s = 1 )' % (Q, IFK))
    instsn = w.s([hsn], 'sumsn',
                 '( ( %s e. _V /\ 1 e. CC ) -> sum_ k e. { %s } %s = 1 )' % (Q, Q, IFK))
    snval = st([st([qnn], 'elexd', '%s e. _V' % Q),
                st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), instsn], 'syl2anc',
               'sum_ k e. { %s } %s = 1' % (Q, IFK))
    sumk = st([st([sss], 'eqcomd', 'sum_ k e. %s %s = sum_ k e. { %s } %s' % (DVQ, IFK, Q, IFK)),
               snval], 'eqtrd', 'sum_ k e. %s %s = 1' % (DVQ, IFK))
    lhs = st([st([sumj, sumk], 'oveq12d',
                 '( sum_ j e. %s 1 x. sum_ k e. %s %s ) = ( ( # ` %s ) x. 1 )'
                 % (DVD, DVQ, IFK, DVD)),
              st([hashcn], 'mulridd', '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (DVD, DVD))],
             'eqtrd', '( sum_ j e. %s 1 x. sum_ k e. %s %s ) = ( # ` %s )' % (DVD, DVQ, IFK, DVD))
    zrab = st([st([dq], 'breq2d', '( x || ( D x. %s ) <-> x || N )' % Q)], 'rabbidv',
              '%s = %s' % (DVZ, DVN))
    zsum = st([zrab], 'sumeq1d', 'sum_ e e. %s %s = sum_ e e. %s %s' % (DVZ, IFE, DVN, IFE))
    w.qed([st([st([zsum], 'eqcomd',
                  'sum_ e e. %s %s = sum_ e e. %s %s' % (DVN, IFE, DVZ, IFE)),
               st([mul], 'eqcomd',
                  'sum_ e e. %s %s = ( sum_ j e. %s 1 x. sum_ k e. %s %s )'
                  % (DVZ, IFE, DVD, DVQ, IFK))], 'eqtrd',
              'sum_ e e. %s %s = ( sum_ j e. %s 1 x. sum_ k e. %s %s )'
              % (DVN, IFE, DVD, DVQ, IFK)), lhs], 'eqtrd',
          '( %s -> sum_ e e. %s %s = ( # ` %s ) )' % (A, DVN, IFE, DVD))
    return w


def lcmcnt():
    w = W('lcmcnt', 'The number of pairs of divisors of a squarefree number with least common '
                    'multiple the number itself is three to the number of prime divisors.')
    A = '( N e. NN /\ ( mmu ` N ) =/= 0 )'
    DVN = DV('N')
    IFL = 'if ( N = ( d lcm e ) , 1 , 0 )'
    IFQ = 'if ( ( N / d ) || e , 1 , 0 )'
    st = mkst(w, A)
    nnn = st([], 'simpl', 'N e. NN')
    nsq = st([], 'simpr', '( mmu ` N ) =/= 0')
    nz = st([nnn], 'nnzd', 'N e. ZZ')
    BD = '( %s /\ d e. %s )' % (A, DVN)
    sd = mkst(w, BD)
    eldn = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\ d || N ) )' % DVN)
    dc = sd([sd([eldn], 'a1i', '( d e. %s <-> ( d e. NN /\ d || N ) )' % DVN),
             sd([], 'simpr', 'd e. %s' % DVN)], 'mpbid', '( d e. NN /\ d || N )')
    dnn = sd([dc], 'simpld', 'd e. NN')
    ddn = sd([dc], 'simprd', 'd || N')
    dsq = sd([sd([sd([sd([nnn], 'adantr', 'N e. NN'), dnn, ddn], '3jca',
                     '( N e. NN /\ d e. NN /\ d || N )'), w.inst('dvdssqf')], 'syl',
                 '( ( mmu ` N ) =/= 0 -> ( mmu ` d ) =/= 0 )'),
               sd([nsq], 'adantr', '( mmu ` N ) =/= 0')], 'mpd', '( mmu ` d ) =/= 0')
    # the inner summand
    BE = '( %s /\ e e. %s )' % (BD, DVN)
    se = mkst(w, BE)
    elen = w.s([w.s([], 'breq1', '( x = e -> ( x || N <-> e || N ) )')], 'elrab',
               '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN)
    ec = se([se([elen], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
             se([], 'simpr', 'e e. %s' % DVN)], 'mpbid', '( e e. NN /\ e || N )')
    equiv = se([se([se([sd([nnn], 'adantr', 'N e. NN')], 'adantr', 'N e. NN'),
                    se([sd([nsq], 'adantr', '( mmu ` N ) =/= 0')], 'adantr',
                       '( mmu ` N ) =/= 0')], 'jca', A),
                se([se([dnn], 'adantr', 'd e. NN'), se([ddn], 'adantr', 'd || N')], 'jca',
                   '( d e. NN /\ d || N )'), ec, w.inst('lcmequiv')], 'syl3anc',
               '( N = ( d lcm e ) <-> ( N / d ) || e )')
    ifeq = se([equiv], 'ifbid', '%s = %s' % (IFL, IFQ))
    inner = sd([ifeq], 'sumeq2dv',
               'sum_ e e. %s %s = sum_ e e. %s %s' % (DVN, IFL, DVN, IFQ))
    fib = sd([sd([sd([nnn], 'adantr', 'N e. NN'), sd([nsq], 'adantr', '( mmu ` N ) =/= 0')],
                 'jca', A), sd([dnn, ddn], 'jca', '( d e. NN /\ d || N )'), w.inst('lcmfib')],
             'syl2anc', 'sum_ e e. %s %s = ( # ` %s )' % (DVN, IFQ, DV('d')))
    hsh = sd([sd([dnn, dsq], 'jca', '( d e. NN /\ ( mmu ` d ) =/= 0 )'), w.inst('hashdv')],
             'syl', '( # ` %s ) = ( 2 ^ %s )' % (DV('d'), OM('d', 'r')))
    cbvd = sd([sd([sd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'q'), PF('d', 'r')))], 'a1i',
                      '%s = %s' % (PF('d', 'q'), PF('d', 'r')))], 'fveq2d',
                  '%s = %s' % (OM('d', 'q'), OM('d', 'r')))], 'oveq2d',
               '( 2 ^ %s ) = ( 2 ^ %s )' % (OM('d', 'q'), OM('d', 'r')))
    term = sd([sd([inner, fib], 'eqtrd',
                  'sum_ e e. %s %s = ( # ` %s )' % (DVN, IFL, DV('d'))),
               sd([hsh, sd([cbvd], 'eqcomd',
                           '( 2 ^ %s ) = ( 2 ^ %s )' % (OM('d', 'r'), OM('d', 'q')))], 'eqtrd',
                  '( # ` %s ) = ( 2 ^ %s )' % (DV('d'), OM('d', 'q')))], 'eqtrd',
              'sum_ e e. %s %s = ( 2 ^ %s )' % (DVN, IFL, OM('d', 'q')))
    outer = st([term], 'sumeq2dv',
               'sum_ d e. %s sum_ e e. %s %s = sum_ d e. %s ( 2 ^ %s )'
               % (DVN, DVN, IFL, DVN, OM('d', 'q')))
    key = st([st([nnn, nsq], 'jca', A), st([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC'),
              w.inst('dmkey')], 'syl2anc',
             'sum_ d e. %s ( 2 ^ %s ) = ( ( 2 + 1 ) ^ %s )'
             % (DVN, OM('d', 'q'), OM('N', 'q')))
    three = st([st([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'a1i', '( 2 + 1 ) = 3')], 'oveq1d',
               '( ( 2 + 1 ) ^ %s ) = ( 3 ^ %s )' % (OM('N', 'q'), OM('N', 'q')))
    cbvn = st([st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('N', 'q'), PF('N', 'r')))], 'a1i',
                      '%s = %s' % (PF('N', 'q'), PF('N', 'r')))], 'fveq2d',
                  '%s = %s' % (OM('N', 'q'), OM('N', 'r')))], 'oveq2d',
               '( 3 ^ %s ) = ( 3 ^ %s )' % (OM('N', 'q'), OM('N', 'r')))
    w.qed([outer, st([st([key, three], 'eqtrd',
                         'sum_ d e. %s ( 2 ^ %s ) = ( 3 ^ %s )'
                         % (DVN, OM('d', 'q'), OM('N', 'q'))), cbvn], 'eqtrd',
                     'sum_ d e. %s ( 2 ^ %s ) = ( 3 ^ %s )'
                     % (DVN, OM('d', 'q'), OM('N', 'r')))], 'eqtrd',
          '( %s -> sum_ d e. %s sum_ e e. %s %s = ( 3 ^ %s ) )'
          % (A, DVN, DVN, IFL, OM('N', 'r')))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['hashdv']:
        globals()[f]().run()
