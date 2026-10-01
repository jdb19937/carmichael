"""Sortie v2b: the fundamental sieve inequality.

wge0c     instantiation of the weight nonnegativity hypothesis
umc       instantiation of the upper Moebius hypothesis
siftgcd   the divisor sum over ( P gcd C ) as a restricted sum over the divisors of P
siftcom   the support / divisor double sum swap
siftub    the sifted sum is at most the main term plus the error term
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *

WGE0 = 'A. k e. NN 0 <_ ( W ` k )'
UMS = 'sum_ e e. { x e. NN | x || y } ( U ` e )'
UM = 'A. y e. NN if ( y = 1 , 1 , 0 ) <_ %s' % UMS


def wge0c():
    w = W('wge0c', 'Instantiation of the weight nonnegativity hypothesis at a positive integer.')
    A = '( %s /\\ C e. NN )' % WGE0
    st = mkst(w, A)
    e1 = w.s([w.s([], 'fveq2', '( k = C -> ( W ` k ) = ( W ` C ) )')], 'breq2d',
             '( k = C -> ( 0 <_ ( W ` k ) <-> 0 <_ ( W ` C ) ) )')
    w.qed([e1, st([], 'simpl', WGE0), st([], 'simpr', 'C e. NN')], 'rspcdva',
          '( %s -> 0 <_ ( W ` C ) )' % A)
    return w


def umc():
    w = W('umc', 'Instantiation of the upper Moebius hypothesis at a positive integer.')
    A = '( %s /\\ C e. NN )' % UM
    SC = 'sum_ e e. %s ( U ` e )' % DV('C')
    st = mkst(w, A)
    e1 = w.s([w.s([], 'eqeq1', '( y = C -> ( y = 1 <-> C = 1 ) )')], 'ifbid',
             '( y = C -> if ( y = 1 , 1 , 0 ) = if ( C = 1 , 1 , 0 ) )')
    e2 = w.s([w.s([w.s([], 'breq2', '( y = C -> ( x || y <-> x || C ) )')], 'rabbidv',
                  '( y = C -> %s = %s )' % (DV('y'), DV('C')))], 'sumeq1d',
             '( y = C -> %s = %s )' % (UMS, SC))
    e3 = w.s([e1, e2], 'breq12d',
             '( y = C -> ( if ( y = 1 , 1 , 0 ) <_ %s <-> if ( C = 1 , 1 , 0 ) <_ %s ) )'
             % (UMS, SC))
    w.qed([e3, st([], 'simpl', UM), st([], 'simpr', 'C e. NN')], 'rspcdva',
          '( %s -> if ( C = 1 , 1 , 0 ) <_ %s )' % (A, SC))
    return w


def siftgcd():
    w = W('siftgcd', 'The sum over the divisors of the greatest common divisor of P and C is the '
                     'sum over the divisors of P that divide C.')
    A = '( ( P e. NN /\\ U : NN --> RR ) /\\ C e. NN )'
    G = '( P gcd C )'
    DVG = DV(G)
    DVP = DV('P')
    IFD = 'if ( d || C , ( U ` d ) , 0 )'
    st = mkst(w, A)
    pnn = st([], 'simpll', 'P e. NN')
    uf = st([], 'simplr', 'U : NN --> RR')
    cnn = st([], 'simpr', 'C e. NN')
    pz = st([pnn], 'nnzd', 'P e. ZZ')
    cz = st([cnn], 'nnzd', 'C e. ZZ')
    gnn = st([pnn, cnn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G)
    gz = st([gnn], 'nnzd', '%s e. ZZ' % G)
    gd = st([pz, cz, w.inst('gcddvds')], 'syl2anc', '( %s || P /\\ %s || C )' % (G, G))
    gdP = st([gd], 'simpld', '%s || P' % G)
    gdC = st([gd], 'simprd', '%s || C' % G)
    finP = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    finG = st([gnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVG)
    # DV ( G ) C_ DV ( P )
    AX = '( %s /\\ x e. NN )' % A
    sx = mkst(w, AX)
    AXG = '( %s /\\ x || %s )' % (AX, G)
    sxg = mkst(w, AXG)
    tr = sxg([sxg([sxg([w.s([], 'simplr', '( %s -> x e. NN )' % AXG)], 'nnzd', 'x e. ZZ'),
                   sxg([sx([gz], 'adantr', '%s e. ZZ' % G)], 'adantr', '%s e. ZZ' % G),
                   sxg([sx([pz], 'adantr', 'P e. ZZ')], 'adantr', 'P e. ZZ')], '3jca',
                  '( x e. ZZ /\\ %s e. ZZ /\\ P e. ZZ )' % G), w.inst('dvdstr')], 'syl',
             '( ( x || %s /\\ %s || P ) -> x || P )' % (G, G))
    xdP = sxg([tr, sxg([sxg([], 'simpr', 'x || %s' % G),
                        sxg([sx([gdP], 'adantr', '%s || P' % G)], 'adantr', '%s || P' % G)], 'jca',
                       '( x || %s /\\ %s || P )' % (G, G))], 'mpd', 'x || P')
    sub = st([sx([xdP], 'ex', '( x || %s -> x || P )' % G)], 'ss2rabdv', '%s C_ %s' % (DVG, DVP))
    # rename the summation variable
    cbv = st([w.s([], 'cbvsumv',
                  'sum_ e e. %s ( U ` e ) = sum_ d e. %s ( U ` d )' % (DVG, DVG))], 'a1i',
             'sum_ e e. %s ( U ` e ) = sum_ d e. %s ( U ` d )' % (DVG, DVG))

    def eld(S, X):
        return w.s([w.s([], 'breq1', '( x = d -> ( x || %s <-> d || %s ) )' % (X, X))], 'elrab',
                   '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (S, X))

    eldG = eld(DVG, G)
    eldP = eld(DVP, 'P')
    # on DV ( G ) the condition holds
    AG = '( %s /\\ d e. %s )' % (A, DVG)
    sg = mkst(w, AG)
    dcG = sg([sg([eldG], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DVG, G)),
              sg([], 'simpr', 'd e. %s' % DVG)], 'mpbid', '( d e. NN /\\ d || %s )' % G)
    dnnG = sg([dcG], 'simpld', 'd e. NN')
    ddG = sg([dcG], 'simprd', 'd || %s' % G)
    ddC = sg([sg([sg([sg([dnnG], 'nnzd', 'd e. ZZ'), sg([gz], 'adantr', '%s e. ZZ' % G),
                      sg([cz], 'adantr', 'C e. ZZ')], '3jca',
                     '( d e. ZZ /\\ %s e. ZZ /\\ C e. ZZ )' % G), w.inst('dvdstr')], 'syl',
                 '( ( d || %s /\\ %s || C ) -> d || C )' % (G, G)),
              sg([ddG, sg([gdC], 'adantr', '%s || C' % G)], 'jca',
                 '( d || %s /\\ %s || C )' % (G, G))], 'mpd', 'd || C')
    tru = sg([ddC], 'iftrued', '%s = ( U ` d )' % IFD)
    eqG = sg([tru], 'eqcomd', '( U ` d ) = %s' % IFD)
    sumG = st([eqG], 'sumeq2dv',
              'sum_ d e. %s ( U ` d ) = sum_ d e. %s %s' % (DVG, DVG, IFD))
    # closure on DV ( G )
    udrG = sg([sg([uf], 'adantr', 'U : NN --> RR'), dnnG, w.inst('ffvelcdm')], 'syl2anc',
              '( U ` d ) e. RR')
    ccG = sg([sg([udrG], 'recnd', '( U ` d ) e. CC'),
              w.s([], '0cnd', '( %s -> 0 e. CC )' % AG)], 'ifcld', '%s e. CC' % IFD)
    # off DV ( G ) the condition fails
    ADF = '( %s /\\ d e. ( %s \\ %s ) )' % (A, DVP, DVG)
    sdf = mkst(w, ADF)
    ddif = w.s([], 'simpr', '( %s -> d e. ( %s \\ %s ) )' % (ADF, DVP, DVG))
    dinP = sdf([ddif, w.inst('eldifi')], 'syl', 'd e. %s' % DVP)
    dnotG = sdf([ddif, w.inst('eldifn')], 'syl', '-. d e. %s' % DVG)
    dcP = sdf([sdf([eldP], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || P ) )' % DVP), dinP], 'mpbid',
              '( d e. NN /\\ d || P )')
    dnnP = sdf([dcP], 'simpld', 'd e. NN')
    ddP = sdf([dcP], 'simprd', 'd || P')
    ADC = '( %s /\\ d || C )' % ADF
    sdc = mkst(w, ADC)
    dgcd = sdc([sdc([sdc([sdc([sdc([dnnP], 'adantr', 'd e. NN')], 'nnzd', 'd e. ZZ'),
                          sdc([sdf([pz], 'adantr', 'P e. ZZ')], 'adantr', 'P e. ZZ'),
                          sdc([sdf([cz], 'adantr', 'C e. ZZ')], 'adantr', 'C e. ZZ')], '3jca',
                         '( d e. ZZ /\\ P e. ZZ /\\ C e. ZZ )'), w.inst('dvdsgcdb')], 'syl',
                    '( ( d || P /\\ d || C ) <-> d || %s )' % G),
                sdc([sdc([ddP], 'adantr', 'd || P'), sdc([], 'simpr', 'd || C')], 'jca',
                    '( d || P /\\ d || C )')], 'mpbid', 'd || %s' % G)
    inG = sdc([sdc([eldG], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || %s ) )' % (DVG, G)),
               sdc([sdc([dnnP], 'adantr', 'd e. NN'), dgcd], 'jca',
                   '( d e. NN /\\ d || %s )' % G)], 'mpbird', 'd e. %s' % DVG)
    ndC = sdf([dnotG, inG], 'mtand', '-. d || C')
    zero = sdf([ndC], 'iffalsed', '%s = 0' % IFD)
    ext = st([sub, ccG, zero, finP], 'fsumss',
             'sum_ d e. %s %s = sum_ d e. %s %s' % (DVG, IFD, DVP, IFD))
    w.qed([st([cbv, sumG], 'eqtrd',
              'sum_ e e. %s ( U ` e ) = sum_ d e. %s %s' % (DVG, DVG, IFD)), ext], 'eqtrd',
          '( %s -> sum_ e e. %s ( U ` e ) = sum_ d e. %s %s )' % (A, DVG, DVP, IFD))
    return w


def siftcom():
    w = W('siftcom', 'Swapping the support sum and the divisor sum of the sifting product.')
    A = ('( ( A e. Fin /\ A C_ NN /\ W : NN --> RR ) /\ ( P e. NN /\ U : NN --> RR ) )')
    DVP = DV('P')
    IFU = 'if ( d || n , ( U ` d ) , 0 )'
    IFW = 'if ( d || n , ( W ` n ) , 0 )'
    st = mkst(w, A)
    finA = st([], 'simpl1', 'A e. Fin')
    assnn = st([], 'simpl2', 'A C_ NN')
    wf = st([], 'simpl3', 'W : NN --> RR')
    pnn = st([], 'simprl', 'P e. NN')
    uf = st([], 'simprr', 'U : NN --> RR')
    finP = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    eldP = w.s([w.s([], 'breq1', '( x = d -> ( x || P <-> d || P ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP)

    def clos(ante, nstep, dstep, lift):
        """closures of ( W ` n ) , ( U ` d ) , IFU , IFW under `ante`"""
        sb = mkst(w, ante)
        nnn = sb([lift(assnn, 'A C_ NN'), nstep], 'sseldd', 'n e. NN')
        wnr = sb([lift(wf, 'W : NN --> RR'), nnn, w.inst('ffvelcdm')], 'syl2anc',
                 '( W ` n ) e. RR')
        wnc = sb([wnr], 'recnd', '( W ` n ) e. CC')
        dnn = sb([sb([sb([eldP], 'a1i', '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP), dstep],
                     'mpbid', '( d e. NN /\ d || P )')], 'simpld', 'd e. NN')
        udr = sb([lift(uf, 'U : NN --> RR'), dnn, w.inst('ffvelcdm')], 'syl2anc',
                 '( U ` d ) e. RR')
        udc = sb([udr], 'recnd', '( U ` d ) e. CC')
        zc = w.s([], '0cnd', '( %s -> 0 e. CC )' % ante)
        ifu = sb([udc, zc], 'ifcld', '%s e. CC' % IFU)
        ifw = sb([wnc, zc], 'ifcld', '%s e. CC' % IFW)
        return sb, wnc, udc, ifu, ifw, dnn, nnn

    # ---- shape ( ( A /\ n e. A ) /\ d e. DV ( P ) )
    AN = '( %s /\ n e. A )' % A
    sn = mkst(w, AN)
    AND1 = '( %s /\ d e. %s )' % (AN, DVP)
    s1, wnc1, udc1, ifu1, ifw1, _, _ = clos(
        AND1, w.s([], 'simplr', '( %s -> n e. A )' % AND1),
        w.s([], 'simpr', '( %s -> d e. %s )' % (AND1, DVP)),
        lambda step, f: w.s([step], 'ad2antrr', '( %s -> %s )' % (AND1, f)))
    wnc1n = sn([sn([assnn], 'adantr', 'A C_ NN'), sn([], 'simpr', 'n e. A')], 'sseldd', 'n e. NN')
    wncn = sn([sn([sn([wf], 'adantr', 'W : NN --> RR'), wnc1n, w.inst('ffvelcdm')], 'syl2anc',
                  '( W ` n ) e. RR')], 'recnd', '( W ` n ) e. CC')
    step1 = st([sn([sn([finP], 'adantr', '%s e. Fin' % DVP), wncn, ifu1], 'fsummulc2',
                   '( ( W ` n ) x. sum_ d e. %s %s ) = sum_ d e. %s ( ( W ` n ) x. %s )'
                   % (DVP, IFU, DVP, IFU))], 'sumeq2dv',
               'sum_ n e. A ( ( W ` n ) x. sum_ d e. %s %s ) = '
               'sum_ n e. A sum_ d e. %s ( ( W ` n ) x. %s )' % (DVP, IFU, DVP, IFU))
    # ---- shape ( A /\ ( n e. A /\ d e. DV ( P ) ) )
    APR = '( %s /\ ( n e. A /\ d e. %s ) )' % (A, DVP)
    s2, wnc2, udc2, ifu2, ifw2, _, _ = clos(
        APR, w.s([w.s([], 'simpr', '( %s -> ( n e. A /\ d e. %s ) )' % (APR, DVP))], 'simpld',
                 '( %s -> n e. A )' % APR),
        w.s([w.s([], 'simpr', '( %s -> ( n e. A /\ d e. %s ) )' % (APR, DVP))], 'simprd',
            '( %s -> d e. %s )' % (APR, DVP)),
        lambda step, f: w.s([step], 'adantr', '( %s -> %s )' % (APR, f)))
    prodc2 = s2([wnc2, ifu2], 'mulcld', '( ( W ` n ) x. %s ) e. CC' % IFU)
    swap = st([finA, finP, prodc2], 'fsumcom',
              'sum_ n e. A sum_ d e. %s ( ( W ` n ) x. %s ) = '
              'sum_ d e. %s sum_ n e. A ( ( W ` n ) x. %s )' % (DVP, IFU, DVP, IFU))
    # ---- shape ( ( A /\ d e. DV ( P ) ) /\ n e. A )
    AD = '( %s /\ d e. %s )' % (A, DVP)
    sdd = mkst(w, AD)
    ADN = '( %s /\ n e. A )' % AD
    s3, wnc3, udc3, ifu3, ifw3, _, _ = clos(
        ADN, w.s([], 'simpr', '( %s -> n e. A )' % ADN),
        w.s([], 'simplr', '( %s -> d e. %s )' % (ADN, DVP)),
        lambda step, f: w.s([step], 'ad2antrr', '( %s -> %s )' % (ADN, f)))
    # the termwise identity
    ADNT = '( %s /\ d || n )' % ADN
    st4 = mkst(w, ADNT)
    t1 = st4([st4([], 'simpr', 'd || n')], 'iftrued', '%s = ( U ` d )' % IFU)
    t2 = st4([st4([], 'simpr', 'd || n')], 'iftrued', '%s = ( W ` n )' % IFW)
    lhs1 = st4([t1], 'oveq2d',
               '( ( W ` n ) x. %s ) = ( ( W ` n ) x. ( U ` d ) )' % IFU)
    rhs1 = st4([t2], 'oveq2d',
               '( ( U ` d ) x. %s ) = ( ( U ` d ) x. ( W ` n ) )' % IFW)
    comm = st4([st4([wnc3], 'adantr', '( W ` n ) e. CC'),
                st4([udc3], 'adantr', '( U ` d ) e. CC')], 'mulcomd',
               '( ( W ` n ) x. ( U ` d ) ) = ( ( U ` d ) x. ( W ` n ) )')
    case1 = st4([st4([lhs1, comm], 'eqtrd',
                     '( ( W ` n ) x. %s ) = ( ( U ` d ) x. ( W ` n ) )' % IFU), rhs1], 'eqtr4d',
                '( ( W ` n ) x. %s ) = ( ( U ` d ) x. %s )' % (IFU, IFW))
    ADNF = '( %s /\ -. d || n )' % ADN
    st5 = mkst(w, ADNF)
    f1 = st5([st5([], 'simpr', '-. d || n')], 'iffalsed', '%s = 0' % IFU)
    f2 = st5([st5([], 'simpr', '-. d || n')], 'iffalsed', '%s = 0' % IFW)
    lhs2 = st5([st5([f1], 'oveq2d',
                    '( ( W ` n ) x. %s ) = ( ( W ` n ) x. 0 )' % IFU),
                st5([st5([wnc3], 'adantr', '( W ` n ) e. CC')], 'mul01d',
                    '( ( W ` n ) x. 0 ) = 0')], 'eqtrd', '( ( W ` n ) x. %s ) = 0' % IFU)
    rhs2 = st5([st5([f2], 'oveq2d',
                    '( ( U ` d ) x. %s ) = ( ( U ` d ) x. 0 )' % IFW),
                st5([st5([udc3], 'adantr', '( U ` d ) e. CC')], 'mul01d',
                    '( ( U ` d ) x. 0 ) = 0')], 'eqtrd', '( ( U ` d ) x. %s ) = 0' % IFW)
    case2 = st5([lhs2, rhs2], 'eqtr4d',
                '( ( W ` n ) x. %s ) = ( ( U ` d ) x. %s )' % (IFU, IFW))
    term = s3([case1, case2], 'pm2.61dan',
              '( ( W ` n ) x. %s ) = ( ( U ` d ) x. %s )' % (IFU, IFW))
    inner = sdd([term], 'sumeq2dv',
                'sum_ n e. A ( ( W ` n ) x. %s ) = sum_ n e. A ( ( U ` d ) x. %s )' % (IFU, IFW))
    pull = sdd([sdd([finA], 'adantr', 'A e. Fin'), udc3 if False else
                sdd([sdd([sdd([uf], 'adantr', 'U : NN --> RR'),
                          sdd([sdd([sdd([eldP], 'a1i',
                                        '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP),
                                    sdd([], 'simpr', 'd e. %s' % DVP)], 'mpbid',
                                   '( d e. NN /\ d || P )')], 'simpld', 'd e. NN'),
                          w.inst('ffvelcdm')], 'syl2anc', '( U ` d ) e. RR')], 'recnd',
                    '( U ` d ) e. CC'), ifw3], 'fsummulc2',
               '( ( U ` d ) x. sum_ n e. A %s ) = sum_ n e. A ( ( U ` d ) x. %s )' % (IFW, IFW))
    outer = st([sdd([inner, sdd([pull], 'eqcomd',
                                'sum_ n e. A ( ( U ` d ) x. %s ) = '
                                '( ( U ` d ) x. sum_ n e. A %s )' % (IFW, IFW))], 'eqtrd',
                    'sum_ n e. A ( ( W ` n ) x. %s ) = ( ( U ` d ) x. sum_ n e. A %s )'
                    % (IFU, IFW))], 'sumeq2dv',
               'sum_ d e. %s sum_ n e. A ( ( W ` n ) x. %s ) = '
               'sum_ d e. %s ( ( U ` d ) x. sum_ n e. A %s )' % (DVP, IFU, DVP, IFW))
    w.qed([st([step1, swap], 'eqtrd',
              'sum_ n e. A ( ( W ` n ) x. sum_ d e. %s %s ) = '
              'sum_ d e. %s sum_ n e. A ( ( W ` n ) x. %s )' % (DVP, IFU, DVP, IFU)), outer],
          'eqtrd',
          '( %s -> sum_ n e. A ( ( W ` n ) x. sum_ d e. %s %s ) = '
          'sum_ d e. %s ( ( U ` d ) x. sum_ n e. A %s ) )' % (A, DVP, IFU, DVP, IFW))
    return w


def siftub():
    w = W('siftub', 'The sifted sum is at most the main term plus the error term of any upper '
                    'Moebius sequence.')
    A = '( %s /\ ( U : NN --> RR /\ %s ) )' % (SH, UM)
    DVP = DV('P')
    IFU = 'if ( d || n , ( U ` d ) , 0 )'
    IFW = 'if ( d || n , ( W ` n ) , 0 )'
    MSD = 'sum_ n e. A %s' % IFW
    RMD = '( %s - ( ( V ` d ) x. X ) )' % MSD
    SFS = 'sum_ n e. A if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )'
    SUV = 'sum_ d e. %s ( ( U ` d ) x. ( V ` d ) )' % DVP
    SABS = 'sum_ d e. %s ( ( abs ` ( U ` d ) ) x. ( abs ` %s ) )' % (DVP, RMD)
    T1 = 'sum_ n e. A ( ( W ` n ) x. sum_ d e. %s %s )' % (DVP, IFU)
    T2 = 'sum_ d e. %s ( ( U ` d ) x. %s )' % (DVP, MSD)
    TRM = '( ( X x. ( ( U ` d ) x. ( V ` d ) ) ) + ( ( U ` d ) x. %s ) )' % RMD
    T3 = 'sum_ d e. %s %s' % (DVP, TRM)
    T4A = 'sum_ d e. %s ( X x. ( ( U ` d ) x. ( V ` d ) ) )' % DVP
    T4B = 'sum_ d e. %s ( ( U ` d ) x. %s )' % (DVP, RMD)
    d = shsteps(w, A, (SH,))
    st = d['st']
    uf = st([], 'simprl', 'U : NN --> RR')
    um = st([], 'simprr', UM)
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    eldP = w.s([w.s([], 'breq1', '( x = d -> ( x || P <-> d || P ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP)
    # ---------- T0 <_ T1
    AN = '( %s /\ n e. A )' % A
    sn = mkst(w, AN)
    nnn = sn([sn([d['assnn']], 'adantr', 'A C_ NN'), sn([], 'simpr', 'n e. A')], 'sseldd',
             'n e. NN')
    wnr = sn([sn([d['wf']], 'adantr', 'W : NN --> RR'), nnn, w.inst('ffvelcdm')], 'syl2anc',
             '( W ` n ) e. RR')
    wnc = sn([wnr], 'recnd', '( W ` n ) e. CC')
    wn0 = sn([sn([d['wge0']], 'adantr', WGE0), nnn, w.inst('wge0c')], 'syl2anc',
             '0 <_ ( W ` n )')
    gnn = sn([sn([sn([d['pnn']], 'adantr', 'P e. NN'), nnn], 'jca',
                 '( P e. NN /\ n e. NN )'), w.inst('gcdnncl')], 'syl', '( P gcd n ) e. NN')
    ANT = '( %s /\ ( P gcd n ) = 1 )' % AN
    snt = mkst(w, ANT)
    ANF = '( %s /\ -. ( P gcd n ) = 1 )' % AN
    snf = mkst(w, ANF)
    fac1 = snt([snt([snt([wnc], 'adantr', '( W ` n ) e. CC')], 'mullidd',
                    '( 1 x. ( W ` n ) ) = ( W ` n )'),
                snt([snt([], 'simpr', '( P gcd n ) = 1')], 'iftrued',
                    'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 ) = ( W ` n )')], 'eqtr4d',
               '( 1 x. ( W ` n ) ) = if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )')
    mul1 = snt([snt([snt([], 'simpr', '( P gcd n ) = 1')], 'iftrued',
                    'if ( ( P gcd n ) = 1 , 1 , 0 ) = 1')], 'oveq2d',
               '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) ) = ( ( W ` n ) x. 1 )')
    case1 = snt([snt([mul1, snt([snt([wnc], 'adantr', '( W ` n ) e. CC')], 'mulridd',
                                '( ( W ` n ) x. 1 ) = ( W ` n )')], 'eqtrd',
                     '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) ) = ( W ` n )'),
                 snt([snt([], 'simpr', '( P gcd n ) = 1')], 'iftrued',
                     'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 ) = ( W ` n )')], 'eqtr4d',
                '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) ) = '
                'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )')
    case2 = snf([snf([snf([snf([], 'simpr', '-. ( P gcd n ) = 1')], 'iffalsed',
                          'if ( ( P gcd n ) = 1 , 1 , 0 ) = 0')], 'oveq2d',
                     '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) ) = ( ( W ` n ) x. 0 )'),
                 snf([snf([snf([wnc], 'adantr', '( W ` n ) e. CC')], 'mul01d',
                          '( ( W ` n ) x. 0 ) = 0'),
                      snf([snf([snf([], 'simpr', '-. ( P gcd n ) = 1')], 'iffalsed',
                               'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 ) = 0')], 'eqcomd',
                          '0 = if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )')], 'eqtrd',
                     '( ( W ` n ) x. 0 ) = if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )')], 'eqtrd',
                '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) ) = '
                'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )')
    facw = sn([case1, case2], 'pm2.61dan',
              '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) ) = '
              'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )')
    umle = sn([sn([um], 'adantr', UM), gnn, w.inst('umc')], 'syl2anc',
              'if ( ( P gcd n ) = 1 , 1 , 0 ) <_ sum_ e e. %s ( U ` e )' % DV('( P gcd n )'))
    gcdsum = sn([sn([sn([sn([d['pnn']], 'adantr', 'P e. NN'),
                         sn([uf], 'adantr', 'U : NN --> RR')], 'jca',
                        '( P e. NN /\ U : NN --> RR )'), nnn], 'jca',
                    '( ( P e. NN /\ U : NN --> RR ) /\ n e. NN )'), w.inst('siftgcd')], 'syl',
                'sum_ e e. %s ( U ` e ) = sum_ d e. %s %s'
                % (DV('( P gcd n )'), DVP, IFU))
    umle2 = sn([umle, gcdsum], 'breqtrd',
               'if ( ( P gcd n ) = 1 , 1 , 0 ) <_ sum_ d e. %s %s' % (DVP, IFU))
    # closures on DV ( P ) under AN
    AND = '( %s /\ d e. %s )' % (AN, DVP)
    snd = mkst(w, AND)
    dnn1 = snd([snd([snd([eldP], 'a1i', '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP),
                     snd([], 'simpr', 'd e. %s' % DVP)], 'mpbid',
                    '( d e. NN /\ d || P )')], 'simpld', 'd e. NN')
    udr1 = snd([snd([uf], 'ad2antrr', 'U : NN --> RR'), dnn1, w.inst('ffvelcdm')], 'syl2anc',
               '( U ` d ) e. RR')
    ifu1 = snd([udr1, w.s([], '0red', '( %s -> 0 e. RR )' % AND)], 'ifcld', '%s e. RR' % IFU)
    sumur = sn([sn([finP], 'adantr', '%s e. Fin' % DVP), ifu1], 'fsumrecl',
               'sum_ d e. %s %s e. RR' % (DVP, IFU))
    ifre = sn([wnr, w.s([], '0red', '( %s -> 0 e. RR )' % AN)], 'ifcld',
              'if ( ( P gcd n ) = 1 , 1 , 0 ) e. RR') if False else None
    if1re = sn([w.s([], '1red', '( %s -> 1 e. RR )' % AN),
                w.s([], '0red', '( %s -> 0 e. RR )' % AN)], 'ifcld',
               'if ( ( P gcd n ) = 1 , 1 , 0 ) e. RR')
    ifwre = sn([wnr, w.s([], '0red', '( %s -> 0 e. RR )' % AN)], 'ifcld',
               'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 ) e. RR')
    prodle = sn([if1re, sumur, wnr, wn0, umle2], 'lemul2ad',
                '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) ) <_ '
                '( ( W ` n ) x. sum_ d e. %s %s )' % (DVP, IFU))
    termle = sn([sn([facw], 'eqcomd',
                    'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 ) = '
                    '( ( W ` n ) x. if ( ( P gcd n ) = 1 , 1 , 0 ) )'), prodle], 'eqbrtrd',
                'if ( ( P gcd n ) = 1 , ( W ` n ) , 0 ) <_ '
                '( ( W ` n ) x. sum_ d e. %s %s )' % (DVP, IFU))
    prodre = sn([wnr, sumur], 'remulcld',
                '( ( W ` n ) x. sum_ d e. %s %s ) e. RR' % (DVP, IFU))
    step01 = st([d['afin'], ifwre, prodre, termle], 'fsumle', '%s <_ %s' % (SFS, T1))
    # ---------- T1 = T2
    com = st([st([st([d['afin'], d['assnn'], d['wf']], '3jca',
                     '( A e. Fin /\ A C_ NN /\ W : NN --> RR )'),
                  st([d['pnn'], uf], 'jca', '( P e. NN /\ U : NN --> RR )')], 'jca',
                  '( ( A e. Fin /\ A C_ NN /\ W : NN --> RR ) /\ ( P e. NN /\ U : NN --> RR ) )'),
              w.inst('siftcom')], 'syl', '%s = %s' % (T1, T2))
    # ---------- closures on DV ( P ) under A
    AD = '( %s /\ d e. %s )' % (A, DVP)
    sdd = mkst(w, AD)
    dnn = sdd([sdd([sdd([eldP], 'a1i', '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP),
                    sdd([], 'simpr', 'd e. %s' % DVP)], 'mpbid',
                   '( d e. NN /\ d || P )')], 'simpld', 'd e. NN')
    udr = sdd([sdd([uf], 'adantr', 'U : NN --> RR'), dnn, w.inst('ffvelcdm')], 'syl2anc',
              '( U ` d ) e. RR')
    udc = sdd([udr], 'recnd', '( U ` d ) e. CC')
    vdr = sdd([sdd([d['vf']], 'adantr', 'V : NN --> RR'), dnn, w.inst('ffvelcdm')], 'syl2anc',
              '( V ` d ) e. RR')
    vdc = sdd([vdr], 'recnd', '( V ` d ) e. CC')
    xr = sdd([d['xr']], 'adantr', 'X e. RR')
    xc = sdd([xr], 'recnd', 'X e. CC')
    ADN = '( %s /\ n e. A )' % AD
    sdn = mkst(w, ADN)
    nnn2 = sdn([sdn([d['assnn']], 'ad2antrr', 'A C_ NN'), sdn([], 'simpr', 'n e. A')], 'sseldd',
               'n e. NN')
    wnr2 = sdn([sdn([d['wf']], 'ad2antrr', 'W : NN --> RR'), nnn2, w.inst('ffvelcdm')],
               'syl2anc', '( W ` n ) e. RR')
    ifw2 = sdn([wnr2, w.s([], '0red', '( %s -> 0 e. RR )' % ADN)], 'ifcld', '%s e. RR' % IFW)
    msr = sdd([sdd([d['afin']], 'adantr', 'A e. Fin'), ifw2], 'fsumrecl', '%s e. RR' % MSD)
    msc = sdd([msr], 'recnd', '%s e. CC' % MSD)
    rmr = sdd([msr, sdd([vdr, xr], 'remulcld', '( ( V ` d ) x. X ) e. RR')], 'resubcld',
              '%s e. RR' % RMD)
    rmc = sdd([rmr], 'recnd', '%s e. CC' % RMD)
    # ---------- T2 = T3 termwise
    sub = sdd([udc, msc, sdd([vdc, xc], 'mulcld', '( ( V ` d ) x. X ) e. CC')], 'subdid',
              '( ( U ` d ) x. %s ) = ( ( ( U ` d ) x. %s ) - '
              '( ( U ` d ) x. ( ( V ` d ) x. X ) ) )' % (RMD, MSD))
    ass = sdd([udc, vdc, xc], 'mulassd',
              '( ( ( U ` d ) x. ( V ` d ) ) x. X ) = ( ( U ` d ) x. ( ( V ` d ) x. X ) )')
    comm = sdd([xc, sdd([udc, vdc], 'mulcld', '( ( U ` d ) x. ( V ` d ) ) e. CC')], 'mulcomd',
               '( X x. ( ( U ` d ) x. ( V ` d ) ) ) = ( ( ( U ` d ) x. ( V ` d ) ) x. X )')
    xeq = sdd([comm, ass], 'eqtrd',
              '( X x. ( ( U ` d ) x. ( V ` d ) ) ) = ( ( U ` d ) x. ( ( V ` d ) x. X ) )')
    rhs = sdd([sdd([xeq, sub], 'oveq12d',
                   '%s = ( ( ( U ` d ) x. ( ( V ` d ) x. X ) ) + ( ( ( U ` d ) x. %s ) - '
                   '( ( U ` d ) x. ( ( V ` d ) x. X ) ) ) )' % (TRM, MSD)),
               sdd([sdd([udc, sdd([vdc, xc], 'mulcld', '( ( V ` d ) x. X ) e. CC')], 'mulcld',
                        '( ( U ` d ) x. ( ( V ` d ) x. X ) ) e. CC'),
                    sdd([udc, msc], 'mulcld', '( ( U ` d ) x. %s ) e. CC' % MSD)], 'pncan3d',
                   '( ( ( U ` d ) x. ( ( V ` d ) x. X ) ) + ( ( ( U ` d ) x. %s ) - '
                   '( ( U ` d ) x. ( ( V ` d ) x. X ) ) ) ) = ( ( U ` d ) x. %s )'
                   % (MSD, MSD))], 'eqtrd', '%s = ( ( U ` d ) x. %s )' % (TRM, MSD))
    step23 = st([sdd([rhs], 'eqcomd', '( ( U ` d ) x. %s ) = %s' % (MSD, TRM))], 'sumeq2dv',
                '%s = %s' % (T2, T3))
    # ---------- T3 = T4
    add = st([finP, sdd([xc, sdd([udc, vdc], 'mulcld', '( ( U ` d ) x. ( V ` d ) ) e. CC')],
                        'mulcld', '( X x. ( ( U ` d ) x. ( V ` d ) ) ) e. CC'),
              sdd([udc, rmc], 'mulcld', '( ( U ` d ) x. %s ) e. CC' % RMD)], 'fsumadd',
             '%s = ( %s + %s )' % (T3, T4A, T4B))
    pull = st([finP, d['xr'] if False else st([d['xr']], 'recnd', 'X e. CC'),
               sdd([udc, vdc], 'mulcld', '( ( U ` d ) x. ( V ` d ) ) e. CC')], 'fsummulc2',
              '( X x. %s ) = %s' % (SUV, T4A))
    step45 = st([add, st([st([pull], 'eqcomd', '%s = ( X x. %s )' % (T4A, SUV))], 'oveq1d',
                         '( %s + %s ) = ( ( X x. %s ) + %s )' % (T4A, T4B, SUV, T4B))], 'eqtrd',
                '%s = ( ( X x. %s ) + %s )' % (T3, SUV, T4B))
    # ---------- T4B <_ SABS
    absle = sdd([sdd([sdd([udr, rmr], 'remulcld', '( ( U ` d ) x. %s ) e. RR' % RMD)], 'leabsd',
                     '( ( U ` d ) x. %s ) <_ ( abs ` ( ( U ` d ) x. %s ) )' % (RMD, RMD)),
                 sdd([udc, rmc], 'absmuld',
                     '( abs ` ( ( U ` d ) x. %s ) ) = '
                     '( ( abs ` ( U ` d ) ) x. ( abs ` %s ) )' % (RMD, RMD))], 'breqtrd',
                '( ( U ` d ) x. %s ) <_ ( ( abs ` ( U ` d ) ) x. ( abs ` %s ) )' % (RMD, RMD))
    absre = sdd([sdd([udc], 'abscld', '( abs ` ( U ` d ) ) e. RR'),
                 sdd([rmc], 'abscld', '( abs ` %s ) e. RR' % RMD)], 'remulcld',
                '( ( abs ` ( U ` d ) ) x. ( abs ` %s ) ) e. RR' % RMD)
    errle = st([finP, sdd([udr, rmr], 'remulcld', '( ( U ` d ) x. %s ) e. RR' % RMD), absre,
                absle], 'fsumle', '%s <_ %s' % (T4B, SABS))
    xsuvr = st([d['xr'], st([finP, sdd([udr, vdr], 'remulcld',
                                       '( ( U ` d ) x. ( V ` d ) ) e. RR')], 'fsumrecl',
                            '%s e. RR' % SUV)], 'remulcld', '( X x. %s ) e. RR' % SUV)
    t4br = st([finP, sdd([udr, rmr], 'remulcld', '( ( U ` d ) x. %s ) e. RR' % RMD)], 'fsumrecl',
              '%s e. RR' % T4B)
    sabsr = st([finP, absre], 'fsumrecl', '%s e. RR' % SABS)
    final = st([t4br, sabsr, xsuvr, errle], 'leadd2dd',
               '( ( X x. %s ) + %s ) <_ ( ( X x. %s ) + %s )' % (SUV, T4B, SUV, SABS))
    chain = st([st([com, step23], 'eqtrd', '%s = %s' % (T1, T3)), step45], 'eqtrd',
               '%s = ( ( X x. %s ) + %s )' % (T1, SUV, T4B))
    sfle = st([step01, chain], 'breqtrd', '%s <_ ( ( X x. %s ) + %s )' % (SFS, SUV, T4B))
    sfr = st([d['afin'], ifwre], 'fsumrecl', '%s e. RR' % SFS)
    w.qed([sfr, st([xsuvr, t4br], 'readdcld',
                   '( ( X x. %s ) + %s ) e. RR' % (SUV, T4B)),
           st([xsuvr, sabsr], 'readdcld', '( ( X x. %s ) + %s ) e. RR' % (SUV, SABS)),
           sfle, final], 'letrd',
          '( %s -> %s <_ ( ( X x. %s ) + %s ) )' % (A, SFS, SUV, SABS))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['wge0c']:
        globals()[f]().run()
