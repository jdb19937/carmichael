"""Sortie v2b: the Lambda squared upper Moebius inequality.

lamsqex   the inner divisor ranges of the Lambda squared coefficient extend to DV ( N )
lamsqsq   the triple sum over DV ( N ) is the square of the weight sum
lamsqub   the Lambda squared coefficients of a weight sequence with L ( 1 ) = 1 are upper Moebius
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *

LU = '( ( L ` u ) x. ( L ` e ) )'


def IFD(D):
    return 'if ( %s = ( u lcm e ) , %s , 0 )' % (D, LU)


def lamsqex():
    w = W('lamsqex', 'The inner divisor ranges of a Lambda squared coefficient extend from the '
                     'divisors of D to the divisors of any multiple N of D.')
    A = '( L : NN --> RR /\ N e. NN /\ ( D e. NN /\ D || N ) )'
    DVN = DV('N')
    DVD = DV('D')
    IF = IFD('D')
    st = mkst(w, A)
    lf = st([], 'simp1', 'L : NN --> RR')
    nnn = st([], 'simp2', 'N e. NN')
    dnn = st([], 'simp3l', 'D e. NN')
    ddn = st([], 'simp3r', 'D || N')
    nz = st([nnn], 'nnzd', 'N e. ZZ')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    finN = st([nnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVN)
    finD = st([dnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVD)
    # DV ( D ) C_ DV ( N )
    AX = '( %s /\ x e. NN )' % A
    sx = mkst(w, AX)
    ssimp = sx([sx([sx([sx([], 'simpr', 'x e. NN')], 'nnzd', 'x e. ZZ'),
                    sx([dz], 'adantr', 'D e. ZZ'), sx([nz], 'adantr', 'N e. ZZ')], '3jca',
                   '( x e. ZZ /\ D e. ZZ /\ N e. ZZ )'), w.inst('dvdstr')], 'syl',
               '( ( x || D /\ D || N ) -> x || N )')
    AXD = '( %s /\ x || D )' % AX
    sxd = mkst(w, AXD)
    xdn = sxd([sxd([ssimp], 'adantr', '( ( x || D /\ D || N ) -> x || N )'),
               sxd([sxd([], 'simpr', 'x || D'),
                    sxd([sx([ddn], 'adantr', 'D || N')], 'adantr', 'D || N')], 'jca',
                   '( x || D /\ D || N )')], 'mpd', 'x || N')
    sub = st([sx([xdn], 'ex', '( x || D -> x || N )')], 'ss2rabdv', '%s C_ %s' % (DVD, DVN))

    def elfacts(v, S, X):
        return w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (v, X, v, X))],
                   'elrab', '( %s e. %s <-> ( %s e. NN /\ %s || %s ) )' % (v, S, v, v, X))

    eluN = elfacts('u', DVN, 'N')
    eleN = elfacts('e', DVN, 'N')
    eluD = elfacts('u', DVD, 'D')
    eleD = elfacts('e', DVD, 'D')
    # closure of the body for u , e e. DV ( N )
    AU2 = '( %s /\ u e. %s )' % (A, DVN)
    AUE = '( %s /\ e e. %s )' % (AU2, DVN)
    sue = mkst(w, AUE)
    uc = sue([sue([eluN], 'a1i', '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN),
              w.s([], 'simplr', '( %s -> u e. %s )' % (AUE, DVN))], 'mpbid',
             '( u e. NN /\ u || N )')
    ec = sue([sue([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
              w.s([], 'simpr', '( %s -> e e. %s )' % (AUE, DVN))], 'mpbid',
             '( e e. NN /\ e || N )')
    lfue = sue([lf], 'ad2antrr', 'L : NN --> RR')
    lur = sue([lfue, sue([uc], 'simpld', 'u e. NN'), w.inst('ffvelcdm')], 'syl2anc',
              '( L ` u ) e. RR')
    ler = sue([lfue, sue([ec], 'simpld', 'e e. NN'), w.inst('ffvelcdm')], 'syl2anc',
              '( L ` e ) e. RR')
    bodyc = sue([sue([sue([lur], 'recnd', '( L ` u ) e. CC'),
                      sue([ler], 'recnd', '( L ` e ) e. CC')], 'mulcld', '%s e. CC' % LU),
                 w.s([], '0cnd', '( %s -> 0 e. CC )' % AUE)], 'ifcld', '%s e. CC' % IF)
    # ---- inner extension, for u e. DV ( D )
    AU = '( %s /\ u e. %s )' % (A, DVD)
    su = mkst(w, AU)
    uinD = w.s([], 'simpr', '( %s -> u e. %s )' % (AU, DVD))
    ucD = su([su([eluD], 'a1i', '( u e. %s <-> ( u e. NN /\ u || D ) )' % DVD), uinD], 'mpbid',
             '( u e. NN /\ u || D )')
    unnAU = su([ucD], 'simpld', 'u e. NN')
    AUE2 = '( %s /\ e e. %s )' % (AU, DVN)
    su2 = mkst(w, AUE2)
    lec = su2([su2([su2([lf], 'ad2antrr', 'L : NN --> RR'),
                    su2([su2([su2([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
                              su2([], 'simpr', 'e e. %s' % DVN)], 'mpbid',
                             '( e e. NN /\ e || N )')], 'simpld', 'e e. NN'),
                    w.inst('ffvelcdm')], 'syl2anc', '( L ` e ) e. RR')], 'recnd',
              '( L ` e ) e. CC')
    luc = su2([su2([su2([lf], 'ad2antrr', 'L : NN --> RR'),
                    su2([unnAU], 'adantr', 'u e. NN'), w.inst('ffvelcdm')], 'syl2anc',
                   '( L ` u ) e. RR')], 'recnd', '( L ` u ) e. CC')
    bodyc2 = su2([su2([luc, lec], 'mulcld', '%s e. CC' % LU),
                  w.s([], '0cnd', '( %s -> 0 e. CC )' % AUE2)], 'ifcld', '%s e. CC' % IF)
    AUEX = '( %s /\ e e. ( %s \ %s ) )' % (AU, DVN, DVD)
    sux = mkst(w, AUEX)
    edif = w.s([], 'simpr', '( %s -> e e. ( %s \ %s ) )' % (AUEX, DVN, DVD))
    einNx = sux([edif, w.inst('eldifi')], 'syl', 'e e. %s' % DVN)
    enotD = sux([edif, w.inst('eldifn')], 'syl', '-. e e. %s' % DVD)
    ennx = sux([sux([sux([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN), einNx],
                    'mpbid', '( e e. NN /\ e || N )')], 'simpld', 'e e. NN')
    AUEXD = '( %s /\ e || D )' % AUEX
    sxd2 = mkst(w, AUEXD)
    inD = sxd2([sxd2([eleD], 'a1i', '( e e. %s <-> ( e e. NN /\ e || D ) )' % DVD),
                sxd2([sxd2([ennx], 'adantr', 'e e. NN'), sxd2([], 'simpr', 'e || D')], 'jca',
                     '( e e. NN /\ e || D )')], 'mpbird', 'e e. %s' % DVD)
    endD = sux([enotD, inD], 'mtand', '-. e || D')
    AUEXE = '( %s /\ D = ( u lcm e ) )' % AUEX
    sxe = mkst(w, AUEXE)
    ez2 = sxe([sxe([ennx], 'adantr', 'e e. NN')], 'nnzd', 'e e. ZZ')
    uz2 = sxe([sxe([unnAU], 'ad2antrr', 'u e. NN')], 'nnzd', 'u e. ZZ')
    dl = sxe([sxe([uz2, ez2], 'jca', '( u e. ZZ /\ e e. ZZ )'), w.inst('dvdslcm')], 'syl',
             '( u || ( u lcm e ) /\ e || ( u lcm e ) )')
    edD = sxe([sxe([sxe([], 'simpr', 'D = ( u lcm e )')], 'eqcomd', '( u lcm e ) = D'),
               sxe([dl], 'simprd', 'e || ( u lcm e )')], 'breqtrd', 'e || D')
    zero = sux([sux([endD, edD], 'mtand', '-. D = ( u lcm e )')], 'iffalsed', '%s = 0' % IF)
    AUED = '( %s /\ e e. %s )' % (AU, DVD)
    sud = mkst(w, AUED)
    lecd = sud([sud([sud([lf], 'ad2antrr', 'L : NN --> RR'),
                     sud([sud([sud([eleD], 'a1i',
                                   '( e e. %s <-> ( e e. NN /\ e || D ) )' % DVD),
                               sud([], 'simpr', 'e e. %s' % DVD)], 'mpbid',
                              '( e e. NN /\ e || D )')], 'simpld', 'e e. NN'),
                     w.inst('ffvelcdm')], 'syl2anc', '( L ` e ) e. RR')], 'recnd',
               '( L ` e ) e. CC')
    lucd = sud([sud([sud([sud([lf], 'ad2antrr', 'L : NN --> RR'),
                          sud([unnAU], 'adantr', 'u e. NN'), w.inst('ffvelcdm')], 'syl2anc',
                         '( L ` u ) e. RR')], 'recnd', '( L ` u ) e. CC')], 'id',
               '( L ` u ) e. CC') if False else sud(
        [sud([sud([lf], 'ad2antrr', 'L : NN --> RR'), sud([unnAU], 'adantr', 'u e. NN'),
              w.inst('ffvelcdm')], 'syl2anc', '( L ` u ) e. RR')], 'recnd', '( L ` u ) e. CC')
    bodycD = sud([sud([lucd, lecd], 'mulcld', '%s e. CC' % LU),
                  w.s([], '0cnd', '( %s -> 0 e. CC )' % AUED)], 'ifcld', '%s e. CC' % IF)
    ext1 = su([su([sub], 'adantr', '%s C_ %s' % (DVD, DVN)), bodycD, zero,
               su([finN], 'adantr', '%s e. Fin' % DVN)], 'fsumss',
              'sum_ e e. %s %s = sum_ e e. %s %s' % (DVD, IF, DVN, IF))
    step1 = st([ext1], 'sumeq2dv',
               'sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s sum_ e e. %s %s'
               % (DVD, DVD, IF, DVD, DVN, IF))
    # ---- outer extension
    AUX = '( %s /\ u e. ( %s \ %s ) )' % (A, DVN, DVD)
    sox = mkst(w, AUX)
    udif = w.s([], 'simpr', '( %s -> u e. ( %s \ %s ) )' % (AUX, DVN, DVD))
    uinNo = sox([udif, w.inst('eldifi')], 'syl', 'u e. %s' % DVN)
    unotD = sox([udif, w.inst('eldifn')], 'syl', '-. u e. %s' % DVD)
    unno = sox([sox([sox([eluN], 'a1i', '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN), uinNo],
                    'mpbid', '( u e. NN /\ u || N )')], 'simpld', 'u e. NN')
    AUXD = '( %s /\ u || D )' % AUX
    soxd = mkst(w, AUXD)
    uinDo = soxd([soxd([eluD], 'a1i', '( u e. %s <-> ( u e. NN /\ u || D ) )' % DVD),
                  soxd([soxd([unno], 'adantr', 'u e. NN'), soxd([], 'simpr', 'u || D')], 'jca',
                       '( u e. NN /\ u || D )')], 'mpbird', 'u e. %s' % DVD)
    undD = sox([unotD, uinDo], 'mtand', '-. u || D')
    AUXE = '( %s /\ e e. %s )' % (AUX, DVN)
    soe = mkst(w, AUXE)
    enno2 = soe([soe([soe([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
                     soe([], 'simpr', 'e e. %s' % DVN)], 'mpbid', '( e e. NN /\ e || N )')],
                'simpld', 'e e. NN')
    AUXEE = '( %s /\ D = ( u lcm e ) )' % AUXE
    soee = mkst(w, AUXEE)
    uz3 = soee([soee([unno], 'ad2antrr', 'u e. NN')], 'nnzd', 'u e. ZZ')
    ez3 = soee([soee([enno2], 'adantr', 'e e. NN')], 'nnzd', 'e e. ZZ')
    dl2 = soee([soee([uz3, ez3], 'jca', '( u e. ZZ /\ e e. ZZ )'), w.inst('dvdslcm')], 'syl',
               '( u || ( u lcm e ) /\ e || ( u lcm e ) )')
    udD2 = soee([soee([soee([], 'simpr', 'D = ( u lcm e )')], 'eqcomd', '( u lcm e ) = D'),
                 soee([dl2], 'simpld', 'u || ( u lcm e )')], 'breqtrd', 'u || D')
    zero2 = soe([soe([soe([undD], 'adantr', '-. u || D'), udD2], 'mtand',
                     '-. D = ( u lcm e )')], 'iffalsed', '%s = 0' % IF)
    innerz = sox([sox([zero2], 'sumeq2dv',
                      'sum_ e e. %s %s = sum_ e e. %s 0' % (DVN, IF, DVN)),
                  sox([sox([sox([finN], 'adantr', '%s e. Fin' % DVN)], 'olcd',
                           '( %s C_ ( ZZ>= ` 1 ) \/ %s e. Fin )' % (DVN, DVN)),
                       w.inst('sumz')], 'syl', 'sum_ e e. %s 0 = 0' % DVN)], 'eqtrd',
                 'sum_ e e. %s %s = 0' % (DVN, IF))
    innerc2 = su([su([finN], 'adantr', '%s e. Fin' % DVN), bodyc2], 'fsumcl',
                 'sum_ e e. %s %s e. CC' % (DVN, IF))
    ext2 = st([sub, innerc2, innerz, finN], 'fsumss',
              'sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s sum_ e e. %s %s'
              % (DVD, DVN, IF, DVN, DVN, IF))
    w.qed([step1, ext2], 'eqtrd',
          '( %s -> sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s sum_ e e. %s %s )'
          % (A, DVD, DVD, IF, DVN, DVN, IF))
    return w


def lamsqsq():
    w = W('lamsqsq', 'The triple divisor sum of the Lambda squared coefficients is the square of '
                     'the sum of the weights.')
    A = '( L : NN --> RR /\ N e. NN )'
    DVN = DV('N')
    IF = 'if ( d = ( u lcm e ) , %s , 0 )' % LU
    SU = 'sum_ u e. %s ( L ` u )' % DVN
    SE = 'sum_ e e. %s ( L ` e )' % DVN
    st = mkst(w, A)
    lf = st([], 'simpl', 'L : NN --> RR')
    nnn = st([], 'simpr', 'N e. NN')
    finN = st([nnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVN)

    def elfacts(v):
        return w.s([w.s([], 'breq1', '( x = %s -> ( x || N <-> %s || N ) )' % (v, v))], 'elrab',
                   '( %s e. %s <-> ( %s e. NN /\ %s || N ) )' % (v, DVN, v, v))

    eluN = elfacts('u')
    eleN = elfacts('e')
    eldN = elfacts('d')
    # ---- for u , e e. DV ( N ) : the inner d sum collapses
    AU = '( %s /\ u e. %s )' % (A, DVN)
    su = mkst(w, AU)
    AUE = '( %s /\ e e. %s )' % (AU, DVN)
    sue = mkst(w, AUE)
    uc = sue([sue([eluN], 'a1i', '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN),
              w.s([], 'simplr', '( %s -> u e. %s )' % (AUE, DVN))], 'mpbid',
             '( u e. NN /\ u || N )')
    ec = sue([sue([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
              w.s([], 'simpr', '( %s -> e e. %s )' % (AUE, DVN))], 'mpbid',
             '( e e. NN /\ e || N )')
    unn = sue([uc], 'simpld', 'u e. NN')
    udn = sue([uc], 'simprd', 'u || N')
    enn = sue([ec], 'simpld', 'e e. NN')
    edn = sue([ec], 'simprd', 'e || N')
    uz = sue([unn], 'nnzd', 'u e. ZZ')
    ez = sue([enn], 'nnzd', 'e e. ZZ')
    nzue = sue([sue([nnn], 'ad2antrr', 'N e. NN')], 'nnzd', 'N e. ZZ')
    lfue = sue([lf], 'ad2antrr', 'L : NN --> RR')
    luc = sue([sue([lfue, unn, w.inst('ffvelcdm')], 'syl2anc', '( L ` u ) e. RR')], 'recnd',
              '( L ` u ) e. CC')
    lec = sue([sue([lfue, enn, w.inst('ffvelcdm')], 'syl2anc', '( L ` e ) e. RR')], 'recnd',
              '( L ` e ) e. CC')
    luec = sue([luc, lec], 'mulcld', '%s e. CC' % LU)
    lcmnn = sue([sue([sue([uz, ez], 'jca', '( u e. ZZ /\ e e. ZZ )'),
                      sue([sue([w.s([], 'ioran',
                                    '( -. ( u = 0 \/ e = 0 ) <-> ( -. u = 0 /\ -. e = 0 ) )')],
                               'a1i',
                               '( -. ( u = 0 \/ e = 0 ) <-> ( -. u = 0 /\ -. e = 0 ) )'),
                           sue([sue([sue([unn], 'nnne0d', 'u =/= 0')], 'neneqd', '-. u = 0'),
                                sue([sue([enn], 'nnne0d', 'e =/= 0')], 'neneqd', '-. e = 0')],
                               'jca', '( -. u = 0 /\ -. e = 0 )')], 'mpbird',
                          '-. ( u = 0 \/ e = 0 )')], 'jca',
                     '( ( u e. ZZ /\ e e. ZZ ) /\ -. ( u = 0 \/ e = 0 ) )'),
                 w.inst('lcmn0cl')], 'syl', '( u lcm e ) e. NN')
    lcmdn = sue([sue([sue([nzue, uz, ez], '3jca', '( N e. ZZ /\ u e. ZZ /\ e e. ZZ )'),
                      w.inst('lcmdvds')], 'syl',
                     '( ( u || N /\ e || N ) -> ( u lcm e ) || N )'),
                 sue([udn, edn], 'jca', '( u || N /\ e || N )')], 'mpd', '( u lcm e ) || N')
    lcmin = sue([w.s([w.s([], 'breq1',
                          '( x = ( u lcm e ) -> ( x || N <-> ( u lcm e ) || N ) )')], 'elrab',
                     '( ( u lcm e ) e. %s <-> ( ( u lcm e ) e. NN /\ ( u lcm e ) || N ) )' % DVN),
                 sue([lcmnn, lcmdn], 'jca',
                     '( ( u lcm e ) e. NN /\ ( u lcm e ) || N )')], 'sylibr',
                '( u lcm e ) e. %s' % DVN)
    snss = sue([lcmin], 'snssd', '{ ( u lcm e ) } C_ %s' % DVN)
    ASN = '( %s /\ d e. { ( u lcm e ) } )' % AUE
    ssn = mkst(w, ASN)
    bcsn = ssn([ssn([luec], 'adantr', '%s e. CC' % LU),
                w.s([], '0cnd', '( %s -> 0 e. CC )' % ASN)], 'ifcld', '%s e. CC' % IF)
    ADF = '( %s /\ d e. ( %s \ { ( u lcm e ) } ) )' % (AUE, DVN)
    sdf = mkst(w, ADF)
    dne = sdf([sdf([], 'simpr', 'd e. ( %s \ { ( u lcm e ) } )' % DVN), w.inst('eldifsni')],
              'syl', 'd =/= ( u lcm e )')
    zero = sdf([sdf([dne], 'neneqd', '-. d = ( u lcm e )')], 'iffalsed', '%s = 0' % IF)
    sss = sue([snss, bcsn, zero, sue([finN], 'ad2antrr', '%s e. Fin' % DVN)], 'fsumss',
              'sum_ d e. { ( u lcm e ) } %s = sum_ d e. %s %s' % (IF, DVN, IF))
    hsn = w.s([w.s([], 'id', '( d = ( u lcm e ) -> d = ( u lcm e ) )')], 'iftrued',
              '( d = ( u lcm e ) -> %s = %s )' % (IF, LU))
    instsn = w.s([hsn], 'sumsn',
                 '( ( ( u lcm e ) e. _V /\ %s e. CC ) -> sum_ d e. { ( u lcm e ) } %s = %s )'
                 % (LU, IF, LU))
    snval = sue([sue([lcmnn], 'elexd', '( u lcm e ) e. _V'), luec, instsn], 'syl2anc',
                'sum_ d e. { ( u lcm e ) } %s = %s' % (IF, LU))
    collapse = sue([sue([sss], 'eqcomd',
                        'sum_ d e. %s %s = sum_ d e. { ( u lcm e ) } %s' % (DVN, IF, IF)),
                    snval], 'eqtrd', 'sum_ d e. %s %s = %s' % (DVN, IF, LU))
    # ---- swap d out of the two outer sums
    ADU = '( %s /\ ( d e. %s /\ u e. %s ) )' % (A, DVN, DVN)
    sdu = mkst(w, ADU)
    ADUE = '( %s /\ e e. %s )' % (ADU, DVN)
    sdue = mkst(w, ADUE)
    uc2 = sdue([sdue([eluN], 'a1i', '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN),
                sdue([sdue([], 'simplr', '( d e. %s /\ u e. %s )' % (DVN, DVN))], 'simprd',
                     'u e. %s' % DVN)], 'mpbid', '( u e. NN /\ u || N )')
    ec2 = sdue([sdue([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
                sdue([], 'simpr', 'e e. %s' % DVN)], 'mpbid', '( e e. NN /\ e || N )')
    lf2 = sdue([lf], 'ad2antrr', 'L : NN --> RR')
    bc2 = sdue([sdue([sdue([sdue([lf2, sdue([uc2], 'simpld', 'u e. NN'), w.inst('ffvelcdm')],
                                 'syl2anc', '( L ` u ) e. RR')], 'recnd', '( L ` u ) e. CC'),
                      sdue([sdue([lf2, sdue([ec2], 'simpld', 'e e. NN'), w.inst('ffvelcdm')],
                                 'syl2anc', '( L ` e ) e. RR')], 'recnd', '( L ` e ) e. CC')],
                     'mulcld', '%s e. CC' % LU),
                w.s([], '0cnd', '( %s -> 0 e. CC )' % ADUE)], 'ifcld', '%s e. CC' % IF)
    innerc = sdu([sdu([finN], 'adantr', '%s e. Fin' % DVN), bc2], 'fsumcl',
                 'sum_ e e. %s %s e. CC' % (DVN, IF))
    swap1 = st([finN, finN, innerc], 'fsumcom',
               'sum_ d e. %s sum_ u e. %s sum_ e e. %s %s = '
               'sum_ u e. %s sum_ d e. %s sum_ e e. %s %s' % (DVN, DVN, DVN, IF, DVN, DVN, DVN, IF))
    AUD = '( %s /\ ( d e. %s /\ e e. %s ) )' % (AU, DVN, DVN)
    sud = mkst(w, AUD)
    uc3 = sud([sud([eluN], 'a1i', '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN),
               w.s([], 'simplr', '( %s -> u e. %s )' % (AUD, DVN))], 'mpbid',
              '( u e. NN /\ u || N )')
    ec3 = sud([sud([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
               sud([sud([], 'simpr', '( d e. %s /\ e e. %s )' % (DVN, DVN))], 'simprd',
                   'e e. %s' % DVN)], 'mpbid', '( e e. NN /\ e || N )')
    lf3 = sud([lf], 'ad2antrr', 'L : NN --> RR')
    bc3 = sud([sud([sud([sud([lf3, sud([uc3], 'simpld', 'u e. NN'), w.inst('ffvelcdm')],
                             'syl2anc', '( L ` u ) e. RR')], 'recnd', '( L ` u ) e. CC'),
                    sud([sud([lf3, sud([ec3], 'simpld', 'e e. NN'), w.inst('ffvelcdm')],
                             'syl2anc', '( L ` e ) e. RR')], 'recnd', '( L ` e ) e. CC')],
                   'mulcld', '%s e. CC' % LU),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % AUD)], 'ifcld', '%s e. CC' % IF)
    swap2 = su([su([finN], 'adantr', '%s e. Fin' % DVN),
                su([finN], 'adantr', '%s e. Fin' % DVN), bc3], 'fsumcom',
               'sum_ d e. %s sum_ e e. %s %s = sum_ e e. %s sum_ d e. %s %s'
               % (DVN, DVN, IF, DVN, DVN, IF))
    inner2 = su([su([swap2, su([collapse], 'sumeq2dv',
                               'sum_ e e. %s sum_ d e. %s %s = sum_ e e. %s %s'
                               % (DVN, DVN, IF, DVN, LU))], 'eqtrd',
                    'sum_ d e. %s sum_ e e. %s %s = sum_ e e. %s %s' % (DVN, DVN, IF, DVN, LU)),
                 su([su([finN], 'adantr', '%s e. Fin' % DVN),
                     su([su([su([lf], 'adantr', 'L : NN --> RR'),
                             su([su([su([eluN], 'a1i',
                                        '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN),
                                     su([], 'simpr', 'u e. %s' % DVN)], 'mpbid',
                                    '( u e. NN /\ u || N )')], 'simpld', 'u e. NN'),
                             w.inst('ffvelcdm')], 'syl2anc', '( L ` u ) e. RR')], 'recnd',
                        '( L ` u ) e. CC'),
                     sue([lec], 'id', '( L ` e ) e. CC') if False else lec], 'fsummulc2',
                    '( ( L ` u ) x. %s ) = sum_ e e. %s %s' % (SE, DVN, LU))], 'eqtr4d',
                'sum_ d e. %s sum_ e e. %s %s = ( ( L ` u ) x. %s )' % (DVN, DVN, IF, SE))
    outer = st([swap1, st([inner2], 'sumeq2dv',
                          'sum_ u e. %s sum_ d e. %s sum_ e e. %s %s = '
                          'sum_ u e. %s ( ( L ` u ) x. %s )'
                          % (DVN, DVN, DVN, IF, DVN, SE))], 'eqtrd',
               'sum_ d e. %s sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s ( ( L ` u ) x. %s )'
               % (DVN, DVN, DVN, IF, DVN, SE))
    # ---- pull the constant out and recognise the square
    AUS = '( %s /\ u e. %s )' % (A, DVN)
    sus = mkst(w, AUS)
    lucs = sus([sus([sus([lf], 'adantr', 'L : NN --> RR'),
                     sus([sus([sus([eluN], 'a1i', '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN),
                               sus([], 'simpr', 'u e. %s' % DVN)], 'mpbid',
                              '( u e. NN /\ u || N )')], 'simpld', 'u e. NN'),
                     w.inst('ffvelcdm')], 'syl2anc', '( L ` u ) e. RR')], 'recnd',
               '( L ` u ) e. CC')
    secc = st([finN, sus([lucs], 'id', '( L ` u ) e. CC') if False else lucs], 'fsumcl',
              '%s e. CC' % SU)
    AES = '( %s /\ e e. %s )' % (A, DVN)
    ses = mkst(w, AES)
    lecs = ses([ses([ses([lf], 'adantr', 'L : NN --> RR'),
                     ses([ses([ses([eleN], 'a1i', '( e e. %s <-> ( e e. NN /\ e || N ) )' % DVN),
                               ses([], 'simpr', 'e e. %s' % DVN)], 'mpbid',
                              '( e e. NN /\ e || N )')], 'simpld', 'e e. NN'),
                     w.inst('ffvelcdm')], 'syl2anc', '( L ` e ) e. RR')], 'recnd',
               '( L ` e ) e. CC')
    seccE = st([finN, lecs], 'fsumcl', '%s e. CC' % SE)
    pull = st([finN, lucs, seccE], 'fsummulc1',
              '( %s x. %s ) = sum_ u e. %s ( ( L ` u ) x. %s )' % (SU, SE, DVN, SE))
    cbv = st([w.s([], 'cbvsumv', '%s = %s' % (SE, SU))], 'a1i', '%s = %s' % (SE, SU))
    sqv = st([st([cbv], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (SU, SE, SU, SU)),
              st([secc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (SU, SU, SU))], 'eqtr4d',
             '( %s x. %s ) = ( %s ^ 2 )' % (SU, SE, SU))
    w.qed([st([outer, st([pull], 'eqcomd',
                         'sum_ u e. %s ( ( L ` u ) x. %s ) = ( %s x. %s )' % (DVN, SE, SU, SE))],
              'eqtrd',
              'sum_ d e. %s sum_ u e. %s sum_ e e. %s %s = ( %s x. %s )'
              % (DVN, DVN, DVN, IF, SU, SE)), sqv], 'eqtrd',
          '( %s -> sum_ d e. %s sum_ u e. %s sum_ e e. %s %s = ( %s ^ 2 ) )'
          % (A, DVN, DVN, DVN, IF, SU))
    return w


def lamsqub():
    w = W('lamsqub', 'The Lambda squared coefficients of a weight sequence with L ( 1 ) = 1 are '
                     'upper Moebius.')
    A = '( L : NN --> RR /\ ( L ` 1 ) = 1 /\ N e. NN )'
    DVN = DV('N')
    IF = 'if ( d = ( u lcm e ) , %s , 0 )' % LU
    SU = 'sum_ u e. %s ( L ` u )' % DVN
    TRIPLE = 'sum_ d e. %s sum_ u e. %s sum_ e e. %s %s' % (DVN, DV('d'), DV('d'), IF)
    FLAT = 'sum_ d e. %s sum_ u e. %s sum_ e e. %s %s' % (DVN, DVN, DVN, IF)
    st = mkst(w, A)
    lf = st([], 'simp1', 'L : NN --> RR')
    l1 = st([], 'simp2', '( L ` 1 ) = 1')
    nnn = st([], 'simp3', 'N e. NN')
    finN = st([nnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVN)
    eluN = w.s([w.s([], 'breq1', '( x = u -> ( x || N <-> u || N ) )')], 'elrab',
               '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN)
    eldN = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\ d || N ) )' % DVN)
    # step 1: flatten the inner ranges
    AD = '( %s /\ d e. %s )' % (A, DVN)
    sd = mkst(w, AD)
    dc = sd([sd([eldN], 'a1i', '( d e. %s <-> ( d e. NN /\ d || N ) )' % DVN),
             sd([], 'simpr', 'd e. %s' % DVN)], 'mpbid', '( d e. NN /\ d || N )')
    ext = sd([sd([sd([lf], 'adantr', 'L : NN --> RR'), sd([nnn], 'adantr', 'N e. NN'), dc],
                 '3jca', '( L : NN --> RR /\ N e. NN /\ ( d e. NN /\ d || N ) )'),
              w.inst('lamsqex')], 'syl',
             'sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s sum_ e e. %s %s'
             % (DV('d'), DV('d'), IF, DVN, DVN, IF))
    flat = st([ext], 'sumeq2dv', '%s = %s' % (TRIPLE, FLAT))
    sq = st([st([lf, nnn], 'jca', '( L : NN --> RR /\ N e. NN )'), w.inst('lamsqsq')], 'syl',
            '%s = ( %s ^ 2 )' % (FLAT, SU))
    val = st([flat, sq], 'eqtrd', '%s = ( %s ^ 2 )' % (TRIPLE, SU))
    # SU is real
    AU = '( %s /\ u e. %s )' % (A, DVN)
    sus = mkst(w, AU)
    lur = sus([sus([lf], 'adantr', 'L : NN --> RR'),
               sus([sus([sus([eluN], 'a1i', '( u e. %s <-> ( u e. NN /\ u || N ) )' % DVN),
                         sus([], 'simpr', 'u e. %s' % DVN)], 'mpbid',
                        '( u e. NN /\ u || N )')], 'simpld', 'u e. NN'),
               w.inst('ffvelcdm')], 'syl2anc', '( L ` u ) e. RR')
    sur = st([finN, lur], 'fsumrecl', '%s e. RR' % SU)
    sqr = st([sur], 'resqcld', '( %s ^ 2 ) e. RR' % SU)
    # ---- case N = 1
    A1 = '( %s /\ N = 1 )' % A
    s1 = mkst(w, A1)
    heq = s1([], 'simpr', 'N = 1')
    rab1 = s1([s1([heq], 'breq2d', '( x || N <-> x || 1 )')], 'rabbidv',
              '%s = %s' % (DVN, DV('1')))
    A1X = '( %s /\ x e. NN )' % A1
    s1x = mkst(w, A1X)
    d1 = s1x([s1x([s1x([], 'simpr', 'x e. NN')], 'nnnn0d', 'x e. NN0'), w.inst('dvds1')],
             'syl', '( x || 1 <-> x = 1 )')
    rab2 = s1([d1], 'rabbidva', '%s = { x e. NN | x = 1 }' % DV('1'))
    rab3 = s1([s1([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), w.inst('rabsn')], 'syl',
              '{ x e. NN | x = 1 } = { 1 }')
    dvset = s1([s1([rab1, rab2], 'eqtrd', '%s = { x e. NN | x = 1 }' % DVN), rab3], 'eqtrd',
               '%s = { 1 }' % DVN)
    sumeq = s1([dvset], 'sumeq1d', '%s = sum_ u e. { 1 } ( L ` u )' % SU)
    hsn = w.s([], 'fveq2', '( u = 1 -> ( L ` u ) = ( L ` 1 ) )')
    instsn = w.s([hsn], 'sumsn',
                 '( ( 1 e. _V /\ ( L ` 1 ) e. CC ) -> sum_ u e. { 1 } ( L ` u ) = ( L ` 1 ) )')
    l1a = s1([l1], 'adantr', '( L ` 1 ) = 1')
    l1c = s1([l1a, s1([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'eqeltrd',
             '( L ` 1 ) e. CC')
    snval = s1([s1([w.s([], '1ex', '1 e. _V')], 'a1i', '1 e. _V'), l1c, instsn], 'syl2anc',
               'sum_ u e. { 1 } ( L ` u ) = ( L ` 1 )')
    sueq = s1([s1([sumeq, snval], 'eqtrd', '%s = ( L ` 1 )' % SU), l1a], 'eqtrd', '%s = 1' % SU)
    sq1v = s1([s1([sueq], 'oveq1d', '( %s ^ 2 ) = ( 1 ^ 2 )' % SU),
               s1([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1')], 'eqtrd',
              '( %s ^ 2 ) = 1' % SU)
    lhs1 = s1([heq], 'iftrued', 'if ( N = 1 , 1 , 0 ) = 1')
    le1 = s1([w.s([], '1red', '( %s -> 1 e. RR )' % A1)], 'leidd', '1 <_ 1')
    case1 = s1([s1([lhs1, le1], 'eqbrtrd', 'if ( N = 1 , 1 , 0 ) <_ 1'),
                s1([sq1v], 'eqcomd', '1 = ( %s ^ 2 )' % SU)], 'breqtrd',
               'if ( N = 1 , 1 , 0 ) <_ ( %s ^ 2 )' % SU)
    # ---- case N =/= 1
    A2 = '( %s /\ -. N = 1 )' % A
    s2 = mkst(w, A2)
    lhs0 = s2([s2([], 'simpr', '-. N = 1')], 'iffalsed', 'if ( N = 1 , 1 , 0 ) = 0')
    ge0 = s2([s2([sur], 'adantr', '%s e. RR' % SU)], 'sqge0d', '0 <_ ( %s ^ 2 )' % SU)
    case2 = s2([lhs0, ge0], 'eqbrtrd', 'if ( N = 1 , 1 , 0 ) <_ ( %s ^ 2 )' % SU)
    both = st([case1, case2], 'pm2.61dan', 'if ( N = 1 , 1 , 0 ) <_ ( %s ^ 2 )' % SU)
    w.qed([both, st([val], 'eqcomd', '( %s ^ 2 ) = %s' % (SU, TRIPLE))], 'breqtrd',
          '( %s -> if ( N = 1 , 1 , 0 ) <_ %s )' % (A, TRIPLE))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['lamsqex']:
        globals()[f]().run()
