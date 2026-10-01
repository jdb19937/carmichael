"""Sortie v2b: the divisor sum of the Selberg terms.

vsubrp   1 - ( V ` Q ) is a positive real for a prime divisor Q of P
gtprm    the Selberg term at a prime divisor of P
gtfprod  the Selberg term as a product over the prime divisors
gtsum    sum over the divisors of D of the Selberg terms is GT ( D ) / ( V ` D )
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *

BODY = '( 1 / ( 1 - ( V ` q ) ) )'


def QUOT(v): return '( ( V ` %s ) / ( 1 - ( V ` %s ) ) )' % (v, v)
def RECP(v): return '( 1 / ( 1 - ( V ` %s ) ) )' % v


def vsubrp():
    w = W('vsubrp', 'One minus the density at a prime divisor of the sifting product is a '
                    'positive real.')
    A = '( %s /\\ ( Q e. Prime /\\ Q || P ) )' % SH
    d = shsteps(w, A, (SH,))
    st = d['st']
    qprm = st([], 'simprl', 'Q e. Prime')
    qdp = st([], 'simprr', 'Q || P')
    qnn = st([qprm, w.inst('prmnn')], 'syl', 'Q e. NN')
    vqr = st([d['vf'], qnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` Q ) e. RR')
    both = st([d['vprm'], st([qprm, qdp], 'jca', '( Q e. Prime /\\ Q || P )'), w.inst('vprmc')],
              'syl2anc', '( 0 < ( V ` Q ) /\\ ( V ` Q ) < 1 )')
    one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
    pos = st([st([vqr, one], 'posdifd', '( ( V ` Q ) < 1 <-> 0 < ( 1 - ( V ` Q ) ) )'),
              st([both], 'simprd', '( V ` Q ) < 1')], 'mpbid', '0 < ( 1 - ( V ` Q ) )')
    w.qed([st([one, vqr], 'resubcld', '( 1 - ( V ` Q ) ) e. RR'), pos], 'elrpd',
          '( %s -> ( 1 - ( V ` Q ) ) e. RR+ )' % A)
    return w


def gtprm():
    w = W('gtprm', 'The Selberg term at a prime divisor of the sifting product.')
    A = '( %s /\\ ( Q e. Prime /\\ Q || P ) )' % SH
    PFQ = PF('Q')
    d = shsteps(w, A, (SH,))
    st = d['st']
    qprm = st([], 'simprl', 'Q e. Prime')
    qdp = st([], 'simprr', 'Q || P')
    qnn = st([qprm, w.inst('prmnn')], 'syl', 'Q e. NN')
    vqr = st([d['vf'], qnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` Q ) e. RR')
    vqc = st([vqr], 'recnd', '( V ` Q ) e. CC')
    subrp = st([d['sh'], st([qprm, qdp], 'jca', '( Q e. Prime /\\ Q || P )'), w.inst('vsubrp')],
               'syl2anc', '( 1 - ( V ` Q ) ) e. RR+')
    subc = st([subrp], 'rpcnd', '( 1 - ( V ` Q ) ) e. CC')
    subne = st([subrp], 'rpne0d', '( 1 - ( V ` Q ) ) =/= 0')
    recc = st([st([subrp], 'rpreccld', '%s e. RR+' % RECP('Q'))], 'rpcnd', '%s e. CC' % RECP('Q'))
    # the prime divisors of Q are { Q }
    AR = '( %s /\\ r e. Prime )' % A
    sr = mkst(w, AR)
    rprm = w.s([], 'simpr', '( %s -> r e. Prime )' % AR)
    bi = sr([sr([sr([rprm, w.inst('prmuz2')], 'syl', 'r e. ( ZZ>= ` 2 )'),
                 sr([qprm], 'adantr', 'Q e. Prime')], 'jca',
                '( r e. ( ZZ>= ` 2 ) /\\ Q e. Prime )'), w.inst('dvdsprm')], 'syl',
            '( r || Q <-> r = Q )')
    rab1 = st([bi], 'rabbidva', '%s = { r e. Prime | r = Q }' % PFQ)
    rab2 = st([qprm, w.inst('rabsn')], 'syl', '{ r e. Prime | r = Q } = { Q }')
    pfeq = st([rab1, rab2], 'eqtrd', '%s = { Q }' % PFQ)
    # the product over { Q }
    hsn = w.s([w.s([w.s([], 'fveq2', '( q = Q -> ( V ` q ) = ( V ` Q ) )')], 'oveq2d',
                   '( q = Q -> ( 1 - ( V ` q ) ) = ( 1 - ( V ` Q ) ) )')], 'oveq2d',
              '( q = Q -> %s = %s )' % (BODY, RECP('Q')))
    inst = w.s([hsn], 'prodsn',
               '( ( Q e. _V /\\ %s e. CC ) -> prod_ q e. { Q } %s = %s )'
               % (RECP('Q'), BODY, RECP('Q')))
    snval = st([st([qnn], 'elexd', 'Q e. _V'), recc, inst], 'syl2anc',
               'prod_ q e. { Q } %s = %s' % (BODY, RECP('Q')))
    prd = st([st([pfeq], 'prodeq1d',
                 'prod_ q e. %s %s = prod_ q e. { Q } %s' % (PFQ, BODY, BODY)), snval], 'eqtrd',
             'prod_ q e. %s %s = %s' % (PFQ, BODY, RECP('Q')))
    w.qed([st([prd], 'oveq2d', '%s = ( ( V ` Q ) x. %s )' % (GT('Q'), RECP('Q'))),
           st([vqc, subc, subne], 'divrecd',
              '%s = ( ( V ` Q ) x. %s )' % (QUOT('Q'), RECP('Q')))], 'eqtr4d',
          '( %s -> %s = %s )' % (A, GT('Q'), QUOT('Q')))
    return w


def gtfprod():
    w = W('gtfprod', 'The Selberg term as a product over the prime divisors.')
    A = '( %s /\\ ( K e. NN /\\ K || P ) )' % SH
    TR = PF('K')
    d = shsteps(w, A, (SH,))
    st = d['st']
    knn = st([], 'simprl', 'K e. NN')
    kdp = st([], 'simprr', 'K || P')
    kz = st([knn], 'nnzd', 'K e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    ksq = st([st([st([d['pnn'], knn, kdp], '3jca', '( P e. NN /\\ K e. NN /\\ K || P )'),
                  w.inst('dvdssqf')], 'syl',
                 '( ( mmu ` P ) =/= 0 -> ( mmu ` K ) =/= 0 )'), d['psqf']], 'mpd',
             '( mmu ` K ) =/= 0')
    fin = st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('K', 'p'), TR))], 'a1i',
                 '%s = %s' % (PF('K', 'p'), TR)),
              st([knn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('K', 'p'))], 'eqeltrrd',
             '%s e. Fin' % TR)
    vk = st([d['vh'], st([knn, ksq], 'jca', '( K e. NN /\\ ( mmu ` K ) =/= 0 )'),
             w.inst('vsqfprod')], 'syl2anc',
            '( V ` K ) = prod_ p e. %s ( V ` p )' % TR)
    # facts for a prime divisor p of K
    AP = '( %s /\\ p e. %s )' % (A, TR)
    sp = mkst(w, AP)
    elp = w.s([w.s([], 'breq1', '( r = p -> ( r || K <-> p || K ) )')], 'elrab',
              '( p e. %s <-> ( p e. Prime /\\ p || K ) )' % TR)
    pc = sp([sp([elp], 'a1i', '( p e. %s <-> ( p e. Prime /\\ p || K ) )' % TR),
             sp([], 'simpr', 'p e. %s' % TR)], 'mpbid', '( p e. Prime /\\ p || K )')
    pprm = sp([pc], 'simpld', 'p e. Prime')
    pdk = sp([pc], 'simprd', 'p || K')
    pdp = sp([sp([sp([sp([pprm, w.inst('prmz')], 'syl', 'p e. ZZ'),
                      sp([kz], 'adantr', 'K e. ZZ'), sp([pz], 'adantr', 'P e. ZZ')], '3jca',
                     '( p e. ZZ /\\ K e. ZZ /\\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                  '( ( p || K /\\ K || P ) -> p || P )'),
              sp([pdk, sp([kdp], 'adantr', 'K || P')], 'jca', '( p || K /\\ K || P )')], 'mpd',
             'p || P')
    vpc = sp([sp([sp([d['vf']], 'adantr', 'V : NN --> RR'),
                  sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN'), w.inst('ffvelcdm')], 'syl2anc',
                 '( V ` p ) e. RR')], 'recnd', '( V ` p ) e. CC')
    subrp = sp([sp([d['sh']], 'adantr', SH), sp([pprm, pdp], 'jca',
                                               '( p e. Prime /\\ p || P )'),
                w.inst('vsubrp')], 'syl2anc', '( 1 - ( V ` p ) ) e. RR+')
    recpc = sp([sp([subrp], 'rpreccld', '%s e. RR+' % RECP('p'))], 'rpcnd',
               '%s e. CC' % RECP('p'))
    quot = sp([vpc, sp([subrp], 'rpcnd', '( 1 - ( V ` p ) ) e. CC'),
               sp([subrp], 'rpne0d', '( 1 - ( V ` p ) ) =/= 0')], 'divrecd',
              '%s = ( ( V ` p ) x. %s )' % (QUOT('p'), RECP('p')))
    cbv = st([w.s([], 'cbvprodv',
                  'prod_ q e. %s %s = prod_ p e. %s %s' % (TR, BODY, TR, RECP('p')))], 'a1i',
             'prod_ q e. %s %s = prod_ p e. %s %s' % (TR, BODY, TR, RECP('p')))
    mul = st([fin, vpc, recpc], 'fprodmul',
             'prod_ p e. %s ( ( V ` p ) x. %s ) = '
             '( prod_ p e. %s ( V ` p ) x. prod_ p e. %s %s )' % (TR, RECP('p'), TR, TR, RECP('p')))
    qeq = st([sp([quot], 'id', '%s = ( ( V ` p ) x. %s )' % (QUOT('p'), RECP('p')))
              if False else quot], 'prodeq2dv',
             'prod_ p e. %s %s = prod_ p e. %s ( ( V ` p ) x. %s )'
             % (TR, QUOT('p'), TR, RECP('p')))
    w.qed([st([vk, cbv], 'oveq12d',
              '%s = ( prod_ p e. %s ( V ` p ) x. prod_ p e. %s %s )' % (GT('K'), TR, TR, RECP('p'))),
           st([qeq, mul], 'eqtrd',
              'prod_ p e. %s %s = ( prod_ p e. %s ( V ` p ) x. prod_ p e. %s %s )'
              % (TR, QUOT('p'), TR, TR, RECP('p')))], 'eqtr4d',
          '( %s -> %s = prod_ p e. %s %s )' % (A, GT('K'), TR, QUOT('p')))
    return w


BODYT = 'if ( t || P , %s , 0 )' % QUOT('t')
BODYP = 'if ( p || P , %s , 0 )' % QUOT('p')
GFN = '( t e. Prime |-> %s )' % BODYT


def gtsum():
    w = W('gtsum', 'The sum of the Selberg terms over the divisors of D is the Selberg term of D '
                   'divided by the density at D.')
    A = '( %s /\ ( D e. NN /\ D || P ) )' % SH
    DVD = DV('D')
    SD = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\ x || D ) }'
    PFQd, PFRd = PF('d', 'q'), PF('d', 'r')
    PFQD, PFRD = PF('D', 'q'), PF('D', 'r')
    PRD = 'prod_ q e. %s %s' % (PFRD, BODY)
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simprl', 'D e. NN')
    ddp = st([], 'simprr', 'D || P')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    dsq = st([st([st([d['pnn'], dnn, ddp], '3jca', '( P e. NN /\ D e. NN /\ D || P )'),
                  w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` D ) =/= 0 )'),
              d['psqf']], 'mpd', '( mmu ` D ) =/= 0')
    hgfn = w.s([], 'eqid', '%s = %s' % (GFN, GFN))
    # ---- the function is into CC
    AT = '( %s /\ t e. Prime )' % A
    sat = mkst(w, AT)
    tprm = w.s([], 'simpr', '( %s -> t e. Prime )' % AT)
    vtr = sat([sat([sat([d['vf']], 'adantr', 'V : NN --> RR'),
                    sat([tprm, w.inst('prmnn')], 'syl', 't e. NN')], 'jca',
                   '( V : NN --> RR /\ t e. NN )'), w.inst('ffvelcdm')], 'syl',
              '( V ` t ) e. RR')
    ATT = '( %s /\ t || P )' % AT
    satt = mkst(w, ATT)
    tsub = satt([satt([sat([d['sh']], 'adantr', SH)], 'adantr', SH),
                 satt([satt([tprm], 'adantr', 't e. Prime'),
                       satt([], 'simpr', 't || P')], 'jca', '( t e. Prime /\ t || P )'),
                 w.inst('vsubrp')], 'syl2anc', '( 1 - ( V ` t ) ) e. RR+')
    qtr = satt([satt([vtr], 'adantr', '( V ` t ) e. RR'), tsub], 'rerpdivcld',
               '%s e. RR' % QUOT('t'))
    cc1 = satt([satt([], 'iftrued', '%s = %s' % (BODYT, QUOT('t'))),
              satt([qtr], 'recnd', '%s e. CC' % QUOT('t'))], 'eqeltrd', '%s e. CC' % BODYT)
    ATF = '( %s /\ -. t || P )' % AT
    satf = mkst(w, ATF)
    cc2 = satf([satf([], 'iffalsed', '%s = 0' % BODYT),
                w.s([], '0cnd', '( %s -> 0 e. CC )' % ATF)], 'eqeltrd', '%s e. CC' % BODYT)
    ccT = sat([cc1, cc2], 'pm2.61dan', '%s e. CC' % BODYT)
    ral = st([ccT], 'ralrimiva', 'A. t e. Prime %s e. CC' % BODYT)
    gf = st([ral, st([w.s([hgfn], 'fmpt',
                          '( A. t e. Prime %s e. CC <-> %s : Prime --> CC )' % (BODYT, GFN))],
                     'a1i',
                     '( A. t e. Prime %s e. CC <-> %s : Prime --> CC )' % (BODYT, GFN))],
             'mpbid', '%s : Prime --> CC' % GFN)
    # ---- the master lemma
    master = st([st([dnn, gf], 'jca', '( D e. NN /\ %s : Prime --> CC )' % GFN),
                 w.inst('sqfdvdsum')], 'syl',
                'sum_ d e. %s prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 + ( %s ` p ) )'
                % (SD, PFQd, GFN, PFQD, GFN))
    # ---- SD = DV ( D )
    AX = '( %s /\ x e. NN )' % A
    sx = mkst(w, AX)
    AXD = '( %s /\ x || D )' % AX
    sxd = mkst(w, AXD)
    xsq = sxd([sxd([sxd([sxd([sx([dnn], 'adantr', 'D e. NN')], 'adantr', 'D e. NN'),
                        w.s([], 'simplr', '( %s -> x e. NN )' % AXD),
                        sxd([], 'simpr', 'x || D')], '3jca',
                       '( D e. NN /\ x e. NN /\ x || D )'), w.inst('dvdssqf')], 'syl',
                    '( ( mmu ` D ) =/= 0 -> ( mmu ` x ) =/= 0 )'),
               sxd([sx([dsq], 'adantr', '( mmu ` D ) =/= 0')], 'adantr',
                   '( mmu ` D ) =/= 0')], 'mpd', '( mmu ` x ) =/= 0')
    bi = sx([sx([sxd([xsq, sxd([], 'simpr', 'x || D')], 'jca',
                     '( ( mmu ` x ) =/= 0 /\ x || D )')], 'ex',
                '( x || D -> ( ( mmu ` x ) =/= 0 /\ x || D ) )'),
             sx([w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\ x || D ) -> x || D )')], 'a1i',
                '( ( ( mmu ` x ) =/= 0 /\ x || D ) -> x || D )')], 'impbid',
            '( x || D <-> ( ( mmu ` x ) =/= 0 /\ x || D ) )')
    sdeq = st([bi], 'rabbidva', '%s = %s' % (DVD, SD))
    # ---- the value of the function at a prime divisor of P
    hsub = w.s([w.s([], 'breq1', '( t = p -> ( t || P <-> p || P ) )'),
                w.s([w.s([], 'fveq2', '( t = p -> ( V ` t ) = ( V ` p ) )'),
                     w.s([w.s([], 'fveq2', '( t = p -> ( V ` t ) = ( V ` p ) )')], 'oveq2d',
                         '( t = p -> ( 1 - ( V ` t ) ) = ( 1 - ( V ` p ) ) )')], 'oveq12d',
                    '( t = p -> %s = %s )' % (QUOT('t'), QUOT('p')))], 'ifbieq1d',
               '( t = p -> %s = %s )' % (BODYT, BODYP))
    fvinst = w.s([hsub, hgfn], 'fvmptg',
                 '( ( p e. Prime /\ %s e. CC ) -> ( %s ` p ) = %s )' % (BODYP, GFN, BODYP))

    # ---- for d e. DV ( D ) the inner product is GT ( d )
    AD = '( %s /\ d e. %s )' % (A, DVD)
    sd = mkst(w, AD)
    eldD = w.s([w.s([], 'breq1', '( x = d -> ( x || D <-> d || D ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\ d || D ) )' % DVD)
    dc = sd([sd([eldD], 'a1i', '( d e. %s <-> ( d e. NN /\ d || D ) )' % DVD),
             sd([], 'simpr', 'd e. %s' % DVD)], 'mpbid', '( d e. NN /\ d || D )')
    dnn2 = sd([dc], 'simpld', 'd e. NN')
    ddD = sd([dc], 'simprd', 'd || D')
    ddP = sd([sd([sd([sd([dnn2], 'nnzd', 'd e. ZZ'), sd([dz], 'adantr', 'D e. ZZ'),
                      sd([pz], 'adantr', 'P e. ZZ')], '3jca',
                     '( d e. ZZ /\ D e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                  '( ( d || D /\ D || P ) -> d || P )'),
              sd([ddD, sd([ddp], 'adantr', 'D || P')], 'jca', '( d || D /\ D || P )')], 'mpd',
             'd || P')
    ADP = '( %s /\ p e. %s )' % (AD, PFQd)
    sdp = mkst(w, ADP)
    elpd = w.s([w.s([], 'breq1', '( q = p -> ( q || d <-> p || d ) )')], 'elrab',
               '( p e. %s <-> ( p e. Prime /\ p || d ) )' % PFQd)
    pcd = sdp([sdp([elpd], 'a1i', '( p e. %s <-> ( p e. Prime /\ p || d ) )' % PFQd),
               sdp([], 'simpr', 'p e. %s' % PFQd)], 'mpbid', '( p e. Prime /\ p || d )')
    pprm1 = sdp([pcd], 'simpld', 'p e. Prime')
    pdd = sdp([pcd], 'simprd', 'p || d')
    pdP1 = sdp([sdp([sdp([sdp([pprm1, w.inst('prmz')], 'syl', 'p e. ZZ'),
                          sdp([sd([dnn2], 'nnzd', 'd e. ZZ')], 'adantr', 'd e. ZZ'),
                          sdp([sd([pz], 'adantr', 'P e. ZZ')], 'adantr', 'P e. ZZ')], '3jca',
                         '( p e. ZZ /\ d e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                    '( ( p || d /\ d || P ) -> p || P )'),
                sdp([pdd, sdp([ddP], 'adantr', 'd || P')], 'jca',
                    '( p || d /\ d || P )')], 'mpd', 'p || P')
    sub1 = sdp([sdp([sd([d['sh']], 'adantr', SH)], 'adantr', SH),
                sdp([pprm1, pdP1], 'jca', '( p e. Prime /\ p || P )'), w.inst('vsubrp')],
               'syl2anc', '( 1 - ( V ` p ) ) e. RR+')
    vp1 = sdp([sdp([sdp([sd([d['vf']], 'adantr', 'V : NN --> RR')], 'adantr', 'V : NN --> RR'),
                    sdp([pprm1, w.inst('prmnn')], 'syl', 'p e. NN')], 'jca',
                   '( V : NN --> RR /\ p e. NN )'), w.inst('ffvelcdm')], 'syl',
               '( V ` p ) e. RR')
    q1 = sdp([sdp([vp1, sub1], 'rerpdivcld', '%s e. RR' % QUOT('p'))], 'recnd',
              '%s e. CC' % QUOT('p'))
    bp1 = sdp([sdp([pdP1], 'iftrued', '%s = %s' % (BODYP, QUOT('p'))), q1], 'eqeltrd',
              '%s e. CC' % BODYP)
    gfv1 = sdp([sdp([pprm1, bp1, fvinst], 'syl2anc', '( %s ` p ) = %s' % (GFN, BODYP)),
                sdp([pdP1], 'iftrued', '%s = %s' % (BODYP, QUOT('p')))], 'eqtrd',
               '( %s ` p ) = %s' % (GFN, QUOT('p')))
    prd1 = sd([sd([gfv1], 'prodeq2dv',
                  'prod_ p e. %s ( %s ` p ) = prod_ p e. %s %s' % (PFQd, GFN, PFQd, QUOT('p'))),
               sd([sd([w.s([], 'cbvrabv', '%s = %s' % (PFQd, PFRd))], 'a1i',
                      '%s = %s' % (PFQd, PFRd))], 'prodeq1d',
                  'prod_ p e. %s %s = prod_ p e. %s %s' % (PFQd, QUOT('p'), PFRd, QUOT('p')))],
              'eqtrd',
              'prod_ p e. %s ( %s ` p ) = prod_ p e. %s %s' % (PFQd, GFN, PFRd, QUOT('p')))
    gtd = sd([sd([d['sh']], 'adantr', SH), sd([dnn2, ddP], 'jca', '( d e. NN /\ d || P )'),
              w.inst('gtfprod')], 'syl2anc',
             '%s = prod_ p e. %s %s' % (GT('d'), PFRd, QUOT('p')))
    lterm = sd([prd1, sd([gtd], 'eqcomd',
                         'prod_ p e. %s %s = %s' % (PFRd, QUOT('p'), GT('d')))], 'eqtrd',
               'prod_ p e. %s ( %s ` p ) = %s' % (PFQd, GFN, GT('d')))
    lhs1 = st([sdeq], 'sumeq1d',
              'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s prod_ p e. %s ( %s ` p )'
              % (DVD, PFQd, GFN, SD, PFQd, GFN))
    lhs2 = st([lterm], 'sumeq2dv',
              'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s %s'
              % (DVD, PFQd, GFN, DVD, GT('d')))
    # ---- for p e. PF ( D ) : 1 + ( GFN ` p ) = 1 / ( 1 - ( V ` p ) )
    APD = '( %s /\ p e. %s )' % (A, PFQD)
    spd = mkst(w, APD)
    elpD = w.s([w.s([], 'breq1', '( q = p -> ( q || D <-> p || D ) )')], 'elrab',
               '( p e. %s <-> ( p e. Prime /\ p || D ) )' % PFQD)
    pcD = spd([spd([elpD], 'a1i', '( p e. %s <-> ( p e. Prime /\ p || D ) )' % PFQD),
               spd([], 'simpr', 'p e. %s' % PFQD)], 'mpbid', '( p e. Prime /\ p || D )')
    pprm2 = spd([pcD], 'simpld', 'p e. Prime')
    pdD = spd([pcD], 'simprd', 'p || D')
    pdP2 = spd([spd([spd([spd([pprm2, w.inst('prmz')], 'syl', 'p e. ZZ'),
                          spd([dz], 'adantr', 'D e. ZZ'),
                          spd([pz], 'adantr', 'P e. ZZ')], '3jca',
                         '( p e. ZZ /\ D e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                    '( ( p || D /\ D || P ) -> p || P )'),
                spd([pdD, spd([ddp], 'adantr', 'D || P')], 'jca',
                    '( p || D /\ D || P )')], 'mpd', 'p || P')
    sub2 = spd([spd([d['sh']], 'adantr', SH),
                spd([pprm2, pdP2], 'jca', '( p e. Prime /\ p || P )'), w.inst('vsubrp')],
               'syl2anc', '( 1 - ( V ` p ) ) e. RR+')
    vp2 = spd([spd([spd([d['vf']], 'adantr', 'V : NN --> RR'),
                    spd([pprm2, w.inst('prmnn')], 'syl', 'p e. NN')], 'jca',
                   '( V : NN --> RR /\ p e. NN )'), w.inst('ffvelcdm')], 'syl',
               '( V ` p ) e. RR')
    vpc2 = spd([vp2], 'recnd', '( V ` p ) e. CC')
    subc2 = spd([sub2], 'rpcnd', '( 1 - ( V ` p ) ) e. CC')
    subn2 = spd([sub2], 'rpne0d', '( 1 - ( V ` p ) ) =/= 0')
    q2 = spd([spd([vp2, sub2], 'rerpdivcld', '%s e. RR' % QUOT('p'))], 'recnd',
             '%s e. CC' % QUOT('p'))
    bp2 = spd([spd([pdP2], 'iftrued', '%s = %s' % (BODYP, QUOT('p'))), q2], 'eqeltrd',
              '%s e. CC' % BODYP)
    gfv2 = spd([spd([pprm2, bp2, fvinst], 'syl2anc', '( %s ` p ) = %s' % (GFN, BODYP)),
                spd([pdP2], 'iftrued', '%s = %s' % (BODYP, QUOT('p')))], 'eqtrd',
               '( %s ` p ) = %s' % (GFN, QUOT('p')))
    one = spd([spd([subc2, subn2], 'dividd',
                   '( ( 1 - ( V ` p ) ) / ( 1 - ( V ` p ) ) ) = 1')], 'eqcomd',
              '1 = ( ( 1 - ( V ` p ) ) / ( 1 - ( V ` p ) ) )')
    ddir = spd([subc2, vpc2, subc2, subn2], 'divdird',
               '( ( ( 1 - ( V ` p ) ) + ( V ` p ) ) / ( 1 - ( V ` p ) ) ) = '
               '( ( ( 1 - ( V ` p ) ) / ( 1 - ( V ` p ) ) ) + %s )' % QUOT('p'))
    nc = spd([spd([spd([w.s([], '1cnd', '( %s -> 1 e. CC )' % APD), vpc2], 'jca',
                       '( 1 e. CC /\ ( V ` p ) e. CC )'), w.inst('npcan')], 'syl',
                  '( ( 1 - ( V ` p ) ) + ( V ` p ) ) = 1')], 'oveq1d',
             '( ( ( 1 - ( V ` p ) ) + ( V ` p ) ) / ( 1 - ( V ` p ) ) ) = %s' % RECP('p'))
    onep = spd([spd([one], 'oveq1d',
                    '( 1 + %s ) = ( ( ( 1 - ( V ` p ) ) / ( 1 - ( V ` p ) ) ) + %s )'
                    % (QUOT('p'), QUOT('p'))),
                spd([spd([ddir], 'eqcomd',
                         '( ( ( 1 - ( V ` p ) ) / ( 1 - ( V ` p ) ) ) + %s ) = '
                         '( ( ( 1 - ( V ` p ) ) + ( V ` p ) ) / ( 1 - ( V ` p ) ) )'
                         % QUOT('p')), nc], 'eqtrd',
                    '( ( ( 1 - ( V ` p ) ) / ( 1 - ( V ` p ) ) ) + %s ) = %s'
                    % (QUOT('p'), RECP('p')))], 'eqtrd',
               '( 1 + %s ) = %s' % (QUOT('p'), RECP('p')))
    rterm = spd([spd([gfv2], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + %s )' % (GFN, QUOT('p'))),
                 onep], 'eqtrd', '( 1 + ( %s ` p ) ) = %s' % (GFN, RECP('p')))
    rhs1 = st([rterm], 'prodeq2dv',
              'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s %s' % (PFQD, GFN, PFQD, RECP('p')))
    rhs2 = st([st([w.s([], 'cbvrabv', '%s = %s' % (PFQD, PFRD))], 'a1i',
                  '%s = %s' % (PFQD, PFRD))], 'prodeq1d',
              'prod_ p e. %s %s = prod_ p e. %s %s' % (PFQD, RECP('p'), PFRD, RECP('p')))
    rhs3 = st([w.s([], 'cbvprodv',
                   'prod_ p e. %s %s = %s' % (PFRD, RECP('p'), PRD))], 'a1i',
              'prod_ p e. %s %s = %s' % (PFRD, RECP('p'), PRD))
    rhs = st([st([rhs1, rhs2], 'eqtrd',
                 'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s %s'
                 % (PFQD, GFN, PFRD, RECP('p'))), rhs3], 'eqtrd',
             'prod_ p e. %s ( 1 + ( %s ` p ) ) = %s' % (PFQD, GFN, PRD))
    # ---- the target form
    vdc = st([st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\ D || P )'), w.inst('vdrp')],
                 'syl2anc', '( V ` D ) e. RR+')], 'rpcnd', '( V ` D ) e. CC')
    vdne = st([st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\ D || P )'), w.inst('vdrp')],
                  'syl2anc', '( V ` D ) e. RR+')], 'rpne0d', '( V ` D ) =/= 0')
    finD = st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), PFRD))], 'a1i',
                  '%s = %s' % (PF('D', 'p'), PFRD)),
               st([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))], 'eqeltrrd',
              '%s e. Fin' % PFRD)
    AQD = '( %s /\ q e. %s )' % (A, PFRD)
    sqd = mkst(w, AQD)
    elqD = w.s([w.s([], 'breq1', '( r = q -> ( r || D <-> q || D ) )')], 'elrab',
               '( q e. %s <-> ( q e. Prime /\ q || D ) )' % PFRD)
    qcD = sqd([sqd([elqD], 'a1i', '( q e. %s <-> ( q e. Prime /\ q || D ) )' % PFRD),
               sqd([], 'simpr', 'q e. %s' % PFRD)], 'mpbid', '( q e. Prime /\ q || D )')
    qprm = sqd([qcD], 'simpld', 'q e. Prime')
    qdD = sqd([qcD], 'simprd', 'q || D')
    qdP = sqd([sqd([sqd([sqd([qprm, w.inst('prmz')], 'syl', 'q e. ZZ'),
                         sqd([dz], 'adantr', 'D e. ZZ'), sqd([pz], 'adantr', 'P e. ZZ')], '3jca',
                        '( q e. ZZ /\ D e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                   '( ( q || D /\ D || P ) -> q || P )'),
               sqd([qdD, sqd([ddp], 'adantr', 'D || P')], 'jca',
                   '( q || D /\ D || P )')], 'mpd', 'q || P')
    bodyc = sqd([sqd([sqd([sqd([d['sh']], 'adantr', SH),
                           sqd([qprm, qdP], 'jca', '( q e. Prime /\ q || P )'),
                           w.inst('vsubrp')], 'syl2anc',
                          '( 1 - ( V ` q ) ) e. RR+')], 'rpreccld', '%s e. RR+' % BODY)],
                'rpcnd', '%s e. CC' % BODY)
    prdc = st([finD, bodyc], 'fprodcl', '%s e. CC' % PRD)
    recdc = st([st([vdc, vdne], 'jca', '( ( V ` D ) e. CC /\ ( V ` D ) =/= 0 )'),
                w.inst('reccl')], 'syl', '( 1 / ( V ` D ) ) e. CC')
    e1 = st([st([recdc, vdc, prdc], 'mulassd',
                '( ( ( 1 / ( V ` D ) ) x. ( V ` D ) ) x. %s ) = '
                '( ( 1 / ( V ` D ) ) x. ( ( V ` D ) x. %s ) )' % (PRD, PRD))], 'eqcomd',
             '( ( 1 / ( V ` D ) ) x. ( ( V ` D ) x. %s ) ) = '
             '( ( ( 1 / ( V ` D ) ) x. ( V ` D ) ) x. %s )' % (PRD, PRD))
    e2 = st([st([st([st([vdc, vdne], 'jca', '( ( V ` D ) e. CC /\ ( V ` D ) =/= 0 )'),
                 w.inst('recid2')], 'syl', '( ( 1 / ( V ` D ) ) x. ( V ` D ) ) = 1')], 'oveq1d',
                '( ( ( 1 / ( V ` D ) ) x. ( V ` D ) ) x. %s ) = ( 1 x. %s )' % (PRD, PRD)),
             st([prdc], 'mullidd', '( 1 x. %s ) = %s' % (PRD, PRD))], 'eqtrd',
            '( ( ( 1 / ( V ` D ) ) x. ( V ` D ) ) x. %s ) = %s' % (PRD, PRD))
    alg = st([e1, e2], 'eqtrd', '( ( 1 / ( V ` D ) ) x. %s ) = %s' % (GT('D'), PRD))
    w.qed([st([st([lhs2], 'eqcomd',
                  'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s ( %s ` p )'
                  % (DVD, GT('d'), DVD, PFQd, GFN)),
               st([lhs1, master], 'eqtrd',
                  'sum_ d e. %s prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 + ( %s ` p ) )'
                  % (DVD, PFQd, GFN, PFQD, GFN))], 'eqtrd',
              'sum_ d e. %s %s = prod_ p e. %s ( 1 + ( %s ` p ) )' % (DVD, GT('d'), PFQD, GFN)),
           st([rhs, st([alg], 'eqcomd',
                       '%s = ( ( 1 / ( V ` D ) ) x. %s )' % (PRD, GT('D')))], 'eqtrd',
              'prod_ p e. %s ( 1 + ( %s ` p ) ) = ( ( 1 / ( V ` D ) ) x. %s )'
              % (PFQD, GFN, GT('D')))], 'eqtrd',
          '( %s -> sum_ d e. %s %s = ( ( 1 / ( V ` D ) ) x. %s ) )' % (A, DVD, GT('d'), GT('D')))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['vsubrp']:
        globals()[f]().run()
