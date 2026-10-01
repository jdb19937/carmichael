"""Sortie v2c: the reciprocal Selberg terms and their divisor sum.

gtfprodi   1 / GT ( K ) as a product over the prime divisors of K
gtsuminv   sum over the divisors of D of 1 / GT ( d ) is 1 / ( V ` D )
gtsinv2    the same with the range DV ( P ) and an indicator
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2c_lib import *
from cl import lift


def gtfprodi():
    w = W('gtfprodi', 'The reciprocal Selberg term as a product over the prime divisors.')
    A = '( %s /\\ ( K e. NN /\\ K || P ) )' % SH
    TR = PF('K')
    d = shsteps(w, A, (SH,))
    st = d['st']
    knn = st([], 'simprl', 'K e. NN')
    kdp = st([], 'simprr', 'K || P')
    kz = st([knn], 'nnzd', 'K e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    fin = st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('K', 'p'), TR))], 'a1i',
                 '%s = %s' % (PF('K', 'p'), TR)),
              st([knn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('K', 'p'))], 'eqeltrrd',
             '%s e. Fin' % TR)
    gk = st([d['sh'], st([knn, kdp], 'jca', '( K e. NN /\\ K || P )'), w.inst('gtfprod')],
            'syl2anc', '%s = prod_ p e. %s %s' % (GT('K'), TR, QUOT('p')))
    # ---- facts for a prime divisor p of K
    AP = '( %s /\\ p e. %s )' % (A, TR)
    pf = pdivp(w, A, AP, 'p', 'K', d['sh'], kz, kdp, pz, d['vf'])
    sp = pf['st']
    qrp = sp([pf['vrp'], pf['subrp']], 'rpdivcld', '%s e. RR+' % QUOT('p'))
    qc = sp([qrp], 'rpcnd', '%s e. CC' % QUOT('p'))
    qne = sp([qrp], 'rpne0d', '%s =/= 0' % QUOT('p'))
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % AP)
    rec = sp([sp([pf['vrp']], 'rpcnd', '( V ` p ) e. CC'),
              sp([pf['subrp']], 'rpcnd', '( 1 - ( V ` p ) ) e. CC'),
              sp([pf['vrp']], 'rpne0d', '( V ` p ) =/= 0'),
              sp([pf['subrp']], 'rpne0d', '( 1 - ( V ` p ) ) =/= 0')], 'recdivd',
             '( 1 / %s ) = %s' % (QUOT('p'), IQUOT('p')))
    # ---- prod of reciprocals
    dv = st([fin, one, qc, qne], 'fproddiv',
            'prod_ p e. %s ( 1 / %s ) = ( prod_ p e. %s 1 / prod_ p e. %s %s )'
            % (TR, QUOT('p'), TR, TR, QUOT('p')))
    p1 = st([st([fin], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (TR, TR)),
             w.inst('prod1')], 'syl', 'prod_ p e. %s 1 = 1' % TR)
    peq = st([rec], 'prodeq2dv',
             'prod_ p e. %s ( 1 / %s ) = prod_ p e. %s %s' % (TR, QUOT('p'), TR, IQUOT('p')))
    rhs = st([dv, st([p1], 'oveq1d',
                     '( prod_ p e. %s 1 / prod_ p e. %s %s ) = ( 1 / prod_ p e. %s %s )'
                     % (TR, TR, QUOT('p'), TR, QUOT('p')))], 'eqtrd',
             'prod_ p e. %s ( 1 / %s ) = ( 1 / prod_ p e. %s %s )' % (TR, QUOT('p'), TR, QUOT('p')))
    w.qed([st([gk], 'oveq2d', '%s = ( 1 / prod_ p e. %s %s )' % (IGT('K'), TR, QUOT('p'))),
           st([peq, rhs], 'eqtr3d',
              'prod_ p e. %s %s = ( 1 / prod_ p e. %s %s )' % (TR, IQUOT('p'), TR, QUOT('p')))],
          'eqtr4d', '( %s -> %s = prod_ p e. %s %s )' % (A, IGT('K'), TR, IQUOT('p')))
    return w




BODYT = 'if ( t || P , %s , 0 )' % IQUOT('t')
BODYP = 'if ( p || P , %s , 0 )' % IQUOT('p')
GFN = '( t e. Prime |-> %s )' % BODYT


def gtsuminv():
    w = W('gtsuminv', 'The sum of the reciprocal Selberg terms over the divisors of D is the '
                      'reciprocal of the density at D.')
    A = '( %s /\\ ( D e. NN /\\ D || P ) )' % SH
    DVD = DV('D')
    SD = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || D ) }'
    PFQd, PFRd = PF('d', 'q'), PF('d', 'r')
    PFQD, PFRD = PF('D', 'q'), PF('D', 'r')
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simprl', 'D e. NN')
    ddp = st([], 'simprr', 'D || P')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    dsq = st([st([st([d['pnn'], dnn, ddp], '3jca', '( P e. NN /\\ D e. NN /\\ D || P )'),
                  w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` D ) =/= 0 )'),
              d['psqf']], 'mpd', '( mmu ` D ) =/= 0')
    hgfn = w.s([], 'eqid', '%s = %s' % (GFN, GFN))
    # ---- GFN : Prime --> CC
    AT = '( %s /\\ t e. Prime )' % A
    sat = mkst(w, AT)
    tprm = w.s([], 'simpr', '( %s -> t e. Prime )' % AT)
    ATT = '( %s /\\ t || P )' % AT
    satt = mkst(w, ATT)
    tvrp = satt([lift(w, d['sh'], ATT),
                 satt([satt([satt([tprm], 'adantr', 't e. Prime'), w.inst('prmnn')], 'syl',
                            't e. NN'), satt([], 'simpr', 't || P')], 'jca',
                      '( t e. NN /\\ t || P )'), w.inst('vdrp')], 'syl2anc', '( V ` t ) e. RR+')
    tsub = satt([lift(w, d['sh'], ATT),
                 satt([satt([tprm], 'adantr', 't e. Prime'),
                       satt([], 'simpr', 't || P')], 'jca', '( t e. Prime /\\ t || P )'),
                 w.inst('vsubrp')], 'syl2anc', '( 1 - ( V ` t ) ) e. RR+')
    cc1 = satt([satt([], 'iftrued', '%s = %s' % (BODYT, IQUOT('t'))),
                satt([satt([tsub, tvrp], 'rpdivcld', '%s e. RR+' % IQUOT('t'))], 'rpcnd',
                     '%s e. CC' % IQUOT('t'))], 'eqeltrd', '%s e. CC' % BODYT)
    ATF = '( %s /\\ -. t || P )' % AT
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
    master = st([st([dnn, gf], 'jca', '( D e. NN /\\ %s : Prime --> CC )' % GFN),
                 w.inst('sqfdvdsum')], 'syl',
                'sum_ d e. %s prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 + ( %s ` p ) )'
                % (SD, PFQd, GFN, PFQD, GFN))
    # ---- SD = DV ( D )
    AX = '( %s /\\ x e. NN )' % A
    sx = mkst(w, AX)
    AXD = '( %s /\\ x || D )' % AX
    sxd = mkst(w, AXD)
    xsq = sxd([sxd([sxd([lift(w, dnn, AXD),
                         w.s([], 'simplr', '( %s -> x e. NN )' % AXD),
                         sxd([], 'simpr', 'x || D')], '3jca',
                        '( D e. NN /\\ x e. NN /\\ x || D )'), w.inst('dvdssqf')], 'syl',
                    '( ( mmu ` D ) =/= 0 -> ( mmu ` x ) =/= 0 )'),
               lift(w, dsq, AXD)], 'mpd', '( mmu ` x ) =/= 0')
    bi = sx([sx([sxd([xsq, sxd([], 'simpr', 'x || D')], 'jca',
                     '( ( mmu ` x ) =/= 0 /\\ x || D )')], 'ex',
                '( x || D -> ( ( mmu ` x ) =/= 0 /\\ x || D ) )'),
             sx([w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || D ) -> x || D )')], 'a1i',
                '( ( ( mmu ` x ) =/= 0 /\\ x || D ) -> x || D )')], 'impbid',
            '( x || D <-> ( ( mmu ` x ) =/= 0 /\\ x || D ) )')
    sdeq = st([bi], 'rabbidva', '%s = %s' % (DVD, SD))
    # ---- the value of GFN at a prime
    hsub = w.s([w.s([], 'breq1', '( t = p -> ( t || P <-> p || P ) )'),
                w.s([w.s([w.s([], 'fveq2', '( t = p -> ( V ` t ) = ( V ` p ) )')], 'oveq2d',
                         '( t = p -> ( 1 - ( V ` t ) ) = ( 1 - ( V ` p ) ) )'),
                     w.s([], 'fveq2', '( t = p -> ( V ` t ) = ( V ` p ) )')], 'oveq12d',
                    '( t = p -> %s = %s )' % (IQUOT('t'), IQUOT('p')))], 'ifbieq1d',
               '( t = p -> %s = %s )' % (BODYT, BODYP))
    fvinst = w.s([hsub, hgfn], 'fvmptg',
                 '( ( p e. Prime /\\ %s e. CC ) -> ( %s ` p ) = %s )' % (BODYP, GFN, BODYP))
    # ---- the summand for d e. DV ( D )
    AD = '( %s /\\ d e. %s )' % (A, DVD)
    dd = dvdfacts(w, A, AD, 'd', 'D', d['sh'], dz, ddp, pz)
    sd = dd['st']
    ADP = '( %s /\\ p e. %s )' % (AD, PFQd)
    sdp = mkst(w, ADP)
    elpd = w.s([w.s([], 'breq1', '( q = p -> ( q || d <-> p || d ) )')], 'elrab',
               '( p e. %s <-> ( p e. Prime /\\ p || d ) )' % PFQd)
    pcd = sdp([sdp([elpd], 'a1i', '( p e. %s <-> ( p e. Prime /\\ p || d ) )' % PFQd),
               sdp([], 'simpr', 'p e. %s' % PFQd)], 'mpbid', '( p e. Prime /\\ p || d )')
    pprm1 = sdp([pcd], 'simpld', 'p e. Prime')
    pdd = sdp([pcd], 'simprd', 'p || d')
    pdP1 = sdp([sdp([sdp([sdp([pprm1, w.inst('prmz')], 'syl', 'p e. ZZ'),
                          lift(w, dd['z'], ADP), lift(w, pz, ADP)], '3jca',
                         '( p e. ZZ /\\ d e. ZZ /\\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                    '( ( p || d /\\ d || P ) -> p || P )'),
                sdp([pdd, lift(w, dd['dP'], ADP)], 'jca', '( p || d /\\ d || P )')], 'mpd',
               'p || P')
    vp1 = sdp([lift(w, d['sh'], ADP), sdp([sdp([pprm1, w.inst('prmnn')], 'syl', 'p e. NN'),
                                           pdP1], 'jca', '( p e. NN /\\ p || P )'),
               w.inst('vdrp')], 'syl2anc', '( V ` p ) e. RR+')
    sub1 = sdp([lift(w, d['sh'], ADP), sdp([pprm1, pdP1], 'jca', '( p e. Prime /\\ p || P )'),
                w.inst('vsubrp')], 'syl2anc', '( 1 - ( V ` p ) ) e. RR+')
    i1 = sdp([sdp([sub1, vp1], 'rpdivcld', '%s e. RR+' % IQUOT('p'))], 'rpcnd',
             '%s e. CC' % IQUOT('p'))
    bp1 = sdp([sdp([pdP1], 'iftrued', '%s = %s' % (BODYP, IQUOT('p'))), i1], 'eqeltrd',
              '%s e. CC' % BODYP)
    gfv1 = sdp([sdp([pprm1, bp1, fvinst], 'syl2anc', '( %s ` p ) = %s' % (GFN, BODYP)),
                sdp([pdP1], 'iftrued', '%s = %s' % (BODYP, IQUOT('p')))], 'eqtrd',
               '( %s ` p ) = %s' % (GFN, IQUOT('p')))
    prd1 = sd([sd([gfv1], 'prodeq2dv',
                  'prod_ p e. %s ( %s ` p ) = prod_ p e. %s %s' % (PFQd, GFN, PFQd, IQUOT('p'))),
               sd([sd([w.s([], 'cbvrabv', '%s = %s' % (PFQd, PFRd))], 'a1i',
                      '%s = %s' % (PFQd, PFRd))], 'prodeq1d',
                  'prod_ p e. %s %s = prod_ p e. %s %s' % (PFQd, IQUOT('p'), PFRd, IQUOT('p')))],
              'eqtrd',
              'prod_ p e. %s ( %s ` p ) = prod_ p e. %s %s' % (PFQd, GFN, PFRd, IQUOT('p')))
    gtd = sd([lift(w, d['sh'], AD), sd([dd['nn'], dd['dP']], 'jca', '( d e. NN /\\ d || P )'),
              w.inst('gtfprodi')], 'syl2anc',
             '%s = prod_ p e. %s %s' % (IGT('d'), PFRd, IQUOT('p')))
    lterm = sd([prd1, sd([gtd], 'eqcomd',
                         'prod_ p e. %s %s = %s' % (PFRd, IQUOT('p'), IGT('d')))], 'eqtrd',
               'prod_ p e. %s ( %s ` p ) = %s' % (PFQd, GFN, IGT('d')))
    lhs1 = st([sdeq], 'sumeq1d',
              'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s prod_ p e. %s ( %s ` p )'
              % (DVD, PFQd, GFN, SD, PFQd, GFN))
    lhs2 = st([lterm], 'sumeq2dv',
              'sum_ d e. %s prod_ p e. %s ( %s ` p ) = sum_ d e. %s %s'
              % (DVD, PFQd, GFN, DVD, IGT('d')))
    # ---- the factor for p e. PF ( D )
    APD = '( %s /\\ p e. %s )' % (A, PFQD)
    spd = mkst(w, APD)
    elpD = w.s([w.s([], 'breq1', '( q = p -> ( q || D <-> p || D ) )')], 'elrab',
               '( p e. %s <-> ( p e. Prime /\\ p || D ) )' % PFQD)
    pcD = spd([spd([elpD], 'a1i', '( p e. %s <-> ( p e. Prime /\\ p || D ) )' % PFQD),
               spd([], 'simpr', 'p e. %s' % PFQD)], 'mpbid', '( p e. Prime /\\ p || D )')
    pprm2 = spd([pcD], 'simpld', 'p e. Prime')
    pdD = spd([pcD], 'simprd', 'p || D')
    pdP2 = spd([spd([spd([spd([pprm2, w.inst('prmz')], 'syl', 'p e. ZZ'),
                          lift(w, dz, APD), lift(w, pz, APD)], '3jca',
                         '( p e. ZZ /\\ D e. ZZ /\\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                    '( ( p || D /\\ D || P ) -> p || P )'),
                spd([pdD, lift(w, ddp, APD)], 'jca', '( p || D /\\ D || P )')], 'mpd', 'p || P')
    vp2 = spd([lift(w, d['sh'], APD),
               spd([spd([pprm2, w.inst('prmnn')], 'syl', 'p e. NN'), pdP2], 'jca',
                   '( p e. NN /\\ p || P )'), w.inst('vdrp')], 'syl2anc', '( V ` p ) e. RR+')
    sub2 = spd([lift(w, d['sh'], APD), spd([pprm2, pdP2], 'jca', '( p e. Prime /\\ p || P )'),
                w.inst('vsubrp')], 'syl2anc', '( 1 - ( V ` p ) ) e. RR+')
    vpc2 = spd([vp2], 'rpcnd', '( V ` p ) e. CC')
    vpn2 = spd([vp2], 'rpne0d', '( V ` p ) =/= 0')
    subc2 = spd([sub2], 'rpcnd', '( 1 - ( V ` p ) ) e. CC')
    i2 = spd([spd([sub2, vp2], 'rpdivcld', '%s e. RR+' % IQUOT('p'))], 'rpcnd',
             '%s e. CC' % IQUOT('p'))
    bp2 = spd([spd([pdP2], 'iftrued', '%s = %s' % (BODYP, IQUOT('p'))), i2], 'eqeltrd',
              '%s e. CC' % BODYP)
    gfv2 = spd([spd([pprm2, bp2, fvinst], 'syl2anc', '( %s ` p ) = %s' % (GFN, BODYP)),
                spd([pdP2], 'iftrued', '%s = %s' % (BODYP, IQUOT('p')))], 'eqtrd',
               '( %s ` p ) = %s' % (GFN, IQUOT('p')))
    one = spd([spd([vpc2, vpn2], 'dividd', '( ( V ` p ) / ( V ` p ) ) = 1')], 'eqcomd',
              '1 = ( ( V ` p ) / ( V ` p ) )')
    ddir = spd([vpc2, subc2, vpc2, vpn2], 'divdird',
               '( ( ( V ` p ) + ( 1 - ( V ` p ) ) ) / ( V ` p ) ) = '
               '( ( ( V ` p ) / ( V ` p ) ) + %s )' % IQUOT('p'))
    nc = spd([spd([spd([vpc2, w.s([], '1cnd', '( %s -> 1 e. CC )' % APD)], 'jca',
                       '( ( V ` p ) e. CC /\\ 1 e. CC )'), w.inst('pncan3')], 'syl',
                  '( ( V ` p ) + ( 1 - ( V ` p ) ) ) = 1')], 'oveq1d',
             '( ( ( V ` p ) + ( 1 - ( V ` p ) ) ) / ( V ` p ) ) = ( 1 / ( V ` p ) )')
    onep = spd([spd([one], 'oveq1d',
                    '( 1 + %s ) = ( ( ( V ` p ) / ( V ` p ) ) + %s )' % (IQUOT('p'), IQUOT('p'))),
                spd([spd([ddir], 'eqcomd',
                         '( ( ( V ` p ) / ( V ` p ) ) + %s ) = '
                         '( ( ( V ` p ) + ( 1 - ( V ` p ) ) ) / ( V ` p ) )' % IQUOT('p')),
                     nc], 'eqtrd',
                    '( ( ( V ` p ) / ( V ` p ) ) + %s ) = ( 1 / ( V ` p ) )' % IQUOT('p'))],
               'eqtrd', '( 1 + %s ) = ( 1 / ( V ` p ) )' % IQUOT('p'))
    rterm = spd([spd([gfv2], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + %s )' % (GFN, IQUOT('p'))),
                 onep], 'eqtrd', '( 1 + ( %s ` p ) ) = ( 1 / ( V ` p ) )' % GFN)
    rhs1 = st([rterm], 'prodeq2dv',
              'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s ( 1 / ( V ` p ) )'
              % (PFQD, GFN, PFQD))
    rhs2 = st([st([w.s([], 'cbvrabv', '%s = %s' % (PFQD, PFRD))], 'a1i',
                  '%s = %s' % (PFQD, PFRD))], 'prodeq1d',
              'prod_ p e. %s ( 1 / ( V ` p ) ) = prod_ p e. %s ( 1 / ( V ` p ) )'
              % (PFQD, PFRD))
    # ---- prod_ p e. PF ( D ) ( 1 / ( V ` p ) ) = 1 / ( V ` D )
    finD = st([st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), PFRD))], 'a1i',
                  '%s = %s' % (PF('D', 'p'), PFRD)),
               st([dnn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))], 'eqeltrrd',
              '%s e. Fin' % PFRD)
    APR = '( %s /\\ p e. %s )' % (A, PFRD)
    pf = pdivp(w, A, APR, 'p', 'D', d['sh'], dz, ddp, pz, d['vf'])
    spr = pf['st']
    dvD = st([finD, w.s([], '1cnd', '( %s -> 1 e. CC )' % APR),
              spr([pf['vrp']], 'rpcnd', '( V ` p ) e. CC'),
              spr([pf['vrp']], 'rpne0d', '( V ` p ) =/= 0')], 'fproddiv',
             'prod_ p e. %s ( 1 / ( V ` p ) ) = ( prod_ p e. %s 1 / prod_ p e. %s ( V ` p ) )'
             % (PFRD, PFRD, PFRD))
    p1D = st([st([finD], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (PFRD, PFRD)),
              w.inst('prod1')], 'syl', 'prod_ p e. %s 1 = 1' % PFRD)
    vD = st([d['vh'], st([dnn, dsq], 'jca', '( D e. NN /\\ ( mmu ` D ) =/= 0 )'),
             w.inst('vsqfprod')], 'syl2anc', '( V ` D ) = prod_ p e. %s ( V ` p )' % PFRD)
    rhs3 = st([dvD, st([p1D, st([vD], 'eqcomd', 'prod_ p e. %s ( V ` p ) = ( V ` D )' % PFRD)],
                       'oveq12d',
                       '( prod_ p e. %s 1 / prod_ p e. %s ( V ` p ) ) = ( 1 / ( V ` D ) )'
                       % (PFRD, PFRD))], 'eqtrd',
              'prod_ p e. %s ( 1 / ( V ` p ) ) = ( 1 / ( V ` D ) )' % PFRD)
    rhs = st([st([rhs1, rhs2], 'eqtrd',
                 'prod_ p e. %s ( 1 + ( %s ` p ) ) = prod_ p e. %s ( 1 / ( V ` p ) )'
                 % (PFQD, GFN, PFRD)), rhs3], 'eqtrd',
             'prod_ p e. %s ( 1 + ( %s ` p ) ) = ( 1 / ( V ` D ) )' % (PFQD, GFN))
    w.qed([st([st([lhs2], 'eqcomd',
                  'sum_ d e. %s %s = sum_ d e. %s prod_ p e. %s ( %s ` p )'
                  % (DVD, IGT('d'), DVD, PFQd, GFN)),
               st([lhs1, master], 'eqtrd',
                  'sum_ d e. %s prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 1 + ( %s ` p ) )'
                  % (DVD, PFQd, GFN, PFQD, GFN))], 'eqtrd',
              'sum_ d e. %s %s = prod_ p e. %s ( 1 + ( %s ` p ) )' % (DVD, IGT('d'), PFQD, GFN)),
           rhs], 'eqtrd',
          '( %s -> sum_ d e. %s %s = ( 1 / ( V ` D ) ) )' % (A, DVD, IGT('d')))
    return w


IFB = 'if ( d || D , %s , 0 )' % IGT('d')


def gtsinv2():
    w = W('gtsinv2', 'The sum of the reciprocal Selberg terms over the divisors of P that divide '
                     'D is the reciprocal of the density at D.')
    A = '( %s /\\ ( D e. NN /\\ D || P ) )' % SH
    DVD, DVP = DV('D'), DV('P')
    d = shsteps(w, A, (SH,))
    st = d['st']
    dnn = st([], 'simprl', 'D e. NN')
    ddp = st([], 'simprr', 'D || P')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    pz = st([d['pnn']], 'nnzd', 'P e. ZZ')
    # ---- DV ( D ) C_ DV ( P )
    AX = '( %s /\\ x e. NN )' % A
    sx = mkst(w, AX)
    imp = sx([sx([sx([w.s([], 'simpr', '( %s -> x e. NN )' % AX)], 'nnzd', 'x e. ZZ'),
                  lift(w, dz, AX), lift(w, pz, AX)], '3jca',
                 '( x e. ZZ /\\ D e. ZZ /\\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
             '( ( x || D /\\ D || P ) -> x || P )')
    imp2 = w.s([lift(w, ddp, AX), imp], 'mpan2d', '( %s -> ( x || D -> x || P ) )' % AX)
    sub = w.s([imp2], 'ss2rabdv', '( %s -> %s C_ %s )' % (A, DVD, DVP))
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    # ---- the body on DV ( D )
    AD = '( %s /\\ d e. %s )' % (A, DVD)
    dd = dvdfacts(w, A, AD, 'd', 'D', d['sh'], dz, ddp, pz)
    sd = dd['st']
    gtrpd = sd([lift(w, d['sh'], AD), sd([dd['nn'], dd['dP']], 'jca', '( d e. NN /\\ d || P )'),
                w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('d'))
    igtc = sd([sd([gtrpd], 'rpreccld', '%s e. RR+' % IGT('d'))], 'rpcnd', '%s e. CC' % IGT('d'))
    btrue = sd([dd['dD']], 'iftrued', '%s = %s' % (IFB, IGT('d')))
    bcc = sd([btrue, igtc], 'eqeltrd', '%s e. CC' % IFB)
    # ---- the body vanishes off DV ( D )
    AE = '( %s /\\ d e. ( %s \\ %s ) )' % (A, DVP, DVD)
    se = mkst(w, AE)
    eldp = se([se([], 'simpr', 'd e. ( %s \\ %s )' % (DVP, DVD)), w.inst('eldifi')], 'syl',
              'd e. %s' % DVP)
    notd = se([se([], 'simpr', 'd e. ( %s \\ %s )' % (DVP, DVD)), w.inst('eldifn')], 'syl',
              '-. d e. %s' % DVD)
    eldD = w.s([w.s([], 'breq1', '( x = d -> ( x || D <-> d || D ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\\ d || D ) )' % DVD)
    dnn2 = se([eldp, w.inst('elrabi')], 'syl', 'd e. NN')
    bi2 = se([se([eldD], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || D ) )' % DVD),
              se([dnn2], 'biantrurd', '( d || D <-> ( d e. NN /\\ d || D ) )')], 'bitr4d',
             '( d e. %s <-> d || D )' % DVD)
    nd = se([notd, bi2], 'mtbid', '-. d || D')
    bz = se([nd], 'iffalsed', '%s = 0' % IFB)
    # ---- assemble
    ssq = w.s([sub, bcc, bz, finP], 'fsumss',
              '( %s -> sum_ d e. %s %s = sum_ d e. %s %s )' % (A, DVD, IFB, DVP, IFB))
    inner = st([btrue], 'sumeq2dv',
               'sum_ d e. %s %s = sum_ d e. %s %s' % (DVD, IFB, DVD, IGT('d')))
    gs = st([d['sh'], st([dnn, ddp], 'jca', '( D e. NN /\\ D || P )'), w.inst('gtsuminv')],
            'syl2anc', 'sum_ d e. %s %s = ( 1 / ( V ` D ) )' % (DVD, IGT('d')))
    w.qed([st([ssq], 'eqcomd',
              'sum_ d e. %s %s = sum_ d e. %s %s' % (DVP, IFB, DVD, IFB)),
           st([inner, gs], 'eqtrd', 'sum_ d e. %s %s = ( 1 / ( V ` D ) )' % (DVD, IFB))],
          'eqtrd', '( %s -> sum_ d e. %s %s = ( 1 / ( V ` D ) ) )' % (A, DVP, IFB))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['gtfprodi']:
        globals()[f]().run()
