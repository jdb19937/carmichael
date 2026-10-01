"""Sortie v4a: the remainder of the twin sieve."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import QF, RT, mkst
from cl import lift
from v4a_tb import SH, SH2, SHP, SHV, SHV3, SHVM, SHVP, TMR, TRAL, TB, shparts
from v4a_c import TC, AAS, WWS

RTD = RT('D')
PFQD = '{ q e. Prime | q || D }'
PFRD = '{ r e. Prime | r || D }'
OMD = '( # ` %s )' % PFQD
TDV = '( T / D )'
MSD = 'sum_ n e. A if ( D || n , ( W ` n ) , 0 )'
RMD = '( %s - ( ( V ` D ) x. X ) )' % MSD
CNTR = '( # ` { x e. ( 1 ... T ) | ( x mod D ) = r } )'
ARM = '( %s /\\ ( D e. NN /\\ D || P ) )' % TC


def twinrem():
    w = WS('twinrem', 'The remainder of the twin sieve at a divisor of the sifting product is '
                      'at most that divisor in absolute value.')
    st = mkst(w, ARM)
    tc = st([], 'simpl', TC)
    tb = st([tc], 'simpld', TB)
    rest = st([tc], 'simprd',
              '( ( T e. NN0 /\\ X = T ) /\\ ( A = %s /\\ W = %s ) )' % (AAS, WWS))
    shst = st([tb], 'simp1d', SH)
    sh = shparts(w, st, shst)
    mnn = st([st([tb], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    tn0 = st([st([rest], 'simpld', '( T e. NN0 /\\ X = T )')], 'simpld', 'T e. NN0')
    xeq = st([st([rest], 'simpld', '( T e. NN0 /\\ X = T )')], 'simprd', 'X = T')
    pnn = sh['pnn']
    psqf = sh['psqf']
    vf = sh['vf']
    v1 = st([st([st([shst], 'simprd', SH2)], 'simprd', SHV)], 'simp2d', '( V ` 1 ) = 1')
    vmul = st([st([st([st([shst], 'simprd', SH2)], 'simprd', SHV)], 'simp3d', SHV3)],
              'simpld', SHVM)
    dpair = st([], 'simpr', '( D e. NN /\\ D || P )')
    dnn = st([dpair], 'simpld', 'D e. NN')
    ddp = st([dpair], 'simprd', 'D || P')
    dz = st([dnn], 'nnzd', 'D e. ZZ')
    drp = st([dnn], 'nnrpd', 'D e. RR+')
    dre = st([drp], 'rpred', 'D e. RR')
    tre = st([tn0], 'nn0red', 'T e. RR')
    dsqf = st([st([st([pnn, dnn, ddp], '3jca', '( P e. NN /\\ D e. NN /\\ D || P )'),
                   w.inst('dvdssqf')], 'syl',
                  '( ( mmu ` P ) =/= 0 -> ( mmu ` D ) =/= 0 )'), psqf], 'mpd',
              '( mmu ` D ) =/= 0')
    # the primes of D do not divide M
    APR = '( %s /\\ r e. Prime )' % ARM
    spr = mkst(w, APR)
    rprm = spr([], 'simpr', 'r e. Prime')
    rz = spr([spr([rprm, w.inst('prmnn')], 'syl', 'r e. NN')], 'nnzd', 'r e. ZZ')
    APRD = '( %s /\\ r || D )' % APR
    sprd = mkst(w, APRD)
    rdp = sprd([sprd([sprd([lift(w, rz, APRD), lift(w, dz, APRD), lift(w, sprd([lift(w, pnn, APRD)], 'nnzd', 'P e. ZZ'), APRD)], '3jca',
                           '( r e. ZZ /\\ D e. ZZ /\\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                      '( ( r || D /\\ D || P ) -> r || P )'),
                sprd([sprd([], 'simpr', 'r || D'), lift(w, ddp, APRD)], 'jca',
                      '( r || D /\\ D || P )')], 'mpd', 'r || P')
    nr2m = sprd([sprd([sprd([lift(w, tb, APRD), sprd([lift(w, rprm, APRD), rdp], 'jca',
                                                     '( r e. Prime /\\ r || P )')], 'jca',
                            '( %s /\\ ( r e. Prime /\\ r || P ) )' % TB),
                       w.inst('twinp3')], 'syl',
                      '( 3 <_ r /\\ ( V ` r ) = ( 2 / r ) /\\ -. r || ( 2 x. M ) )')], 'simp3d',
                '-. r || ( 2 x. M )')
    APRM = '( %s /\\ r || M )' % APRD
    sprm = mkst(w, APRM)
    mz2 = sprm([lift(w, mnn, APRM)], 'nnzd', 'M e. ZZ')
    twoz = sprm([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    md2m = sprm([twoz, mz2, w.inst('dvdsmul2')], 'syl2anc', 'M || ( 2 x. M )')
    r2m = sprm([sprm([sprm([lift(w, rz, APRM), mz2,
                            sprm([twoz, mz2], 'zmulcld', '( 2 x. M ) e. ZZ')], '3jca',
                           '( r e. ZZ /\\ M e. ZZ /\\ ( 2 x. M ) e. ZZ )'),
                      w.inst('dvdstr')], 'syl',
                     '( ( r || M /\\ M || ( 2 x. M ) ) -> r || ( 2 x. M ) )'),
                 sprm([sprm([], 'simpr', 'r || M'), md2m], 'jca',
                      '( r || M /\\ M || ( 2 x. M ) )')], 'mpd', 'r || ( 2 x. M )')
    nrm = sprd([nr2m, r2m], 'mtand', '-. r || M')
    ralr = st([spr([nrm], 'ex', '( r || D -> -. r || M )')], 'ralrimiva',
              'A. r e. Prime ( r || D -> -. r || M )')
    rc = st([st([mnn, st([dnn, dsqf], 'jca', '( D e. NN /\\ ( mmu ` D ) =/= 0 )'), ralr],
                '3jca',
                '( M e. NN /\\ ( D e. NN /\\ ( mmu ` D ) =/= 0 ) /\\ '
                'A. r e. Prime ( r || D -> -. r || M ) )'), w.inst('rcdvds')], 'syl',
            '( # ` %s ) = ( 2 ^ %s )' % (RTD, OMD))
    # ---- the density at D
    qdfin = st([dnn, w.inst('pffinq')], 'syl', '%s e. Fin' % PFQD)
    vsq = st([st([st([vf, v1, vmul], '3jca',
                     '( V : NN --> RR /\ ( V ` 1 ) = 1 /\ %s )' % SHVM),
                  st([dnn, dsqf], 'jca', '( D e. NN /\ ( mmu ` D ) =/= 0 )')], 'jca',
                 '( ( V : NN --> RR /\ ( V ` 1 ) = 1 /\ %s ) /\ '
                 '( D e. NN /\ ( mmu ` D ) =/= 0 ) )' % SHVM), w.inst('vsqfprod')], 'syl',
             '( V ` D ) = prod_ p e. %s ( V ` p )' % PFRD)
    cbq = w.s([w.s([], 'breq1', '( r = q -> ( r || D <-> q || D ) )')], 'cbvrabv',
              '%s = %s' % (PFRD, PFQD))
    vsq2 = st([vsq, st([st([cbq], 'a1i', '%s = %s' % (PFRD, PFQD)), w.inst('prodeq1')], 'syl',
                       'prod_ p e. %s ( V ` p ) = prod_ p e. %s ( V ` p )' % (PFRD, PFQD))],
              'eqtrd', '( V ` D ) = prod_ p e. %s ( V ` p )' % PFQD)
    APD = '( %s /\ p e. %s )' % (ARM, PFQD)
    spd = mkst(w, APD)
    elqp = w.s([w.s([], 'breq1', '( q = p -> ( q || D <-> p || D ) )')], 'elrab',
               '( p e. %s <-> ( p e. Prime /\ p || D ) )' % PFQD)
    pmem = spd([spd([elqp], 'a1i', '( p e. %s <-> ( p e. Prime /\ p || D ) )' % PFQD),
                spd([], 'simpr', 'p e. %s' % PFQD)], 'mpbid', '( p e. Prime /\ p || D )')
    pprm = spd([pmem], 'simpld', 'p e. Prime')
    pdd = spd([pmem], 'simprd', 'p || D')
    pz = spd([spd([pprm, w.inst('prmnn')], 'syl', 'p e. NN')], 'nnzd', 'p e. ZZ')
    pdp = spd([spd([spd([pz, lift(w, dz, APD), spd([lift(w, pnn, APD)], 'nnzd', 'P e. ZZ')],
                        '3jca', '( p e. ZZ /\ D e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                    '( ( p || D /\ D || P ) -> p || P )'),
               spd([pdd, lift(w, ddp, APD)], 'jca', '( p || D /\ D || P )')], 'mpd', 'p || P')
    vp = spd([spd([spd([lift(w, tb, APD), spd([pprm, pdp], 'jca',
                                              '( p e. Prime /\ p || P )')], 'jca',
                       '( %s /\ ( p e. Prime /\ p || P ) )' % TB), w.inst('twinp3')], 'syl',
                  '( 3 <_ p /\ ( V ` p ) = ( 2 / p ) /\ -. p || ( 2 x. M ) )')], 'simp2d',
              '( V ` p ) = ( 2 / p )')
    prd = st([vp], 'prodeq2dv',
             'prod_ p e. %s ( V ` p ) = prod_ p e. %s ( 2 / p )' % (PFQD, PFQD))
    prp = spd([spd([pprm, w.inst('prmnn')], 'syl', 'p e. NN')], 'nnrpd', 'p e. RR+')
    twocc = spd([spd([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'recnd', '2 e. CC')
    pcc = spd([spd([prp], 'rpred', 'p e. RR')], 'recnd', 'p e. CC')
    pne = spd([prp], 'rpne0d', 'p =/= 0')
    dvd = st([qdfin, twocc, pcc, pne], 'fproddiv',
             'prod_ p e. %s ( 2 / p ) = ( prod_ p e. %s 2 / prod_ p e. %s p )'
             % (PFQD, PFQD, PFQD))
    c2 = st([st([qdfin, st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'recnd',
                           '2 e. CC')], 'jca', '( %s e. Fin /\ 2 e. CC )' % PFQD),
             w.inst('fprodconst')], 'syl', 'prod_ p e. %s 2 = ( 2 ^ %s )' % (PFQD, OMD))
    cid = st([st([dnn, dsqf], 'jca', '( D e. NN /\ ( mmu ` D ) =/= 0 )'),
              w.inst('sqfprodid')], 'syl', 'prod_ p e. %s p = D' % PFQD)
    vdval = st([st([vsq2, prd], 'eqtrd',
                   '( V ` D ) = prod_ p e. %s ( 2 / p )' % PFQD),
                st([dvd, st([c2, cid], 'oveq12d',
                            '( prod_ p e. %s 2 / prod_ p e. %s p ) = ( ( 2 ^ %s ) / D )'
                            % (PFQD, PFQD, OMD))], 'eqtrd',
                   'prod_ p e. %s ( 2 / p ) = ( ( 2 ^ %s ) / D )' % (PFQD, OMD))], 'eqtrd',
               '( V ` D ) = ( ( 2 ^ %s ) / D )' % OMD)
    # ---- the main term as a sum over the roots
    rtfin = st([st([w.s([], 'fzofi', '( 0 ..^ D ) e. Fin')], 'a1i', '( 0 ..^ D ) e. Fin'),
                st([w.s([], 'ssrab2', '%s C_ ( 0 ..^ D )' % RTD)], 'a1i',
                   '%s C_ ( 0 ..^ D )' % RTD)], 'ssfid', '%s e. Fin' % RTD)
    tdre = st([tre, drp], 'rerpdivcld', '%s e. RR' % TDV)
    tdcc = st([tdre], 'recnd', '%s e. CC' % TDV)
    omn0 = st([st([qdfin, w.inst('hashcl')], 'syl', '%s e. NN0' % OMD)], 'id', '%s e. NN0' % OMD)
    w.lines.pop()
    omn0 = st([qdfin, w.inst('hashcl')], 'syl', '%s e. NN0' % OMD)
    twonn = st([st([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN'), omn0], 'nnexpcld',
               '( 2 ^ %s ) e. NN' % OMD)
    twocc2 = st([st([twonn], 'nnred', '( 2 ^ %s ) e. RR' % OMD)], 'recnd',
                '( 2 ^ %s ) e. CC' % OMD)
    tcc = st([tre], 'recnd', 'T e. CC')
    dcc = st([dre], 'recnd', 'D e. CC')
    dne = st([drp], 'rpne0d', 'D =/= 0')
    mainc = st([st([rtfin, tdcc], 'jca', '( %s e. Fin /\ %s e. CC )' % (RTD, TDV)),
                w.inst('fsumconst')], 'syl',
               'sum_ r e. %s %s = ( ( # ` %s ) x. %s )' % (RTD, TDV, RTD, TDV))
    step1 = st([mainc, st([rc], 'oveq1d',
                          '( ( # ` %s ) x. %s ) = ( ( 2 ^ %s ) x. %s )'
                          % (RTD, TDV, OMD, TDV))], 'eqtrd',
               'sum_ r e. %s %s = ( ( 2 ^ %s ) x. %s )' % (RTD, TDV, OMD, TDV))
    assoc = st([twocc2, tcc, st([dcc, dne], 'jca', '( D e. CC /\ D =/= 0 )'),
                w.inst('divass')], 'syl3anc',
               '( ( ( 2 ^ %s ) x. T ) / D ) = ( ( 2 ^ %s ) x. %s )' % (OMD, OMD, TDV))
    d23 = st([twocc2, tcc, st([dcc, dne], 'jca', '( D e. CC /\ D =/= 0 )'),
              w.inst('div23')], 'syl3anc',
             '( ( ( 2 ^ %s ) x. T ) / D ) = ( ( ( 2 ^ %s ) / D ) x. T )' % (OMD, OMD))
    mainv = st([step1, st([st([assoc], 'eqcomd',
                              '( ( 2 ^ %s ) x. %s ) = ( ( ( 2 ^ %s ) x. T ) / D )'
                              % (OMD, TDV, OMD)),
                           st([d23, st([st([vdval], 'eqcomd',
                                           '( ( 2 ^ %s ) / D ) = ( V ` D )' % OMD)], 'oveq1d',
                                        '( ( ( 2 ^ %s ) / D ) x. T ) = ( ( V ` D ) x. T )'
                                        % OMD)], 'eqtrd',
                              '( ( ( 2 ^ %s ) x. T ) / D ) = ( ( V ` D ) x. T )' % OMD)],
                          'eqtrd',
                          '( ( 2 ^ %s ) x. %s ) = ( ( V ` D ) x. T )' % (OMD, TDV))], 'eqtrd',
               'sum_ r e. %s %s = ( ( V ` D ) x. T )' % (RTD, TDV))
    mainx = st([mainv, st([st([xeq], 'eqcomd', 'T = X')], 'oveq2d',
                          '( ( V ` D ) x. T ) = ( ( V ` D ) x. X )')], 'eqtrd',
               'sum_ r e. %s %s = ( ( V ` D ) x. X )' % (RTD, TDV))
    # ---- the multiplicity sum as a sum over the residue classes
    ms = st([st([tc, dnn], 'jca', '( %s /\ D e. NN )' % TC), w.inst('twinms')], 'syl',
            '%s = sum_ v e. ( 1 ... T ) if ( D || %s , 1 , 0 )' % (MSD, QF('v')))
    cbvm = w.s([w.s([w.s([w.s([], 'id', '( v = m -> v = m )'),
                          w.s([w.s([], 'oveq2', '( v = m -> ( M x. v ) = ( M x. m ) )')],
                              'oveq1d',
                              '( v = m -> ( ( M x. v ) + 1 ) = ( ( M x. m ) + 1 ) )')],
                         'oveq12d', '( v = m -> %s = %s )' % (QF('v'), QF('m')))], 'breq2d',
                 '( v = m -> ( D || %s <-> D || %s ) )' % (QF('v'), QF('m')))], 'ifbid',
               '( v = m -> if ( D || %s , 1 , 0 ) = if ( D || %s , 1 , 0 ) )'
               % (QF('v'), QF('m')))
    cbvm = w.s([cbvm], 'cbvsumv',
               'sum_ v e. ( 1 ... T ) if ( D || %s , 1 , 0 ) = '
               'sum_ m e. ( 1 ... T ) if ( D || %s , 1 , 0 )' % (QF('v'), QF('m')))
    ms2 = st([ms, st([cbvm], 'a1i',
                     'sum_ v e. ( 1 ... T ) if ( D || %s , 1 , 0 ) = '
                     'sum_ m e. ( 1 ... T ) if ( D || %s , 1 , 0 )'
                     % (QF('v'), QF('m')))], 'eqtrd',
              '%s = sum_ m e. ( 1 ... T ) if ( D || %s , 1 , 0 )' % (MSD, QF('m')))
    MOD = '( m mod D )'
    AMM = '( %s /\ m e. ( 1 ... T ) )' % ARM
    smm = mkst(w, AMM)
    mnn2 = smm([smm([], 'simpr', 'm e. ( 1 ... T )'), w.inst('elfznn')], 'syl', 'm e. NN')
    mz3 = smm([mnn2], 'nnzd', 'm e. ZZ')
    modfzo = smm([mz3, lift(w, dnn, AMM), w.inst('zmodfzo')], 'syl2anc',
                 '%s e. ( 0 ..^ D )' % MOD)
    modz = smm([modfzo, w.inst('elfzoelz')], 'syl', '%s e. ZZ' % MOD)
    modid = smm([modfzo, w.inst('zmodidfzoimp')], 'syl', '( %s mod D ) = %s' % (MOD, MOD))
    qm = smm([smm([smm([lift(w, dnn, AMM), smm([lift(w, mnn, AMM)], 'nnzd', 'M e. ZZ')], 'jca',
                       '( D e. NN /\ M e. ZZ )'),
                   smm([modz, mz3], 'jca', '( %s e. ZZ /\ m e. ZZ )' % MOD), modid], '3jca',
                  '( ( D e. NN /\ M e. ZZ ) /\ ( %s e. ZZ /\ m e. ZZ ) /\ '
                  '( %s mod D ) = %s )' % (MOD, MOD, MOD)), w.inst('quadmod')], 'syl',
             '( D || %s <-> D || %s )' % (QF(MOD), QF('m')))
    elrtm = w.s([w.s([w.s([w.s([], 'id', '( v = %s -> v = %s )' % (MOD, MOD)),
                           w.s([w.s([], 'oveq2',
                                    '( v = %s -> ( M x. v ) = ( M x. %s ) )' % (MOD, MOD))],
                               'oveq1d',
                               '( v = %s -> ( ( M x. v ) + 1 ) = ( ( M x. %s ) + 1 ) )'
                               % (MOD, MOD))], 'oveq12d',
                          '( v = %s -> %s = %s )' % (MOD, QF('v'), QF(MOD)))], 'breq2d',
                  '( v = %s -> ( D || %s <-> D || %s ) )' % (MOD, QF('v'), QF(MOD)))],
                'elrab',
                '( %s e. %s <-> ( %s e. ( 0 ..^ D ) /\ D || %s ) )'
                % (MOD, RTD, MOD, QF(MOD)))
    # case D divides the quadratic
    AMA = '( %s /\ D || %s )' % (AMM, QF('m'))
    sma = mkst(w, AMA)
    dqmod = sma([lift(w, qm, AMA), sma([], 'simpr', 'D || %s' % QF('m'))], 'mpbird',
                'D || %s' % QF(MOD))
    modin = sma([sma([lift(w, modfzo, AMA), dqmod], 'jca',
                     '( %s e. ( 0 ..^ D ) /\ D || %s )' % (MOD, QF(MOD))),
                 sma([elrtm], 'a1i',
                     '( %s e. %s <-> ( %s e. ( 0 ..^ D ) /\ D || %s ) )'
                     % (MOD, RTD, MOD, QF(MOD)))], 'mpbird', '%s e. %s' % (MOD, RTD))
    onecc = sma([sma([sma([], '1red', '1 e. RR')], 'recnd', '1 e. CC')], 'id', '1 e. CC')
    w.lines.pop()
    onecc = sma([sma([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    sit = sma([w.s([], 'eqidd', '( r = %s -> 1 = 1 )' % MOD), lift(w, rtfin, AMA), modin,
               onecc], 'sumite',
              'sum_ r e. %s if ( r = %s , 1 , 0 ) = 1' % (RTD, MOD))
    lhsA = sma([sma([], 'simpr', 'D || %s' % QF('m'))], 'iftrued',
               'if ( D || %s , 1 , 0 ) = 1' % QF('m'))
    caseA = sma([lhsA, sma([sit], 'eqcomd',
                           '1 = sum_ r e. %s if ( r = %s , 1 , 0 )' % (RTD, MOD))], 'eqtrd',
                'if ( D || %s , 1 , 0 ) = sum_ r e. %s if ( r = %s , 1 , 0 )'
                % (QF('m'), RTD, MOD))
    # case D does not divide the quadratic
    AMB = '( %s /\ -. D || %s )' % (AMM, QF('m'))
    smb = mkst(w, AMB)
    AMBR = '( %s /\ r e. %s )' % (AMB, RTD)
    smbr = mkst(w, AMBR)
    elrtr = w.s([w.s([w.s([w.s([], 'id', '( v = r -> v = r )'),
                           w.s([w.s([], 'oveq2', '( v = r -> ( M x. v ) = ( M x. r ) )')],
                               'oveq1d',
                               '( v = r -> ( ( M x. v ) + 1 ) = ( ( M x. r ) + 1 ) )')],
                          'oveq12d', '( v = r -> %s = %s )' % (QF('v'), QF('r')))], 'breq2d',
                  '( v = r -> ( D || %s <-> D || %s ) )' % (QF('v'), QF('r')))], 'elrab',
                '( r e. %s <-> ( r e. ( 0 ..^ D ) /\ D || %s ) )' % (RTD, QF('r')))
    rdq = smbr([smbr([smbr([elrtr], 'a1i',
                           '( r e. %s <-> ( r e. ( 0 ..^ D ) /\ D || %s ) )'
                           % (RTD, QF('r'))),
                      smbr([], 'simpr', 'r e. %s' % RTD)], 'mpbid',
                     '( r e. ( 0 ..^ D ) /\ D || %s )' % QF('r'))], 'simprd',
               'D || %s' % QF('r'))
    AMBRE = '( %s /\ r = %s )' % (AMBR, MOD)
    smbe = mkst(w, AMBRE)
    qeqm = smbe([smbe([], 'simpr', 'r = %s' % MOD),
                 smbe([smbe([], 'simpr', 'r = %s' % MOD)], 'oveq2d',
                      '( M x. r ) = ( M x. %s )' % MOD)], 'id', 'z')
    for _ in range(3):
        w.lines.pop()
    reqm = smbe([], 'simpr', 'r = %s' % MOD)
    qsub = smbe([reqm, smbe([smbe([reqm], 'oveq2d', '( M x. r ) = ( M x. %s )' % MOD)],
                            'oveq1d',
                            '( ( M x. r ) + 1 ) = ( ( M x. %s ) + 1 )' % MOD)], 'oveq12d',
                '%s = %s' % (QF('r'), QF(MOD)))
    dqm2 = smbe([smbe([qsub], 'breq2d', '( D || %s <-> D || %s )' % (QF('r'), QF(MOD))),
                 lift(w, rdq, AMBRE)], 'mpbid', 'D || %s' % QF(MOD))
    dqm3 = smbe([lift(w, qm, AMBRE), dqm2], 'mpbid', 'D || %s' % QF('m'))
    nre = smbr([dqm3, lift(w, smb([], 'simpr', '-. D || %s' % QF('m')), AMBRE)], 'pm2.65da',
               '-. r = %s' % MOD)
    zerob = smbr([nre], 'iffalsed', 'if ( r = %s , 1 , 0 ) = 0' % MOD)
    zsum = smb([smb([zerob], 'sumeq2dv',
                    'sum_ r e. %s if ( r = %s , 1 , 0 ) = sum_ r e. %s 0' % (RTD, MOD, RTD)),
                smb([smb([lift(w, rtfin, AMB)], 'olcd',
                         '( %s C_ ( ZZ>= ` j ) \/ %s e. Fin )' % (RTD, RTD)),
                     w.inst('sumz')], 'syl', 'sum_ r e. %s 0 = 0' % RTD)], 'eqtrd',
               'sum_ r e. %s if ( r = %s , 1 , 0 ) = 0' % (RTD, MOD))
    lhsB = smb([smb([], 'simpr', '-. D || %s' % QF('m'))], 'iffalsed',
               'if ( D || %s , 1 , 0 ) = 0' % QF('m'))
    caseB = smb([lhsB, smb([zsum], 'eqcomd',
                           '0 = sum_ r e. %s if ( r = %s , 1 , 0 )' % (RTD, MOD))], 'eqtrd',
                'if ( D || %s , 1 , 0 ) = sum_ r e. %s if ( r = %s , 1 , 0 )'
                % (QF('m'), RTD, MOD))
    bodyeq = smm([caseA, caseB], 'pm2.61dan',
                 'if ( D || %s , 1 , 0 ) = sum_ r e. %s if ( r = %s , 1 , 0 )'
                 % (QF('m'), RTD, MOD))
    ins = st([bodyeq], 'sumeq2dv',
             'sum_ m e. ( 1 ... T ) if ( D || %s , 1 , 0 ) = '
             'sum_ m e. ( 1 ... T ) sum_ r e. %s if ( r = %s , 1 , 0 )'
             % (QF('m'), RTD, MOD))
    AMR = '( %s /\ ( m e. ( 1 ... T ) /\ r e. %s ) )' % (ARM, RTD)
    smr = mkst(w, AMR)
    ifcc = smr([smr([smr([], '1red', '1 e. RR')], 'recnd', '1 e. CC'),
                smr([smr([], '0red', '0 e. RR')], 'recnd', '0 e. CC')], 'ifcld',
               'if ( r = %s , 1 , 0 ) e. CC' % MOD)
    com = st([st([], 'fzfid', '( 1 ... T ) e. Fin'), rtfin, ifcc], 'fsumcom',
             'sum_ m e. ( 1 ... T ) sum_ r e. %s if ( r = %s , 1 , 0 ) = '
             'sum_ r e. %s sum_ m e. ( 1 ... T ) if ( r = %s , 1 , 0 )'
             % (RTD, MOD, RTD, MOD))
    # ---- the inner sum is the residue-class count
    RAB = '{ x e. ( 1 ... T ) | ( x mod D ) = r }'
    ARR = '( %s /\ r e. %s )' % (ARM, RTD)
    srr = mkst(w, ARR)
    rabss = srr([w.s([], 'ssrab2', '%s C_ ( 1 ... T )' % RAB)], 'a1i',
                '%s C_ ( 1 ... T )' % RAB)
    rabfin = srr([srr([], 'fzfid', '( 1 ... T ) e. Fin'), rabss], 'ssfid', '%s e. Fin' % RAB)
    elrab2 = w.s([w.s([w.s([], 'oveq1', '( x = m -> ( x mod D ) = %s )' % MOD)], 'eqeq1d',
                      '( x = m -> ( ( x mod D ) = r <-> %s = r ) )' % MOD)], 'elrab',
                 '( m e. %s <-> ( m e. ( 1 ... T ) /\ %s = r ) )' % (RAB, MOD))
    ARM2 = '( %s /\ m e. %s )' % (ARR, RAB)
    srm = mkst(w, ARM2)
    mineq = srm([srm([srm([elrab2], 'a1i',
                          '( m e. %s <-> ( m e. ( 1 ... T ) /\ %s = r ) )' % (RAB, MOD)),
                      srm([], 'simpr', 'm e. %s' % RAB)], 'mpbid',
                     '( m e. ( 1 ... T ) /\ %s = r )' % MOD)], 'simprd', '%s = r' % MOD)
    onebody = srm([srm([mineq], 'eqcomd', 'r = %s' % MOD)], 'iftrued',
                  'if ( r = %s , 1 , 0 ) = 1' % MOD)
    ARD = '( %s /\ m e. ( ( 1 ... T ) \ %s ) )' % (ARR, RAB)
    srd = mkst(w, ARD)
    min2 = srd([srd([], 'simpr', 'm e. ( ( 1 ... T ) \ %s )' % RAB), w.inst('eldifi')], 'syl',
               'm e. ( 1 ... T )')
    mnin = srd([srd([], 'simpr', 'm e. ( ( 1 ... T ) \ %s )' % RAB), w.inst('eldifn')], 'syl',
               '-. m e. %s' % RAB)
    nand2 = srd([srd([elrab2], 'a1i',
                     '( m e. %s <-> ( m e. ( 1 ... T ) /\ %s = r ) )' % (RAB, MOD)), mnin],
                'mtbid', '-. ( m e. ( 1 ... T ) /\ %s = r )' % MOD)
    imn = w.s([], 'imnan',
              '( ( m e. ( 1 ... T ) -> -. %s = r ) <-> -. ( m e. ( 1 ... T ) /\ %s = r ) )'
              % (MOD, MOD))
    nmodr = srd([srd([srd([imn], 'a1i',
                          '( ( m e. ( 1 ... T ) -> -. %s = r ) <-> '
                          '-. ( m e. ( 1 ... T ) /\ %s = r ) )' % (MOD, MOD)), nand2],
                     'mpbird', '( m e. ( 1 ... T ) -> -. %s = r )' % MOD), min2], 'mpd',
                '-. %s = r' % MOD)
    ARDE = '( %s /\ r = %s )' % (ARD, MOD)
    srde = mkst(w, ARDE)
    nrm2 = srd([srde([srde([], 'simpr', 'r = %s' % MOD)], 'eqcomd', '%s = r' % MOD),
                lift(w, nmodr, ARDE)], 'pm2.65da', '-. r = %s' % MOD)
    zerob2 = srd([nrm2], 'iffalsed', 'if ( r = %s , 1 , 0 ) = 0' % MOD)
    ifccR = srm([srm([srm([], '1red', '1 e. RR')], 'recnd', '1 e. CC'),
                 srm([srm([], '0red', '0 e. RR')], 'recnd', '0 e. CC')], 'ifcld',
                'if ( r = %s , 1 , 0 ) e. CC' % MOD)
    ss = srr([rabss, ifccR, zerob2, srr([], 'fzfid', '( 1 ... T ) e. Fin')], 'fsumss',
             'sum_ m e. %s if ( r = %s , 1 , 0 ) = '
             'sum_ m e. ( 1 ... T ) if ( r = %s , 1 , 0 )' % (RAB, MOD, MOD))
    onecc2 = srr([srr([], '1red', '1 e. RR')], 'recnd', '1 e. CC')
    rsum = srr([srr([onebody], 'sumeq2dv',
                    'sum_ m e. %s if ( r = %s , 1 , 0 ) = sum_ m e. %s 1' % (RAB, MOD, RAB)),
                srr([srr([rabfin, onecc2], 'jca', '( %s e. Fin /\ 1 e. CC )' % RAB),
                     w.inst('fsumconst')], 'syl',
                    'sum_ m e. %s 1 = ( ( # ` %s ) x. 1 )' % (RAB, RAB))], 'eqtrd',
               'sum_ m e. %s if ( r = %s , 1 , 0 ) = ( ( # ` %s ) x. 1 )' % (RAB, MOD, RAB))
    hrab = srr([rabfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RAB)
    hrabre = srr([hrab], 'nn0red', '( # ` %s ) e. RR' % RAB)
    rsum2 = srr([rsum, srr([srr([hrabre], 'recnd', '( # ` %s ) e. CC' % RAB)], 'mulridd',
                           '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (RAB, RAB))], 'eqtrd',
                'sum_ m e. %s if ( r = %s , 1 , 0 ) = %s' % (RAB, MOD, CNTR))
    innr = srr([srr([ss], 'eqcomd',
                    'sum_ m e. ( 1 ... T ) if ( r = %s , 1 , 0 ) = '
                    'sum_ m e. %s if ( r = %s , 1 , 0 )' % (MOD, RAB, MOD)), rsum2], 'eqtrd',
               'sum_ m e. ( 1 ... T ) if ( r = %s , 1 , 0 ) = %s' % (MOD, CNTR))
    msfin = st([st([ms2, ins], 'eqtrd',
                   '%s = sum_ m e. ( 1 ... T ) sum_ r e. %s if ( r = %s , 1 , 0 )'
                   % (MSD, RTD, MOD)),
                st([com, st([innr], 'sumeq2dv',
                            'sum_ r e. %s sum_ m e. ( 1 ... T ) if ( r = %s , 1 , 0 ) = '
                            'sum_ r e. %s %s' % (RTD, MOD, RTD, CNTR))], 'eqtrd',
                   'sum_ m e. ( 1 ... T ) sum_ r e. %s if ( r = %s , 1 , 0 ) = '
                   'sum_ r e. %s %s' % (RTD, MOD, RTD, CNTR))], 'eqtrd',
               '%s = sum_ r e. %s %s' % (MSD, RTD, CNTR))
    # ---- the remainder and its absolute value
    cntcc = srr([srr([hrabre], 'recnd', '( # ` %s ) e. CC' % RAB)], 'id', '%s e. CC' % CNTR)
    w.lines.pop()
    cntcc = srr([hrabre], 'recnd', '%s e. CC' % CNTR)
    sub = st([rtfin, cntcc, lift(w, tdcc, ARR)], 'fsumsub',
             'sum_ r e. %s ( %s - %s ) = ( sum_ r e. %s %s - sum_ r e. %s %s )'
             % (RTD, CNTR, TDV, RTD, CNTR, RTD, TDV))
    remeq = st([sub, st([st([msfin], 'eqcomd',
                            'sum_ r e. %s %s = %s' % (RTD, CNTR, MSD)), mainx], 'oveq12d',
                        '( sum_ r e. %s %s - sum_ r e. %s %s ) = %s'
                        % (RTD, CNTR, RTD, TDV, RMD))], 'eqtrd',
               'sum_ r e. %s ( %s - %s ) = %s' % (RTD, CNTR, TDV, RMD))
    dcc2 = srr([srr([cntcc, lift(w, tdcc, ARR)], 'subcld', '( %s - %s ) e. CC' % (CNTR, TDV))],
               'id', 'z')
    w.lines.pop()
    dcc2 = srr([cntcc, lift(w, tdcc, ARR)], 'subcld', '( %s - %s ) e. CC' % (CNTR, TDV))
    absle = st([rtfin, dcc2], 'fsumabs',
               '( abs ` sum_ r e. %s ( %s - %s ) ) <_ '
               'sum_ r e. %s ( abs ` ( %s - %s ) )' % (RTD, CNTR, TDV, RTD, CNTR, TDV))
    absle2 = st([st([remeq], 'fveq2d',
                    '( abs ` sum_ r e. %s ( %s - %s ) ) = ( abs ` %s )'
                    % (RTD, CNTR, TDV, RMD)), absle], 'eqbrtrrd',
                '( abs ` %s ) <_ sum_ r e. %s ( abs ` ( %s - %s ) )'
                % (RMD, RTD, CNTR, TDV))
    rfzo = srr([srr([srr([elrtr], 'a1i',
                         '( r e. %s <-> ( r e. ( 0 ..^ D ) /\ D || %s ) )' % (RTD, QF('r'))),
                     srr([], 'simpr', 'r e. %s' % RTD)], 'mpbid',
                    '( r e. ( 0 ..^ D ) /\ D || %s )' % QF('r'))], 'simpld',
               'r e. ( 0 ..^ D )')
    cm = srr([srr([lift(w, tn0, ARR), lift(w, dnn, ARR), rfzo], '3jca',
                  '( T e. NN0 /\ D e. NN /\ r e. ( 0 ..^ D ) )'), w.inst('cntmod')], 'syl',
             '( abs ` ( %s - %s ) ) <_ 1' % (CNTR, TDV))
    absre = srr([srr([dcc2], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (CNTR, TDV))], 'id',
                'z')
    w.lines.pop()
    absre = srr([dcc2], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (CNTR, TDV))
    onere3 = srr([], '1red', '1 e. RR')
    sumle = st([rtfin, absre, onere3, cm], 'fsumle',
               'sum_ r e. %s ( abs ` ( %s - %s ) ) <_ sum_ r e. %s 1'
               % (RTD, CNTR, TDV, RTD))
    onesum = st([st([rtfin, st([st([], '1red', '1 e. RR')], 'recnd', '1 e. CC')], 'jca',
                    '( %s e. Fin /\ 1 e. CC )' % RTD), w.inst('fsumconst')], 'syl',
                'sum_ r e. %s 1 = ( ( # ` %s ) x. 1 )' % (RTD, RTD))
    hrtre = st([st([rtfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RTD)], 'nn0red',
               '( # ` %s ) e. RR' % RTD)
    onesum2 = st([onesum, st([st([hrtre], 'recnd', '( # ` %s ) e. CC' % RTD)], 'mulridd',
                             '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (RTD, RTD))], 'eqtrd',
                 'sum_ r e. %s 1 = ( # ` %s )' % (RTD, RTD))
    twole = st([st([dnn, dsqf], 'jca', '( D e. NN /\ ( mmu ` D ) =/= 0 )'),
                w.inst('sqf2omle')], 'syl', '( 2 ^ %s ) <_ D' % OMD)
    hrtd = st([rc, twole], 'eqbrtrd', '( # ` %s ) <_ D' % RTD)
    sumre2 = st([rtfin, absre], 'fsumrecl',
                'sum_ r e. %s ( abs ` ( %s - %s ) ) e. RR' % (RTD, CNTR, TDV))
    absrm = st([st([st([msfin, st([rtfin, srr([cntcc], 'id', 'z')], 'id', 'z')], 'id', 'z')],
                   'id', 'z')], 'id', 'z')
    for _ in range(5):
        w.lines.pop()
    cntre = srr([hrabre], 'id', '%s e. RR' % CNTR)
    w.lines.pop()
    msre = st([rtfin, srr([hrab], 'nn0red', '%s e. RR' % CNTR)], 'fsumrecl',
              'sum_ r e. %s %s e. RR' % (RTD, CNTR))
    rmre = st([st([msfin, msre], 'eqeltrd', '%s e. RR' % MSD),
               st([st([vdval, st([twonn], 'nnred', '( 2 ^ %s ) e. RR' % OMD)], 'eqeltrd',
                      '( V ` D ) e. RR')], 'id', 'z')], 'id', 'z')
    for _ in range(3):
        w.lines.pop()
    msrl = st([msfin, msre], 'eqeltrd', '%s e. RR' % MSD)
    vdre = st([vdval, st([st([twonn], 'nnred', '( 2 ^ %s ) e. RR' % OMD), drp],
                         'rerpdivcld', '( ( 2 ^ %s ) / D ) e. RR' % OMD)], 'eqeltrd',
              '( V ` D ) e. RR')
    xre = st([xeq, tre], 'eqeltrd', 'X e. RR')
    rmrel = st([msrl, st([vdre, xre], 'remulcld', '( ( V ` D ) x. X ) e. RR')], 'resubcld',
               '%s e. RR' % RMD)
    absrmre = st([st([rmrel], 'recnd', '%s e. CC' % RMD)], 'abscld',
                  '( abs ` %s ) e. RR' % RMD)
    chain1 = st([sumre2, hrtre, dre, st([sumle, onesum2], 'breqtrd',
                                        'sum_ r e. %s ( abs ` ( %s - %s ) ) <_ ( # ` %s )'
                                        % (RTD, CNTR, TDV, RTD)), hrtd], 'letrd',
                'sum_ r e. %s ( abs ` ( %s - %s ) ) <_ D' % (RTD, CNTR, TDV))
    w.qed([absrmre, sumre2, dre, absle2, chain1], 'letrd',
          '( %s -> ( abs ` %s ) <_ D )' % (ARM, RMD))
    return w


ALL = {'twinrem': twinrem}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
