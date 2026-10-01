"""Sortie v4a: the error sum of the twin sieve."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import mkst
from cl import lift
from v4a_tb import SH, TMR, TRAL, TB, shparts
from v4a_c import TC, AAS, WWS

DVP = '{ x e. NN | x || P }'
OMR = '( # ` { r e. Prime | r || d } )'
RMD = '( sum_ n e. A if ( d || n , ( W ` n ) , 0 ) - ( ( V ` d ) x. X ) )'
BODY = '( ( 3 ^ %s ) x. ( abs ` %s ) )' % (OMR, RMD)
ERR = 'sum_ d e. %s if ( d <_ Y , %s , 0 )' % (DVP, BODY)
Y3 = '( ( Z ^ 2 ) ^ 3 )'
Y4 = '( ( Z ^ 2 ) ^ 4 )'
RABY = '{ x e. NN | ( x || P /\\ x <_ Y ) }'


def twinerr():
    w = WS('twinerr', 'The error sum of the twin sieve is at most the eighth power of the '
                      'sifting bound.')
    st = mkst(w, TC)
    tb = st([], 'simpl', TB)
    rest = st([], 'simpr',
              '( ( T e. NN0 /\\ X = T ) /\\ ( A = %s /\\ W = %s ) )' % (AAS, WWS))
    sh = shparts(w, st, st([tb], 'simp1d', SH))
    mnn = st([st([tb], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    znn = st([st([tb], 'simp2d', TMR)], 'simp2d', 'Z e. NN')
    yeq = st([st([tb], 'simp2d', TMR)], 'simp3d', 'Y = ( Z ^ 2 )')
    pnn = sh['pnn']
    psqf = sh['psqf']
    zre = st([znn], 'nnred', 'Z e. RR')
    z2nn = st([znn, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'nnexpcld',
              '( Z ^ 2 ) e. NN')
    z2re = st([z2nn], 'nnred', '( Z ^ 2 ) e. RR')
    z2ge = st([st([z2nn], 'nnnn0d', '( Z ^ 2 ) e. NN0')], 'nn0ge0d', '0 <_ ( Z ^ 2 )')
    y3nn = st([z2nn, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'nnexpcld',
              '%s e. NN' % Y3)
    y3re = st([y3nn], 'nnred', '%s e. RR' % Y3)
    y3ge = st([st([y3nn], 'nnnn0d', '%s e. NN0' % Y3)], 'nn0ge0d', '0 <_ %s' % Y3)
    dvfin = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    eldp = w.s([w.s([], 'breq1', '( x = d -> ( x || P <-> d || P ) )')], 'elrab',
               '( d e. %s <-> ( d e. NN /\\ d || P ) )' % DVP)
    AD = '( %s /\\ d e. %s )' % (TC, DVP)
    sd = mkst(w, AD)
    dmem = sd([sd([eldp], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || P ) )' % DVP),
               sd([], 'simpr', 'd e. %s' % DVP)], 'mpbid', '( d e. NN /\\ d || P )')
    dnn = sd([dmem], 'simpld', 'd e. NN')
    ddp = sd([dmem], 'simprd', 'd || P')
    dre = sd([dnn], 'nnred', 'd e. RR')
    dge = sd([sd([dnn], 'nnnn0d', 'd e. NN0')], 'nn0ge0d', '0 <_ d')
    dsqf = sd([sd([sd([lift(w, pnn, AD), dnn, ddp], '3jca',
                      '( P e. NN /\\ d e. NN /\\ d || P )'), w.inst('dvdssqf')], 'syl',
                  '( ( mmu ` P ) =/= 0 -> ( mmu ` d ) =/= 0 )'), lift(w, psqf, AD)], 'mpd',
              '( mmu ` d ) =/= 0')
    rem = sd([sd([lift(w, st([], 'id', TC), AD), dmem], 'jca',
                 '( %s /\\ ( d e. NN /\\ d || P ) )' % TC), w.inst('twinrem')], 'syl',
             '( abs ` %s ) <_ d' % RMD)
    cbr = w.s([w.s([], 'breq1', '( q = r -> ( q || d <-> r || d ) )')], 'cbvrabv',
              '{ q e. Prime | q || d } = { r e. Prime | r || d }')
    sq3 = sd([sd([sd([dnn, dsqf], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'),
                  w.inst('sqf3omle')], 'syl',
                 '( 3 ^ ( # ` { q e. Prime | q || d } ) ) <_ ( d ^ 2 )'),
              sd([sd([cbr], 'a1i',
                      '{ q e. Prime | q || d } = { r e. Prime | r || d }')], 'fveq2d',
                  '( # ` { q e. Prime | q || d } ) = %s' % OMR)], 'id', 'z')
    w.lines.pop()
    omeq = sd([sd([cbr], 'a1i', '{ q e. Prime | q || d } = { r e. Prime | r || d }')],
              'fveq2d', '( # ` { q e. Prime | q || d } ) = %s' % OMR)
    sq3 = sd([sd([sd([sd([dnn, dsqf], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'),
                      w.inst('sqf3omle')], 'syl',
                     '( 3 ^ ( # ` { q e. Prime | q || d } ) ) <_ ( d ^ 2 )'),
                  sd([omeq], 'oveq2d',
                      '( 3 ^ ( # ` { q e. Prime | q || d } ) ) = ( 3 ^ %s )' % OMR)],
                 'eqbrtrrd', '( 3 ^ %s ) <_ ( d ^ 2 )' % OMR)], 'id', 'z')
    w.lines.pop()
    sq3 = sd([sd([omeq], 'oveq2d',
                 '( 3 ^ ( # ` { q e. Prime | q || d } ) ) = ( 3 ^ %s )' % OMR),
              sd([sd([dnn, dsqf], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'),
                  w.inst('sqf3omle')], 'syl',
                 '( 3 ^ ( # ` { q e. Prime | q || d } ) ) <_ ( d ^ 2 )')], 'eqbrtrrd',
             '( 3 ^ %s ) <_ ( d ^ 2 )' % OMR)
    # the product bound
    omn0 = sd([sd([sd([cbr], 'a1i',
                      '{ q e. Prime | q || d } = { r e. Prime | r || d }'),
                   sd([dnn, w.inst('pffinq')], 'syl',
                      '{ q e. Prime | q || d } e. Fin')], 'eqeltrrd',
                  '{ r e. Prime | r || d } e. Fin'), w.inst('hashcl')], 'syl',
              '%s e. NN0' % OMR)
    thnn = sd([sd([w.s([], '3nn', '3 e. NN')], 'a1i', '3 e. NN'), omn0], 'nnexpcld',
              '( 3 ^ %s ) e. NN' % OMR)
    thre = sd([thnn], 'nnred', '( 3 ^ %s ) e. RR' % OMR)
    thge = sd([sd([thnn], 'nnnn0d', '( 3 ^ %s ) e. NN0' % OMR)], 'nn0ge0d',
              '0 <_ ( 3 ^ %s )' % OMR)
    d2re = sd([dre, sd([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'reexpcld',
              '( d ^ 2 ) e. RR')
    # the remainder is real
    sh1 = st([tb], 'simp1d', SH)
    shA = st([st([sh1], 'simpld',
                 '( ( A e. Fin /\ A C_ NN /\ W : NN --> RR ) /\ '
                 '( A. k e. NN 0 <_ ( W ` k ) /\ X e. RR /\ ( Y e. RR /\ 1 <_ Y ) ) )')],
             'simpld', '( A e. Fin /\ A C_ NN /\ W : NN --> RR )')
    afin = st([shA], 'simp1d', 'A e. Fin')
    assn = st([shA], 'simp2d', 'A C_ NN')
    wfn = st([shA], 'simp3d', 'W : NN --> RR')
    xre = st([st([st([sh1], 'simpld',
                     '( ( A e. Fin /\ A C_ NN /\ W : NN --> RR ) /\ '
                     '( A. k e. NN 0 <_ ( W ` k ) /\ X e. RR /\ '
                     '( Y e. RR /\ 1 <_ Y ) ) )')], 'simprd',
                 '( A. k e. NN 0 <_ ( W ` k ) /\ X e. RR /\ ( Y e. RR /\ 1 <_ Y ) )')],
              'simp2d', 'X e. RR')
    yre = st([st([st([sh1], 'simpld',
                     '( ( A e. Fin /\ A C_ NN /\ W : NN --> RR ) /\ '
                     '( A. k e. NN 0 <_ ( W ` k ) /\ X e. RR /\ '
                     '( Y e. RR /\ 1 <_ Y ) ) )')], 'simprd',
                 '( A. k e. NN 0 <_ ( W ` k ) /\ X e. RR /\ ( Y e. RR /\ 1 <_ Y ) )')],
             'simp3d', '( Y e. RR /\ 1 <_ Y )')
    ADN = '( %s /\ n e. A )' % AD
    sdn = mkst(w, ADN)
    wnre = sdn([lift(w, wfn, ADN),
                sdn([lift(w, assn, ADN), sdn([], 'simpr', 'n e. A')], 'sseldd', 'n e. NN'),
                w.inst('ffvelcdm')], 'syl2anc', '( W ` n ) e. RR')
    ifnre = sdn([wnre, sdn([], '0red', '0 e. RR')], 'ifcld',
                'if ( d || n , ( W ` n ) , 0 ) e. RR')
    msre = sd([lift(w, afin, AD), ifnre], 'fsumrecl',
              'sum_ n e. A if ( d || n , ( W ` n ) , 0 ) e. RR')
    vdre = sd([lift(w, sh['vf'], AD), dnn, w.inst('ffvelcdm')], 'syl2anc', '( V ` d ) e. RR')
    rmre = sd([msre, sd([vdre, lift(w, xre, AD)], 'remulcld', '( ( V ` d ) x. X ) e. RR')],
              'resubcld', '%s e. RR' % RMD)
    absre = sd([sd([rmre], 'recnd', '%s e. CC' % RMD)], 'abscld', '( abs ` %s ) e. RR' % RMD)
    absge = sd([sd([rmre], 'recnd', '%s e. CC' % RMD)], 'absge0d', '0 <_ ( abs ` %s )' % RMD)
    prodle = sd([sd([sd([sd([thre, thge], 'jca',
                            '( ( 3 ^ %s ) e. RR /\ 0 <_ ( 3 ^ %s ) )' % (OMR, OMR)),
                         d2re], 'jca',
                        '( ( ( 3 ^ %s ) e. RR /\ 0 <_ ( 3 ^ %s ) ) /\ ( d ^ 2 ) e. RR )'
                        % (OMR, OMR)),
                     sd([sd([absre, absge], 'jca',
                            '( ( abs ` %s ) e. RR /\ 0 <_ ( abs ` %s ) )' % (RMD, RMD)),
                         dre], 'jca',
                        '( ( ( abs ` %s ) e. RR /\ 0 <_ ( abs ` %s ) ) /\ d e. RR )'
                        % (RMD, RMD))], 'jca',
                    '( ( ( ( 3 ^ %s ) e. RR /\ 0 <_ ( 3 ^ %s ) ) /\ ( d ^ 2 ) e. RR ) /\ '
                    '( ( ( abs ` %s ) e. RR /\ 0 <_ ( abs ` %s ) ) /\ d e. RR ) )'
                    % (OMR, OMR, RMD, RMD)), w.inst('lemul12a')], 'sylc', 'z')
    w.lines.pop()
    prodimp = sd([sd([sd([sd([thre, thge], 'jca',
                             '( ( 3 ^ %s ) e. RR /\ 0 <_ ( 3 ^ %s ) )' % (OMR, OMR)),
                          d2re], 'jca',
                         '( ( ( 3 ^ %s ) e. RR /\ 0 <_ ( 3 ^ %s ) ) /\ ( d ^ 2 ) e. RR )'
                         % (OMR, OMR)),
                      sd([sd([absre, absge], 'jca',
                             '( ( abs ` %s ) e. RR /\ 0 <_ ( abs ` %s ) )' % (RMD, RMD)),
                          dre], 'jca',
                         '( ( ( abs ` %s ) e. RR /\ 0 <_ ( abs ` %s ) ) /\ d e. RR )'
                         % (RMD, RMD))], 'jca',
                     '( ( ( ( 3 ^ %s ) e. RR /\ 0 <_ ( 3 ^ %s ) ) /\ ( d ^ 2 ) e. RR ) /\ '
                     '( ( ( abs ` %s ) e. RR /\ 0 <_ ( abs ` %s ) ) /\ d e. RR ) )'
                     % (OMR, OMR, RMD, RMD)), w.inst('lemul12a')], 'syl',
                  '( ( ( 3 ^ %s ) <_ ( d ^ 2 ) /\ ( abs ` %s ) <_ d ) -> '
                  '( ( 3 ^ %s ) x. ( abs ` %s ) ) <_ ( ( d ^ 2 ) x. d ) )'
                  % (OMR, RMD, OMR, RMD))
    prodle = sd([prodimp, sd([sq3, rem], 'jca',
                             '( ( 3 ^ %s ) <_ ( d ^ 2 ) /\ ( abs ` %s ) <_ d )'
                             % (OMR, RMD))], 'mpd', '%s <_ ( ( d ^ 2 ) x. d )' % BODY)
    d3eq = sd([sd([sd([dre], 'recnd', 'd e. CC'),
                   sd([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0'),
                   w.inst('expp1')], 'syl2anc', '( d ^ ( 2 + 1 ) ) = ( ( d ^ 2 ) x. d )'),
               sd([sd([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'a1i', '( 2 + 1 ) = 3')],
                  'oveq2d', '( d ^ ( 2 + 1 ) ) = ( d ^ 3 )')], 'eqtr3d',
              '( d ^ 3 ) = ( ( d ^ 2 ) x. d )')
    prodle2 = sd([prodle, sd([d3eq], 'eqcomd', '( ( d ^ 2 ) x. d ) = ( d ^ 3 )')], 'breqtrd',
                 '%s <_ ( d ^ 3 )' % BODY)
    # the case d <_ Y
    ADY = '( %s /\ d <_ Y )' % AD
    sdy = mkst(w, ADY)
    dley = sdy([sdy([], 'simpr', 'd <_ Y'), lift(w, yeq, ADY)], 'breqtrd', 'd <_ ( Z ^ 2 )')
    d3le = sdy([sdy([sdy([lift(w, dre, ADY), lift(w, z2re, ADY),
                          sdy([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], '3jca',
                         '( d e. RR /\ ( Z ^ 2 ) e. RR /\ 3 e. NN0 )'),
                     sdy([lift(w, dge, ADY), dley], 'jca',
                         '( 0 <_ d /\ d <_ ( Z ^ 2 ) )')], 'jca',
                    '( ( d e. RR /\ ( Z ^ 2 ) e. RR /\ 3 e. NN0 ) /\ '
                    '( 0 <_ d /\ d <_ ( Z ^ 2 ) ) )'), w.inst('leexp1a')], 'syl',
               '( d ^ 3 ) <_ %s' % Y3)
    d3re = sd([dre, sd([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'reexpcld',
              '( d ^ 3 ) e. RR')
    bodyre = sd([thre, absre], 'remulcld', '%s e. RR' % BODY)
    ifle1 = sdy([sdy([lift(w, bodyre, ADY), lift(w, d3re, ADY), lift(w, y3re, ADY),
                      lift(w, prodle2, ADY), d3le], 'letrd', '%s <_ %s' % (BODY, Y3)),
                 sdy([sdy([], 'simpr', 'd <_ Y')], 'iftrued',
                     'if ( d <_ Y , %s , 0 ) = %s' % (BODY, BODY))], 'id', 'z')
    w.lines.pop()
    chain = sdy([lift(w, bodyre, ADY), lift(w, d3re, ADY), lift(w, y3re, ADY),
                 lift(w, prodle2, ADY), d3le], 'letrd', '%s <_ %s' % (BODY, Y3))
    lhsT = sdy([sdy([], 'simpr', 'd <_ Y')], 'iftrued',
               'if ( d <_ Y , %s , 0 ) = %s' % (BODY, BODY))
    rhsT = sdy([sdy([], 'simpr', 'd <_ Y')], 'iftrued',
               'if ( d <_ Y , %s , 0 ) = %s' % (Y3, Y3))
    caseT = sdy([sdy([lhsT, chain], 'eqbrtrd', 'if ( d <_ Y , %s , 0 ) <_ %s' % (BODY, Y3)),
                 sdy([rhsT], 'eqcomd', '%s = if ( d <_ Y , %s , 0 )' % (Y3, Y3))], 'breqtrd',
                'if ( d <_ Y , %s , 0 ) <_ if ( d <_ Y , %s , 0 )' % (BODY, Y3))
    ADN2 = '( %s /\ -. d <_ Y )' % AD
    sdn2 = mkst(w, ADN2)
    caseF = sdn2([sdn2([sdn2([sdn2([], 'simpr', '-. d <_ Y')], 'iffalsed',
                             'if ( d <_ Y , %s , 0 ) = 0' % BODY),
                        sdn2([sdn2([], '0red', '0 e. RR')], 'leidd', '0 <_ 0')], 'eqbrtrd',
                       'if ( d <_ Y , %s , 0 ) <_ 0' % BODY),
                  sdn2([sdn2([sdn2([], 'simpr', '-. d <_ Y')], 'iffalsed',
                             'if ( d <_ Y , %s , 0 ) = 0' % Y3)], 'eqcomd',
                       '0 = if ( d <_ Y , %s , 0 )' % Y3)], 'breqtrd',
                 'if ( d <_ Y , %s , 0 ) <_ if ( d <_ Y , %s , 0 )' % (BODY, Y3))
    both = sd([caseT, caseF], 'pm2.61dan',
              'if ( d <_ Y , %s , 0 ) <_ if ( d <_ Y , %s , 0 )' % (BODY, Y3))
    ifbre = sd([bodyre, sd([], '0red', '0 e. RR')], 'ifcld',
               'if ( d <_ Y , %s , 0 ) e. RR' % BODY)
    ifyre = sd([lift(w, y3re, AD), sd([], '0red', '0 e. RR')], 'ifcld',
               'if ( d <_ Y , %s , 0 ) e. RR' % Y3)
    sumle = st([dvfin, ifbre, ifyre, both], 'fsumle',
               '%s <_ sum_ d e. %s if ( d <_ Y , %s , 0 )' % (ERR, DVP, Y3))
    # ---- the constant sum
    AX = '( %s /\ x e. NN )' % TC
    sx = mkst(w, AX)
    imp = sx([w.s([], 'simpl', '( ( x || P /\ x <_ Y ) -> x || P )')], 'a1i',
             '( ( x || P /\ x <_ Y ) -> x || P )')
    rsub = st([imp], 'ss2rabdv', '%s C_ %s' % (RABY, DVP))
    rabfin = st([dvfin, rsub], 'ssfid', '%s e. Fin' % RABY)
    elry = w.s([w.s([w.s([], 'breq1', '( x = d -> ( x || P <-> d || P ) )'),
                     w.s([], 'breq1', '( x = d -> ( x <_ Y <-> d <_ Y ) )')], 'anbi12d',
                    '( x = d -> ( ( x || P /\ x <_ Y ) <-> ( d || P /\ d <_ Y ) ) )')],
               'elrab',
               '( d e. %s <-> ( d e. NN /\ ( d || P /\ d <_ Y ) ) )' % RABY)
    ADR = '( %s /\ d e. %s )' % (TC, RABY)
    sdr = mkst(w, ADR)
    drmem = sdr([sdr([elry], 'a1i',
                     '( d e. %s <-> ( d e. NN /\ ( d || P /\ d <_ Y ) ) )' % RABY),
                 sdr([], 'simpr', 'd e. %s' % RABY)], 'mpbid',
                '( d e. NN /\ ( d || P /\ d <_ Y ) )')
    drnn = sdr([drmem], 'simpld', 'd e. NN')
    drle = sdr([sdr([drmem], 'simprd', '( d || P /\ d <_ Y )')], 'simprd', 'd <_ Y')
    ontr = sdr([drle], 'iftrued', 'if ( d <_ Y , %s , 0 ) = %s' % (Y3, Y3))
    ADD = '( %s /\ d e. ( %s \ %s ) )' % (TC, DVP, RABY)
    sdd = mkst(w, ADD)
    ddin = sdd([sdd([], 'simpr', 'd e. ( %s \ %s )' % (DVP, RABY)), w.inst('eldifi')], 'syl',
               'd e. %s' % DVP)
    ddnin = sdd([sdd([], 'simpr', 'd e. ( %s \ %s )' % (DVP, RABY)), w.inst('eldifn')], 'syl',
                '-. d e. %s' % RABY)
    ddnn = sdd([sdd([sdd([eldp], 'a1i', '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP),
                     ddin], 'mpbid', '( d e. NN /\ d || P )')], 'simpld', 'd e. NN')
    dddp = sdd([sdd([sdd([eldp], 'a1i', '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP),
                     ddin], 'mpbid', '( d e. NN /\ d || P )')], 'simprd', 'd || P')
    ADDY = '( %s /\ d <_ Y )' % ADD
    sddy = mkst(w, ADDY)
    dinr = sddy([sddy([lift(w, ddnn, ADDY),
                       sddy([lift(w, dddp, ADDY), sddy([], 'simpr', 'd <_ Y')], 'jca',
                            '( d || P /\ d <_ Y )')], 'jca',
                      '( d e. NN /\ ( d || P /\ d <_ Y ) )'),
                 sddy([elry], 'a1i',
                      '( d e. %s <-> ( d e. NN /\ ( d || P /\ d <_ Y ) ) )' % RABY)],
                'mpbird', 'd e. %s' % RABY)
    ndley = sdd([ddnin, dinr], 'mtand', '-. d <_ Y')
    offb = sdd([ndley], 'iffalsed', 'if ( d <_ Y , %s , 0 ) = 0' % Y3)
    ifycc = sdr([sdr([lift(w, y3re, ADR)], 'recnd', '%s e. CC' % Y3),
                 sdr([sdr([], '0red', '0 e. RR')], 'recnd', '0 e. CC')], 'ifcld',
                'if ( d <_ Y , %s , 0 ) e. CC' % Y3)
    ssy = st([rsub, ifycc, offb, dvfin], 'fsumss',
             'sum_ d e. %s if ( d <_ Y , %s , 0 ) = sum_ d e. %s if ( d <_ Y , %s , 0 )'
             % (RABY, Y3, DVP, Y3))
    consty = st([st([ontr], 'sumeq2dv',
                    'sum_ d e. %s if ( d <_ Y , %s , 0 ) = sum_ d e. %s %s'
                    % (RABY, Y3, RABY, Y3)),
                 st([st([rabfin, st([y3re], 'recnd', '%s e. CC' % Y3)], 'jca',
                        '( %s e. Fin /\ %s e. CC )' % (RABY, Y3)), w.inst('fprodconst')],
                    'id', 'z')], 'id', 'z')
    for _ in range(2):
        w.lines.pop()
    fsc = st([st([rabfin, st([y3re], 'recnd', '%s e. CC' % Y3)], 'jca',
                 '( %s e. Fin /\ %s e. CC )' % (RABY, Y3)), w.inst('fsumconst')], 'syl',
             'sum_ d e. %s %s = ( ( # ` %s ) x. %s )' % (RABY, Y3, RABY, Y3))
    consty = st([st([ontr], 'sumeq2dv',
                    'sum_ d e. %s if ( d <_ Y , %s , 0 ) = sum_ d e. %s %s'
                    % (RABY, Y3, RABY, Y3)), fsc], 'eqtrd',
                'sum_ d e. %s if ( d <_ Y , %s , 0 ) = ( ( # ` %s ) x. %s )'
                % (RABY, Y3, RABY, Y3))
    # the number of admissible divisors is at most Z squared
    drfz = sdr([sdr([drnn, lift(w, z2nn, ADR),
                     sdr([drle, lift(w, yeq, ADR)], 'breqtrd', 'd <_ ( Z ^ 2 )')], '3jca',
                    '( d e. NN /\ ( Z ^ 2 ) e. NN /\ d <_ ( Z ^ 2 ) )'),
                sdr([w.s([], 'elfz1b',
                         '( d e. ( 1 ... ( Z ^ 2 ) ) <-> ( d e. NN /\ ( Z ^ 2 ) e. NN /\ '
                         'd <_ ( Z ^ 2 ) ) )')], 'a1i',
                    '( d e. ( 1 ... ( Z ^ 2 ) ) <-> ( d e. NN /\ ( Z ^ 2 ) e. NN /\ '
                    'd <_ ( Z ^ 2 ) ) )')], 'mpbird', 'd e. ( 1 ... ( Z ^ 2 ) )')
    rsub2 = st([st([drfz], 'ex', '( d e. %s -> d e. ( 1 ... ( Z ^ 2 ) ) )' % RABY)], 'ssrdv',
               '%s C_ ( 1 ... ( Z ^ 2 ) )' % RABY)
    hle = st([st([], 'fzfid', '( 1 ... ( Z ^ 2 ) ) e. Fin'), rsub2, w.inst('hashss')],
             'syl2anc', '( # ` %s ) <_ ( # ` ( 1 ... ( Z ^ 2 ) ) )' % RABY)
    hfz = st([st([z2nn], 'nnnn0d', '( Z ^ 2 ) e. NN0'), w.inst('hashfz1')], 'syl',
             '( # ` ( 1 ... ( Z ^ 2 ) ) ) = ( Z ^ 2 )')
    hle2 = st([hle, hfz], 'breqtrd', '( # ` %s ) <_ ( Z ^ 2 )' % RABY)
    hrre = st([st([rabfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RABY)], 'nn0red',
              '( # ` %s ) e. RR' % RABY)
    mulle = st([st([st([hrre, z2re, st([y3re, y3ge], 'jca',
                                       '( %s e. RR /\ 0 <_ %s )' % (Y3, Y3))], '3jca',
                       '( ( # ` %s ) e. RR /\ ( Z ^ 2 ) e. RR /\ '
                       '( %s e. RR /\ 0 <_ %s ) )' % (RABY, Y3, Y3)), hle2], 'jca',
                   '( ( ( # ` %s ) e. RR /\ ( Z ^ 2 ) e. RR /\ '
                   '( %s e. RR /\ 0 <_ %s ) ) /\ ( # ` %s ) <_ ( Z ^ 2 ) )'
                   % (RABY, Y3, Y3, RABY)), w.inst('lemul1a')], 'syl',
               '( ( # ` %s ) x. %s ) <_ ( ( Z ^ 2 ) x. %s )' % (RABY, Y3, Y3))
    # ( Z ^ 2 ) x. ( ( Z ^ 2 ) ^ 3 ) = ( ( Z ^ 2 ) ^ 4 )
    z2cc = st([z2re], 'recnd', '( Z ^ 2 ) e. CC')
    ep = st([z2cc, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0'), w.inst('expp1')],
            'syl2anc',
            '( ( Z ^ 2 ) ^ ( 3 + 1 ) ) = ( %s x. ( Z ^ 2 ) )' % Y3)
    e4 = st([st([w.s([], '3p1e4', '( 3 + 1 ) = 4')], 'a1i', '( 3 + 1 ) = 4')], 'oveq2d',
            '( ( Z ^ 2 ) ^ ( 3 + 1 ) ) = %s' % Y4)
    z8eq = st([st([z2cc, st([y3re], 'recnd', '%s e. CC' % Y3)], 'mulcomd',
                  '( ( Z ^ 2 ) x. %s ) = ( %s x. ( Z ^ 2 ) )' % (Y3, Y3)),
               st([st([ep], 'eqcomd', '( %s x. ( Z ^ 2 ) ) = ( ( Z ^ 2 ) ^ ( 3 + 1 ) )' % Y3),
                   e4], 'eqtrd', '( %s x. ( Z ^ 2 ) ) = %s' % (Y3, Y4))], 'eqtrd',
              '( ( Z ^ 2 ) x. %s ) = %s' % (Y3, Y4))
    mulle2 = st([mulle, z8eq], 'breqtrd', '( ( # ` %s ) x. %s ) <_ %s' % (RABY, Y3, Y4))
    consty2 = st([st([ssy], 'eqcomd',
                     'sum_ d e. %s if ( d <_ Y , %s , 0 ) = '
                     'sum_ d e. %s if ( d <_ Y , %s , 0 )' % (DVP, Y3, RABY, Y3)),
                  consty], 'eqtrd',
                 'sum_ d e. %s if ( d <_ Y , %s , 0 ) = ( ( # ` %s ) x. %s )'
                 % (DVP, Y3, RABY, Y3))
    fin2 = st([consty2, mulle2], 'eqbrtrd',
              'sum_ d e. %s if ( d <_ Y , %s , 0 ) <_ %s' % (DVP, Y3, Y4))
    errre = st([dvfin, ifbre], 'fsumrecl', '%s e. RR' % ERR)
    cre = st([dvfin, ifyre], 'fsumrecl',
             'sum_ d e. %s if ( d <_ Y , %s , 0 ) e. RR' % (DVP, Y3))
    z8re = st([z2re, st([w.s([], '4nn0', '4 e. NN0')], 'a1i', '4 e. NN0')], 'reexpcld',
              '%s e. RR' % Y4)
    w.qed([errre, st([errre, cre, z8re, sumle, fin2], 'letrd', '%s <_ %s' % (ERR, Y4))],
          'jca', '( %s -> ( %s e. RR /\\ %s <_ %s ) )' % (TC, ERR, ERR, Y4))
    return w


ALL = {'twinerr': twinerr}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
