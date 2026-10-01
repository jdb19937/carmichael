"""Sortie v4a: the twin-type sieve upper bound (the sortie's headline)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import mkst
from cl import lift
import num
import v4a_sh as SHM
from v4a_asm import T1, ZS, US, B5
from v4a_v import VV
from v4a_arc import C2, K2048, LT, LTS, PH, RSQ, RR_


def subz(t):
    return ' '.join(ZS if x == 'Z' else x for x in t.split())


PPI = subz(SHM.PP)
AAI = SHM.AAS
WWI = SHM.WWS
TBI = subz(SHM.TBI)
SHI = subz(SHM.SHI)
Y2 = '( %s ^ 2 )' % ZS
DVPI = '{ x e. NN | x || %s }' % PPI
SSI = ('sum_ l e. %s if ( ( l ^ 2 ) <_ %s , ( ( %s ` l ) x. prod_ q e. '
       '{ r e. Prime | r || l } ( 1 / ( 1 - ( %s ` q ) ) ) ) , 0 )'
       % (DVPI, Y2, VV, VV))
SFI = 'sum_ n e. %s if ( ( %s gcd n ) = 1 , ( %s ` n ) , 0 )' % (AAI, PPI, WWI)
ERRI = ('sum_ d e. %s if ( d <_ %s , ( ( 3 ^ ( # ` { r e. Prime | r || d } ) ) x. '
        '( abs ` ( sum_ n e. %s if ( d || n , ( %s ` n ) , 0 ) - ( ( %s ` d ) x. T ) ) ) ) , 0 )'
        % (DVPI, Y2, AAI, WWI, VV))
CNTI = '( # ` { v e. ( 1 ... T ) | ( v e. Prime /\\ ( ( M x. v ) + 1 ) e. Prime ) } )'
TZI = 'A. y e. Prime ( y || %s -> y <_ %s )' % (PPI, ZS)
TCI = ('( %s /\\ ( ( T e. NN0 /\\ T = T ) /\\ ( %s = %s /\\ %s = %s ) ) )'
       % (TBI, AAI, AAI, WWI, WWI))
GAMI = '( ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) x. ( log ` %s ) )' % US
Y4 = '( %s ^ 4 )' % Y2
EEI = '( %s + %s )' % (Y4, ZS)
AF = '( M e. NN /\\ T e. ( ZZ>= ` %s ) )' % B5
GOAL = '( ( ( %s x. %s ) x. T ) / %s )' % (C2, RSQ, LTS)


def twinsvx():
    w = WS('twinsvx', 'The twin-type sieve upper bound with explicit constants: the number of '
                      'primes q up to T with M q + 1 prime is at most C times ( M / phi M ) '
                      'squared times T over the square of the logarithm of T.')
    st = mkst(w, AF)
    mnn = st([], 'simpl', 'M e. NN')
    tuz = st([], 'simpr', 'T e. ( ZZ>= ` %s )' % B5)
    sqf = st([tuz, w.inst('twinsqf')], 'syl',
             '( ( %s e. NN /\\ T e. NN0 /\\ 2 <_ T ) /\\ '
             '( %s <_ ( ; ; ; 1 0 2 4 x. ( log ` %s ) ) /\\ %s <_ ( ; 6 4 x. %s ) ) /\\ '
             '( ( %s + %s ) <_ ( 2 x. %s ) /\\ ( %s ^ 2 ) <_ T /\\ %s e. NN0 ) )'
             % (ZS, LT, US, LTS, T1, Y4, ZS, T1, T1, T1))
    c1 = st([sqf], 'simp1d', '( %s e. NN /\\ T e. NN0 /\\ 2 <_ T )' % ZS)
    c2p = st([sqf], 'simp2d',
             '( %s <_ ( ; ; ; 1 0 2 4 x. ( log ` %s ) ) /\\ %s <_ ( ; 6 4 x. %s ) )'
             % (LT, US, LTS, T1))
    c3 = st([sqf], 'simp3d',
            '( ( %s + %s ) <_ ( 2 x. %s ) /\\ ( %s ^ 2 ) <_ T /\\ %s e. NN0 )'
            % (Y4, ZS, T1, T1, T1))
    znn = st([c1], 'simp1d', '%s e. NN' % ZS)
    tn0 = st([c1], 'simp2d', 'T e. NN0')
    tge2 = st([c1], 'simp3d', '2 <_ T')
    ltle = st([c2p], 'simpld', '%s <_ ( ; ; ; 1 0 2 4 x. ( log ` %s ) )' % (LT, US))
    ltsle = st([c2p], 'simprd', '%s <_ ( ; 6 4 x. %s )' % (LTS, T1))
    eqle = st([c3], 'simp1d', '( %s + %s ) <_ ( 2 x. %s )' % (Y4, ZS, T1))
    t1sq = st([c3], 'simp2d', '( %s ^ 2 ) <_ T' % T1)
    t1n0 = st([c3], 'simp3d', '%s e. NN0' % T1)
    zn0 = st([znn], 'nnnn0d', '%s e. NN0' % ZS)
    zre = st([znn], 'nnred', '%s e. RR' % ZS)
    t1re = st([t1n0], 'nn0red', '%s e. RR' % T1)
    t1ge = st([t1n0], 'nn0ge0d', '0 <_ %s' % T1)
    # the sieve instance
    tbi = st([st([mnn, tn0, znn], '3jca', '( M e. NN /\\ T e. NN0 /\\ %s e. NN )' % ZS),
              w.inst('twinsh')], 'syl', TBI)
    tci = st([tbi, st([st([tn0, st([], 'eqidd', 'T = T')], 'jca',
                          '( T e. NN0 /\\ T = T )'),
                       st([st([], 'eqidd', '%s = %s' % (AAI, AAI)),
                           st([], 'eqidd', '%s = %s' % (WWI, WWI))], 'jca',
                          '( %s = %s /\\ %s = %s )' % (AAI, AAI, WWI, WWI))], 'jca',
                      '( ( T e. NN0 /\\ T = T ) /\\ ( %s = %s /\\ %s = %s ) )'
                      % (AAI, AAI, WWI, WWI))], 'jca', TCI)
    shi = st([tbi], 'simp1d', SHI)
    tzi = st([zn0, w.inst('twinpz')], 'syl', TZI)
    cnt = st([st([tci, tzi], 'jca', '( %s /\\ %s )' % (TCI, TZI)), w.inst('twincnt')], 'syl',
             '( %s e. RR /\\ %s e. RR /\\ %s <_ ( %s + %s ) )' % (SFI, CNTI, CNTI, SFI, ZS))
    sfre = st([cnt], 'simp1d', '%s e. RR' % SFI)
    cntre = st([cnt], 'simp2d', '%s e. RR' % CNTI)
    cntle = st([cnt], 'simp3d', '%s <_ ( %s + %s )' % (CNTI, SFI, ZS))
    sieve = st([shi, w.inst('selbsieve')], 'syl',
               '%s <_ ( ( T / %s ) + %s )' % (SFI, SSI, ERRI))
    errp = st([tci, w.inst('twinerr')], 'syl', '( %s e. RR /\\ %s <_ %s )' % (ERRI, ERRI, Y4))
    errre = st([errp], 'simpld', '%s e. RR' % ERRI)
    errle = st([errp], 'simprd', '%s <_ %s' % (ERRI, Y4))
    ssge = st([tbi, w.inst('twinssge')], 'syl', '( %s ^ 2 ) <_ %s' % (GAMI, SSI))
    ssrp = st([shi, w.inst('ssrp')], 'syl', '%s e. RR+' % SSI)
    ssre = st([ssrp], 'rpred', '%s e. RR' % SSI)
    sspos = st([ssrp], 'rpgt0d', '0 < %s' % SSI)
    # ---- the count bound in twinarc's shape
    qtre = st([st([tn0], 'nn0red', 'T e. RR'), ssrp], 'rerpdivcld', '( T / %s ) e. RR' % SSI)
    y4re = st([st([zre, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'reexpcld',
                  '%s e. RR' % Y2),
               st([num.fact(w, '4', 'NN0')], 'a1i', '4 e. NN0')], 'reexpcld', '%s e. RR' % Y4)
    eere = st([y4re, zre], 'readdcld', '%s e. RR' % EEI)
    sf2 = st([sfre, st([qtre, errre], 'readdcld', '( ( T / %s ) + %s ) e. RR' % (SSI, ERRI)),
              st([qtre, y4re], 'readdcld', '( ( T / %s ) + %s ) e. RR' % (SSI, Y4)), sieve,
              st([errre, y4re, qtre, errle], 'leadd2dd',
                 '( ( T / %s ) + %s ) <_ ( ( T / %s ) + %s )' % (SSI, ERRI, SSI, Y4))],
             'letrd', '%s <_ ( ( T / %s ) + %s )' % (SFI, SSI, Y4))
    add1 = st([sfre, st([qtre, y4re], 'readdcld', '( ( T / %s ) + %s ) e. RR' % (SSI, Y4)),
               zre, sf2], 'leadd1dd',
              '( %s + %s ) <_ ( ( ( T / %s ) + %s ) + %s )' % (SFI, ZS, SSI, Y4, ZS))
    assoc = st([st([qtre], 'recnd', '( T / %s ) e. CC' % SSI),
                st([y4re], 'recnd', '%s e. CC' % Y4), st([zre], 'recnd', '%s e. CC' % ZS)],
               'addassd',
               '( ( ( T / %s ) + %s ) + %s ) = ( ( T / %s ) + %s )' % (SSI, Y4, ZS, SSI, EEI))
    cntb = st([cntre, st([sfre, zre], 'readdcld', '( %s + %s ) e. RR' % (SFI, ZS)),
               st([qtre, eere], 'readdcld', '( ( T / %s ) + %s ) e. RR' % (SSI, EEI)), cntle,
               st([add1, assoc], 'breqtrd',
                  '( %s + %s ) <_ ( ( T / %s ) + %s )' % (SFI, ZS, SSI, EEI))], 'letrd',
              '%s <_ ( ( T / %s ) + %s )' % (CNTI, SSI, EEI))
    # ---- the bounding-sum lower bound in twinarc's shape
    zge = st([zn0], 'nn0ge0d', '0 <_ %s' % ZS)
    flz = st([st([zre, zge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (ZS, ZS)),
              w.inst('flsqrt2')], 'syl',
             '( %s e. NN0 /\ ( %s ^ 2 ) <_ %s /\ %s < ( ( %s + 1 ) ^ 2 ) )'
             % (US, US, ZS, ZS, US))
    un0 = st([flz], 'simp1d', '%s e. NN0' % US)
    ure = st([un0], 'nn0red', '%s e. RR' % US)
    sq1e = st([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1')
    z1 = st([znn, w.inst('nnge1')], 'syl', '1 <_ %s' % ZS)
    onesq = st([sq1e, z1], 'eqbrtrd', '( 1 ^ 2 ) <_ %s' % ZS)
    uge1 = st([st([zre, st([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0'), onesq], '3jca',
                  '( %s e. RR /\ 1 e. NN0 /\ ( 1 ^ 2 ) <_ %s )' % (ZS, ZS)),
               w.inst('flsqge')], 'syl', '1 <_ %s' % US)
    lure = st([st([st([un0, uge1], 'jca', '( %s e. NN0 /\ 1 <_ %s )' % (US, US)),
                   st([w.s([], 'elnnnn0c',
                           '( %s e. NN <-> ( %s e. NN0 /\ 1 <_ %s ) )' % (US, US, US))], 'a1i',
                      '( %s e. NN <-> ( %s e. NN0 /\ 1 <_ %s ) )' % (US, US, US))], 'mpbird',
                  '%s e. NN' % US)], 'nnrpd', '%s e. RR+' % US)
    lure2 = st([lure, w.inst('relogcl')], 'syl', '( log ` %s ) e. RR' % US)
    luge = st([st([ure, uge1], 'jca', '( %s e. RR /\ 1 <_ %s )' % (US, US)),
               w.inst('logge0')], 'syl', '0 <_ ( log ` %s )' % US)
    m2nn = st([st([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN'), mnn], 'nnmulcld',
              '( 2 x. M ) e. NN')
    ph2nn = st([m2nn, w.inst('phicl')], 'syl', '( phi ` ( 2 x. M ) ) e. NN')
    ph2rp = st([st([ph2nn], 'nnrpd', '( phi ` ( 2 x. M ) ) e. RR+'),
                st([m2nn], 'nnrpd', '( 2 x. M ) e. RR+')], 'rpdivcld',
               '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) e. RR+')
    ph2re = st([ph2rp], 'rpred', '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) e. RR')
    ph2ge = st([ph2rp], 'rpge0d', '0 <_ ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )')
    gamre = st([ph2re, lure2], 'remulcld', '%s e. RR' % GAMI)
    gamge = st([ph2re, lure2, ph2ge, luge], 'mulge0d', '0 <_ %s' % GAMI)
    # PH <_ ( 2 x. PH2 )
    phinn = st([mnn, w.inst('phicl')], 'syl', '( phi ` M ) e. NN')
    mrp = st([mnn], 'nnrpd', 'M e. RR+')
    phile = st([mnn, w.inst('phi2mule')], 'syl', '( phi ` M ) <_ ( phi ` ( 2 x. M ) )')
    dv1 = st([st([phinn], 'nnred', '( phi ` M ) e. RR'),
              st([ph2nn], 'nnred', '( phi ` ( 2 x. M ) ) e. RR'), mrp, phile], 'lediv1dd',
             '%s <_ ( ( phi ` ( 2 x. M ) ) / M )' % PH)
    twocc = st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'recnd', '2 e. CC')
    dass = st([twocc, st([st([ph2nn], 'nnred', '( phi ` ( 2 x. M ) ) e. RR')], 'recnd',
                         '( phi ` ( 2 x. M ) ) e. CC'),
               st([st([m2nn], 'nnrpd', '( 2 x. M ) e. RR+')], 'rpcnd', '( 2 x. M ) e. CC'),
               st([st([m2nn], 'nnrpd', '( 2 x. M ) e. RR+')], 'rpne0d', '( 2 x. M ) =/= 0')],
              'divassd',
              '( ( 2 x. ( phi ` ( 2 x. M ) ) ) / ( 2 x. M ) ) = '
              '( 2 x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) )')
    twone = st([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0')
    dc5 = st([st([st([st([ph2nn], 'nnred', '( phi ` ( 2 x. M ) ) e. RR')], 'recnd',
                     '( phi ` ( 2 x. M ) ) e. CC'),
                  st([st([mrp], 'rpcnd', 'M e. CC'), st([mrp], 'rpne0d', 'M =/= 0')], 'jca',
                     '( M e. CC /\ M =/= 0 )'),
                  st([twocc, twone], 'jca', '( 2 e. CC /\ 2 =/= 0 )')], '3jca',
                 '( ( phi ` ( 2 x. M ) ) e. CC /\ ( M e. CC /\ M =/= 0 ) /\ '
                 '( 2 e. CC /\ 2 =/= 0 ) )'), w.inst('divcan5')], 'syl',
             '( ( 2 x. ( phi ` ( 2 x. M ) ) ) / ( 2 x. M ) ) = '
             '( ( phi ` ( 2 x. M ) ) / M )')
    ph2eq = st([st([dass], 'eqcomd',
                   '( 2 x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) ) = '
                   '( ( 2 x. ( phi ` ( 2 x. M ) ) ) / ( 2 x. M ) )'), dc5], 'eqtrd',
               '( 2 x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) ) = '
               '( ( phi ` ( 2 x. M ) ) / M )')
    phle = st([dv1, st([ph2eq], 'eqcomd',
                       '( ( phi ` ( 2 x. M ) ) / M ) = '
                       '( 2 x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) )')], 'breqtrd',
              '%s <_ ( 2 x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) )' % PH)
    # ( PH x. LT ) <_ ( 2048 x. GAM )
    phrp = st([st([phinn], 'nnrpd', '( phi ` M ) e. RR+'), mrp], 'rpdivcld', '%s e. RR+' % PH)
    phre = st([phrp], 'rpred', '%s e. RR' % PH)
    phge = st([phrp], 'rpge0d', '0 <_ %s' % PH)
    tposi = st([st([], '0red', '0 e. RR'), st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
                st([tn0], 'nn0red', 'T e. RR'),
                st([w.s([], '2pos', '0 < 2')], 'a1i', '0 < 2'), tge2], 'ltletrd', '0 < T')
    trp = st([st([tn0], 'nn0red', 'T e. RR'), tposi], 'elrpd', 'T e. RR+')
    ltre = st([trp, w.inst('relogcl')], 'syl', '%s e. RR' % LT)
    ltge = st([st([st([tn0], 'nn0red', 'T e. RR'),
                   st([st([], '1red', '1 e. RR'),
                       st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
                       st([tn0], 'nn0red', 'T e. RR'),
                       st([w.s([], '1le2', '1 <_ 2')], 'a1i', '1 <_ 2'), tge2], 'letrd',
                      '1 <_ T')], 'jca', '( T e. RR /\ 1 <_ T )'), w.inst('logge0')], 'syl',
              '0 <_ %s' % LT)
    k1024 = '; ; ; 1 0 2 4'
    k1re = st([num.fact(w, k1024, 'RR')], 'a1i', '%s e. RR' % k1024)
    tw2 = st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), ph2re], 'remulcld',
             '( 2 x. %s ) e. RR' % '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )')
    k1l = st([k1re, lure2], 'remulcld', '( %s x. ( log ` %s ) ) e. RR' % (k1024, US))
    prd = st([st([st([st([phre, phge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (PH, PH)),
                     tw2], 'jca',
                    '( ( %s e. RR /\ 0 <_ %s ) /\ ( 2 x. %s ) e. RR )'
                    % (PH, PH, '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )')),
                  st([st([ltre, ltge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (LT, LT)),
                      k1l], 'jca',
                     '( ( %s e. RR /\ 0 <_ %s ) /\ ( %s x. ( log ` %s ) ) e. RR )'
                     % (LT, LT, k1024, US))], 'jca',
                 '( ( ( %s e. RR /\ 0 <_ %s ) /\ ( 2 x. %s ) e. RR ) /\ '
                 '( ( %s e. RR /\ 0 <_ %s ) /\ ( %s x. ( log ` %s ) ) e. RR ) )'
                 % (PH, PH, '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )', LT, LT, k1024, US)),
              w.inst('lemul12a')], 'syl',
             '( ( %s <_ ( 2 x. %s ) /\ %s <_ ( %s x. ( log ` %s ) ) ) -> '
             '( %s x. %s ) <_ ( ( 2 x. %s ) x. ( %s x. ( log ` %s ) ) ) )'
             % (PH, '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )', LT, k1024, US, PH, LT,
                '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )', k1024, US))
    prd2 = st([prd, st([phle, ltle], 'jca',
                       '( %s <_ ( 2 x. %s ) /\ %s <_ ( %s x. ( log ` %s ) ) )'
                       % (PH, '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )', LT, k1024, US))],
              'mpd',
              '( %s x. %s ) <_ ( ( 2 x. %s ) x. ( %s x. ( log ` %s ) ) )'
              % (PH, LT, '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )', k1024, US))
    m4 = st([twocc, st([ph2re], 'recnd', '%s e. CC' % '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )'),
             st([k1re], 'recnd', '%s e. CC' % k1024),
             st([lure2], 'recnd', '( log ` %s ) e. CC' % US)], 'mul4d',
            '( ( 2 x. %s ) x. ( %s x. ( log ` %s ) ) ) = ( ( 2 x. %s ) x. %s )'
            % ('( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )', k1024, US, k1024, GAMI))
    k2eq = st([st([num.mul_nat(w, 2, 1024)], 'a1i', '( 2 x. %s ) = %s' % (k1024, K2048))],
              'oveq1d', '( ( 2 x. %s ) x. %s ) = ( %s x. %s )' % (k1024, GAMI, K2048, GAMI))
    key = st([prd2, st([m4, k2eq], 'eqtrd',
                       '( ( 2 x. %s ) x. ( %s x. ( log ` %s ) ) ) = ( %s x. %s )'
                       % ('( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )', k1024, US, K2048, GAMI))],
             'breqtrd', '( %s x. %s ) <_ ( %s x. %s )' % (PH, LT, K2048, GAMI))
    # ---- twinarc
    arc = st([st([mnn, tn0, tge2], '3jca', '( M e. NN /\ T e. NN0 /\ 2 <_ T )'),
                 st([st([cntre, ssre, sspos], '3jca',
                        '( %s e. RR /\ %s e. RR /\ 0 < %s )' % (CNTI, SSI, SSI)),
                     st([eere, gamre, gamge], '3jca',
                        '( %s e. RR /\ %s e. RR /\ 0 <_ %s )' % (EEI, GAMI, GAMI)),
                     st([t1re, t1ge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (T1, T1))], '3jca',
                    '( ( %s e. RR /\ %s e. RR /\ 0 < %s ) /\ '
                    '( %s e. RR /\ %s e. RR /\ 0 <_ %s ) /\ ( %s e. RR /\ 0 <_ %s ) )'
                    % (CNTI, SSI, SSI, EEI, GAMI, GAMI, T1, T1)),
                 st([st([cntb, eqle], 'jca',
                        '( %s <_ ( ( T / %s ) + %s ) /\ %s <_ ( 2 x. %s ) )'
                        % (CNTI, SSI, EEI, EEI, T1)),
                     st([ssge, key], 'jca',
                        '( ( %s ^ 2 ) <_ %s /\ ( %s x. %s ) <_ ( %s x. %s ) )'
                        % (GAMI, SSI, PH, LT, K2048, GAMI)),
                     st([ltsle, t1sq], 'jca',
                        '( %s <_ ( ; 6 4 x. %s ) /\ ( %s ^ 2 ) <_ T )' % (LTS, T1, T1))],
                    '3jca',
                    '( ( %s <_ ( ( T / %s ) + %s ) /\ %s <_ ( 2 x. %s ) ) /\ '
                    '( ( %s ^ 2 ) <_ %s /\ ( %s x. %s ) <_ ( %s x. %s ) ) /\ '
                    '( %s <_ ( ; 6 4 x. %s ) /\ ( %s ^ 2 ) <_ T ) )'
                    % (CNTI, SSI, EEI, EEI, T1, GAMI, SSI, PH, LT, K2048, GAMI, LTS, T1, T1))],
                '3jca',
                '( ( M e. NN /\ T e. NN0 /\ 2 <_ T ) /\ '
                '( ( %s e. RR /\ %s e. RR /\ 0 < %s ) /\ '
                '( %s e. RR /\ %s e. RR /\ 0 <_ %s ) /\ ( %s e. RR /\ 0 <_ %s ) ) /\ '
                '( ( %s <_ ( ( T / %s ) + %s ) /\ %s <_ ( 2 x. %s ) ) /\ '
                '( ( %s ^ 2 ) <_ %s /\ ( %s x. %s ) <_ ( %s x. %s ) ) /\ '
                '( %s <_ ( ; 6 4 x. %s ) /\ ( %s ^ 2 ) <_ T ) ) )'
                % (CNTI, SSI, SSI, EEI, GAMI, GAMI, T1, T1, CNTI, SSI, EEI, EEI, T1,
                   GAMI, SSI, PH, LT, K2048, GAMI, LTS, T1, T1))
    w.qed([arc, w.inst('twinarc')], 'syl', '( %s -> %s <_ %s )' % (AF, CNTI, GOAL))
    return w


ALL = {'twinsvx': twinsvx}



def BODYT(c, n, z):
    return ('( # ` { v e. ( 1 ... %s ) | ( v e. Prime /\\ ( ( %s x. v ) + 1 ) e. Prime ) } ) '
            '<_ ( ( ( %s x. ( ( %s / ( phi ` %s ) ) ^ 2 ) ) x. %s ) / ( ( log ` %s ) ^ 2 ) )'
            % (z, n, c, n, n, z, z))


def INNER(c, m):
    return 'A. n e. NN A. z e. ( ZZ>= ` %s ) %s' % (m, BODYT(c, 'n', 'z'))


def OUTER(c):
    return '( 0 < %s /\\ E. m e. NN %s )' % (c, INNER(c, 'm'))


def twinsv():
    w = WS('twinsv', 'The twin-type sieve upper bound: there are absolute constants C and t0 '
                     'such that for every m and every t at least t0 the number of primes q '
                     'up to t with m q + 1 prime is at most C ( m / phi m ) squared times t '
                     'over the square of the logarithm of t.')
    h = w.s([], 'twinsvx',
            '( ( n e. NN /\\ z e. ( ZZ>= ` %s ) ) -> %s )' % (B5, BODYT(C2, 'n', 'z')))
    r1 = w.s([h], 'ralrimiva',
             '( n e. NN -> A. z e. ( ZZ>= ` %s ) %s )' % (B5, BODYT(C2, 'n', 'z')))
    r2 = w.s([r1], 'rgen', INNER(C2, B5))
    idm = w.s([], 'id', '( m = %s -> m = %s )' % (B5, B5))
    sb1, new1 = w.wcongr(INNER(C2, 'm'), {'m': B5}, 'm = %s' % B5, {'m': idm})
    two0 = w.s([], '2nn0', '2 e. NN0')
    cur = w.s([], '2nn', '2 e. NN')
    BS = ['2']
    for k in range(5):
        nxt = '( %s ^ 2 )' % BS[-1]
        cur = w.s([cur, two0, w.inst('nnexpcl')], 'mp2an', '%s e. NN' % nxt)
        BS.append(nxt)
    ex1 = w.s([sb1], 'rspcev',
              '( ( %s e. NN /\\ %s ) -> E. m e. NN %s )' % (B5, new1, INNER(C2, 'm')))
    ex1b = w.s([w.s([cur, r2], 'pm3.2i', '( %s e. NN /\\ %s )' % (B5, new1)), ex1], 'ax-mp',
               'E. m e. NN %s' % INNER(C2, 'm'))
    c2pos = num.fact(w, C2, 'gt0')
    pair = w.s([c2pos, ex1b], 'pm3.2i', OUTER(C2))
    idc = w.s([], 'id', '( c = %s -> c = %s )' % (C2, C2))
    sb2, new2 = w.wcongr(OUTER('c'), {'c': C2}, 'c = %s' % C2, {'c': idc})
    c2re = num.fact(w, C2, 'RR')
    ex2 = w.s([sb2], 'rspcev',
              '( ( %s e. RR /\\ %s ) -> E. c e. RR %s )' % (C2, new2, OUTER('c')))
    w.qed([w.s([c2re, pair], 'pm3.2i', '( %s e. RR /\\ %s )' % (C2, new2)), ex2], 'ax-mp',
          'E. c e. RR %s' % OUTER('c'))
    return w


ALL['twinsv'] = twinsv

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
