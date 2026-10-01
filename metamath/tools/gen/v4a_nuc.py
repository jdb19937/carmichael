"""Sortie v4a: the inflated density sum is below the Selberg bounding sum."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import CS, DEN, mkst, csel
from cl import lift
from v4a_tb import SH, TMR, TRAL, TB, shparts

CSZ = CS('( 2 x. M )', 'Z')
DVP = '{ x e. NN | x || P }'


def GT(X):
    return ('( ( V ` %s ) x. prod_ q e. { r e. Prime | r || %s } ( 1 / ( 1 - ( V ` q ) ) ) )'
            % (X, X))


SS = 'sum_ l e. %s if ( ( l ^ 2 ) <_ Y , %s , 0 )' % (DVP, GT('l'))
PGJ = '( P gcd j )'


def twinnuc():
    w = WS('twinnuc', 'The sum of the inflated density over the integers up to Z coprime to '
                      'twice the multiplier is at most the Selberg bounding sum.')
    st = mkst(w, TB)
    tmid = st([], 'id', TB)
    sh = shparts(w, st, st([], 'simp1', SH))
    mnn = st([st([], 'simp2', TMR)], 'simp1d', 'M e. NN')
    znn = st([st([], 'simp2', TMR)], 'simp2d', 'Z e. NN')
    yeq = st([st([], 'simp2', TMR)], 'simp3d', 'Y = ( Z ^ 2 )')
    pnn = sh['pnn']
    pz = st([pnn], 'nnzd', 'P e. ZZ')
    dvfin = st([pnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    csfin = st([st([], 'fzfid', '( 1 ... Z ) e. Fin'),
                st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % CSZ)], 'a1i',
                   '%s C_ ( 1 ... Z )' % CSZ)], 'ssfid', '%s e. Fin' % CSZ)
    # each element of CSZ has its gcd with P in DV( P )
    AJ = '( %s /\\ j e. %s )' % (TB, CSZ)
    sj = mkst(w, AJ)
    jcs = csel(w, 'j', '( 2 x. M )', 'Z')
    jmem = sj([sj([jcs], 'a1i',
                  '( j e. %s <-> ( j e. ( 1 ... Z ) /\\ ( j gcd ( 2 x. M ) ) = 1 ) )' % CSZ),
               sj([], 'simpr', 'j e. %s' % CSZ)], 'mpbid',
              '( j e. ( 1 ... Z ) /\\ ( j gcd ( 2 x. M ) ) = 1 )')
    jfz = sj([jmem], 'simpld', 'j e. ( 1 ... Z )')
    jnn = sj([jfz, w.inst('elfznn')], 'syl', 'j e. NN')
    jlez = sj([jfz, w.inst('elfzle2')], 'syl', 'j <_ Z')
    gnn = sj([lift(w, pnn, AJ), jnn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % PGJ)
    gpair = sj([lift(w, pz, AJ), sj([jnn], 'nnzd', 'j e. ZZ'), w.inst('gcddvds')], 'syl2anc',
               '( %s || P /\\ %s || j )' % (PGJ, PGJ))
    gdp = sj([gpair], 'simpld', '%s || P' % PGJ)
    eldv = w.s([w.s([], 'breq1', '( x = %s -> ( x || P <-> %s || P ) )' % (PGJ, PGJ))], 'elrab',
               '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (PGJ, DVP, PGJ, PGJ))
    gin = sj([sj([gnn, gdp], 'jca', '( %s e. NN /\\ %s || P )' % (PGJ, PGJ)),
              sj([eldv], 'a1i',
                 '( %s e. %s <-> ( %s e. NN /\\ %s || P ) )' % (PGJ, DVP, PGJ, PGJ))],
             'mpbird', '%s e. %s' % (PGJ, DVP))
    denrp = sj([sj([sj([sj([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), jnn,
                       w.inst('sgmnncl')], 'syl2anc', '( 0 sigma j ) e. NN')], 'nnrpd',
                   '( 0 sigma j ) e. RR+'), sj([jnn], 'nnrpd', 'j e. RR+')], 'rpdivcld',
               '%s e. RR+' % DEN('j'))
    dencc = sj([denrp], 'rpcnd', '%s e. CC' % DEN('j'))
    sit = sj([w.s([], 'eqidd', '( l = %s -> %s = %s )' % (PGJ, DEN('j'), DEN('j'))),
              lift(w, dvfin, AJ), gin, dencc], 'sumite',
             'sum_ l e. %s if ( l = %s , %s , 0 ) = %s' % (DVP, PGJ, DEN('j'), DEN('j')))
    ins = st([sj([sit], 'eqcomd',
                 '%s = sum_ l e. %s if ( l = %s , %s , 0 )' % (DEN('j'), DVP, PGJ, DEN('j')))],
             'sumeq2dv',
             'sum_ j e. %s %s = sum_ j e. %s sum_ l e. %s if ( l = %s , %s , 0 )'
             % (CSZ, DEN('j'), CSZ, DVP, PGJ, DEN('j')))
    AJL = '( %s /\\ ( j e. %s /\\ l e. %s ) )' % (TB, CSZ, DVP)
    sjl = mkst(w, AJL)
    jl1 = sjl([sjl([], 'simpr', '( j e. %s /\\ l e. %s )' % (CSZ, DVP))], 'simpld',
              'j e. %s' % CSZ)
    jlnn = sjl([sjl([sjl([sjl([jcs], 'a1i',
                              '( j e. %s <-> ( j e. ( 1 ... Z ) /\\ ( j gcd ( 2 x. M ) ) = 1 ) )'
                              % CSZ), jl1], 'mpbid',
                         '( j e. ( 1 ... Z ) /\\ ( j gcd ( 2 x. M ) ) = 1 )')], 'simpld',
                    'j e. ( 1 ... Z )'), w.inst('elfznn')], 'syl', 'j e. NN')
    sgnn = sjl([sjl([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), jlnn,
                w.inst('sgmnncl')], 'syl2anc', '( 0 sigma j ) e. NN')
    sgrp = sjl([sgnn], 'nnrpd', '( 0 sigma j ) e. RR+')
    jrp2 = sjl([jlnn], 'nnrpd', 'j e. RR+')
    denr = sjl([sgrp, jrp2], 'rpdivcld', '%s e. RR+' % DEN('j'))
    ifcc = sjl([denr], 'rpcnd', '%s e. CC' % DEN('j'))
    ifcc2 = sjl([ifcc, sjl([sjl([], '0red', '0 e. RR')], 'recnd', '0 e. CC')], 'ifcld',
                'if ( l = %s , %s , 0 ) e. CC' % (PGJ, DEN('j')))
    com = st([csfin, dvfin, ifcc2], 'fsumcom',
             'sum_ j e. %s sum_ l e. %s if ( l = %s , %s , 0 ) = '
             'sum_ l e. %s sum_ j e. %s if ( l = %s , %s , 0 )'
             % (CSZ, DVP, PGJ, DEN('j'), DVP, CSZ, PGJ, DEN('j')))
    lhs = st([ins, com], 'eqtrd',
             'sum_ j e. %s %s = sum_ l e. %s sum_ j e. %s if ( l = %s , %s , 0 )'
             % (CSZ, DEN('j'), DVP, CSZ, PGJ, DEN('j')))
    # ---- the per-l bound
    AL = '( %s /\ l e. %s )' % (TB, DVP)
    sl = mkst(w, AL)
    ldv = w.s([w.s([], 'breq1', '( x = l -> ( x || P <-> l || P ) )')], 'elrab',
              '( l e. %s <-> ( l e. NN /\ l || P ) )' % DVP)
    lmem = sl([sl([ldv], 'a1i', '( l e. %s <-> ( l e. NN /\ l || P ) )' % DVP),
               sl([], 'simpr', 'l e. %s' % DVP)], 'mpbid', '( l e. NN /\ l || P )')
    lnn = sl([lmem], 'simpld', 'l e. NN')
    ldp = sl([lmem], 'simprd', 'l || P')
    gtrp = sl([sl([lift(w, sh['sh'], AL), lmem], 'jca',
                  '( %s /\ ( l e. NN /\ l || P ) )' % SH), w.inst('gtrp')], 'syl',
              '%s e. RR+' % GT('l'))
    gtre = sl([gtrp], 'rpred', '%s e. RR' % GT('l'))
    ifre = sl([gtre, sl([], '0red', '0 e. RR')], 'ifcld',
              'if ( ( l ^ 2 ) <_ Y , %s , 0 ) e. RR' % GT('l'))
    ALJ = '( %s /\ j e. %s )' % (AL, CSZ)
    slj = mkst(w, ALJ)
    jljm = slj([slj([jcs], 'a1i',
                    '( j e. %s <-> ( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 ) )' % CSZ),
                slj([], 'simpr', 'j e. %s' % CSZ)], 'mpbid',
               '( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 )')
    jljfz = slj([jljm], 'simpld', 'j e. ( 1 ... Z )')
    jljnn = slj([jljfz, w.inst('elfznn')], 'syl', 'j e. NN')
    jljle = slj([jljfz, w.inst('elfzle2')], 'syl', 'j <_ Z')
    sgnn2 = slj([slj([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), jljnn,
                 w.inst('sgmnncl')], 'syl2anc', '( 0 sigma j ) e. NN')
    denre = slj([slj([sgnn2], 'nnred', '( 0 sigma j ) e. RR'),
                 slj([jljnn], 'nnrpd', 'j e. RR+')], 'rerpdivcld', '%s e. RR' % DEN('j'))
    ifre2 = slj([denre, slj([], '0red', '0 e. RR')], 'ifcld',
                'if ( l = %s , %s , 0 ) e. RR' % (PGJ, DEN('j')))
    innre = sl([lift(w, csfin, AL), ifre2], 'fsumrecl',
               'sum_ j e. %s if ( l = %s , %s , 0 ) e. RR' % (CSZ, PGJ, DEN('j')))
    # case ( l ^ 2 ) <_ Y
    AC1 = '( %s /\ ( l ^ 2 ) <_ Y )' % AL
    sc1 = mkst(w, AC1)
    fibl = sc1([sc1([lift(w, tmid, AC1), lift(w, lmem, AC1)], 'jca',
                    '( %s /\ ( l e. NN /\ l || P ) )' % TB), w.inst('twinfib')], 'syl',
               'sum_ j e. %s if ( l = %s , %s , 0 ) <_ %s' % (CSZ, PGJ, DEN('j'), GT('l')))
    rhs1 = sc1([sc1([], 'simpr', '( l ^ 2 ) <_ Y')], 'iftrued',
               'if ( ( l ^ 2 ) <_ Y , %s , 0 ) = %s' % (GT('l'), GT('l')))
    case1 = sc1([fibl, sc1([rhs1], 'eqcomd',
                           '%s = if ( ( l ^ 2 ) <_ Y , %s , 0 )' % (GT('l'), GT('l')))],
                'breqtrd',
                'sum_ j e. %s if ( l = %s , %s , 0 ) <_ if ( ( l ^ 2 ) <_ Y , %s , 0 )'
                % (CSZ, PGJ, DEN('j'), GT('l')))
    # case -. ( l ^ 2 ) <_ Y
    AC2 = '( %s /\ -. ( l ^ 2 ) <_ Y )' % AL
    sc2 = mkst(w, AC2)
    AC2J = '( %s /\ j e. %s )' % (AC2, CSZ)
    s2j = mkst(w, AC2J)
    s2jm = s2j([s2j([jcs], 'a1i',
                    '( j e. %s <-> ( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 ) )' % CSZ),
                s2j([], 'simpr', 'j e. %s' % CSZ)], 'mpbid',
               '( j e. ( 1 ... Z ) /\ ( j gcd ( 2 x. M ) ) = 1 )')
    s2jfz = s2j([s2jm], 'simpld', 'j e. ( 1 ... Z )')
    s2jnn = s2j([s2jfz, w.inst('elfznn')], 'syl', 'j e. NN')
    s2jle = s2j([s2jfz, w.inst('elfzle2')], 'syl', 'j <_ Z')
    AEQ = '( %s /\ l = %s )' % (AC2J, PGJ)
    seq = mkst(w, AEQ)
    gdj2 = seq([seq([lift(w, pz, AEQ), seq([lift(w, s2jnn, AEQ)], 'nnzd', 'j e. ZZ'),
                     w.inst('gcddvds')], 'syl2anc',
                    '( %s || P /\ %s || j )' % (PGJ, PGJ))], 'simprd', '%s || j' % PGJ)
    ldj = seq([seq([], 'simpr', 'l = %s' % PGJ), gdj2], 'eqbrtrd', 'l || j')
    llej = seq([seq([seq([lift(w, lnn, AEQ)], 'nnzd', 'l e. ZZ'), lift(w, s2jnn, AEQ),
                     w.inst('dvdsle')], 'syl2anc', '( l || j -> l <_ j )'), ldj], 'mpd',
               'l <_ j')
    llez = seq([seq([lift(w, lnn, AEQ)], 'nnred', 'l e. RR'),
                seq([lift(w, s2jnn, AEQ)], 'nnred', 'j e. RR'),
                seq([lift(w, znn, AEQ)], 'nnred', 'Z e. RR'), llej,
                lift(w, s2jle, AEQ)], 'letrd', 'l <_ Z')
    lsq = seq([seq([seq([seq([lift(w, lnn, AEQ)], 'nnred', 'l e. RR'),
                         seq([seq([lift(w, lnn, AEQ)], 'nnnn0d', 'l e. NN0')], 'nn0ge0d',
                             '0 <_ l')], 'jca', '( l e. RR /\ 0 <_ l )'),
                    seq([seq([lift(w, znn, AEQ)], 'nnred', 'Z e. RR'), llez], 'jca',
                        '( Z e. RR /\ l <_ Z )')], 'jca',
                   '( ( l e. RR /\ 0 <_ l ) /\ ( Z e. RR /\ l <_ Z ) )'),
               w.inst('le2sq2')], 'syl', '( l ^ 2 ) <_ ( Z ^ 2 )')
    lsqy = seq([lsq, seq([lift(w, yeq, AEQ)], 'eqcomd', '( Z ^ 2 ) = Y')], 'breqtrd',
               '( l ^ 2 ) <_ Y')
    nleq = s2j([lift(w, sc2([], 'simpr', '-. ( l ^ 2 ) <_ Y'), AC2J), lsqy], 'mtand',
               '-. l = %s' % PGJ)
    zb = s2j([nleq], 'iffalsed', 'if ( l = %s , %s , 0 ) = 0' % (PGJ, DEN('j')))
    zsum = sc2([sc2([zb], 'sumeq2dv',
                    'sum_ j e. %s if ( l = %s , %s , 0 ) = sum_ j e. %s 0'
                    % (CSZ, PGJ, DEN('j'), CSZ)),
                sc2([sc2([lift(w, csfin, AC2)], 'olcd',
                         '( %s C_ ( ZZ>= ` m ) \/ %s e. Fin )' % (CSZ, CSZ)),
                     w.inst('sumz')], 'syl', 'sum_ j e. %s 0 = 0' % CSZ)], 'eqtrd',
               'sum_ j e. %s if ( l = %s , %s , 0 ) = 0' % (CSZ, PGJ, DEN('j')))
    rhs2 = sc2([sc2([], 'simpr', '-. ( l ^ 2 ) <_ Y')], 'iffalsed',
               'if ( ( l ^ 2 ) <_ Y , %s , 0 ) = 0' % GT('l'))
    case2 = sc2([zsum, sc2([sc2([sc2([], '0red', '0 e. RR')], 'leidd', '0 <_ 0'),
                            sc2([rhs2], 'eqcomd',
                                '0 = if ( ( l ^ 2 ) <_ Y , %s , 0 )' % GT('l'))], 'breqtrd',
                           '0 <_ if ( ( l ^ 2 ) <_ Y , %s , 0 )' % GT('l'))], 'eqbrtrd',
                'sum_ j e. %s if ( l = %s , %s , 0 ) <_ if ( ( l ^ 2 ) <_ Y , %s , 0 )'
                % (CSZ, PGJ, DEN('j'), GT('l')))
    both = sl([case1, case2], 'pm2.61dan',
              'sum_ j e. %s if ( l = %s , %s , 0 ) <_ if ( ( l ^ 2 ) <_ Y , %s , 0 )'
              % (CSZ, PGJ, DEN('j'), GT('l')))
    fsle = st([dvfin, innre, ifre, both], 'fsumle',
              'sum_ l e. %s sum_ j e. %s if ( l = %s , %s , 0 ) <_ %s'
              % (DVP, CSZ, PGJ, DEN('j'), SS))
    w.qed([lhs, fsle], 'eqbrtrd',
          '( %s -> sum_ j e. %s %s <_ %s )' % (TB, CSZ, DEN('j'), SS))
    return w


ALL = {'twinnuc': twinnuc}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
