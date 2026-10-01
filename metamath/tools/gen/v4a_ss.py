"""Sortie v4a: the integer square root and the bounding-sum lower bound."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import CS, DEN, mkst
from cl import lift
from v4a_tb import SH, TMR, TRAL, TB, shparts
from v4a_nuc import SS, CSZ, DVP, GT

FLS = '( |_ ` ( sqrt ` %s ) )'
AA = '( A e. RR /\\ 0 <_ A )'


def flsqrt2():
    w = WS('flsqrt2', 'The integer square root of a nonnegative real is a nonnegative '
                      'integer whose square is at most the argument, and the argument is '
                      'below the square of its successor.')
    FA = FLS % 'A'
    st = mkst(w, AA)
    are = st([], 'simpl', 'A e. RR')
    age = st([], 'simpr', '0 <_ A')
    aa = st([are, age], 'jca', AA)
    sre = st([aa, w.inst('resqrtcl')], 'syl', '( sqrt ` A ) e. RR')
    sge = st([aa, w.inst('sqrtge0')], 'syl', '0 <_ ( sqrt ` A )')
    spair = st([sre, sge], 'jca', '( ( sqrt ` A ) e. RR /\\ 0 <_ ( sqrt ` A ) )')
    fn0 = st([spair, w.inst('flge0nn0')], 'syl', '%s e. NN0' % FA)
    fre = st([fn0], 'nn0red', '%s e. RR' % FA)
    fge = st([fn0], 'nn0ge0d', '0 <_ %s' % FA)
    fpair = st([fre, fge], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (FA, FA))
    fle = st([sre, w.inst('flle')], 'syl', '%s <_ ( sqrt ` A )' % FA)
    sq = st([aa, w.inst('resqrtth')], 'syl', '( ( sqrt ` A ) ^ 2 ) = A')
    both1 = st([fpair, spair], 'jca',
               '( ( %s e. RR /\\ 0 <_ %s ) /\\ '
               '( ( sqrt ` A ) e. RR /\\ 0 <_ ( sqrt ` A ) ) )' % (FA, FA))
    le1 = st([both1, w.inst('le2sq')], 'syl',
             '( %s <_ ( sqrt ` A ) <-> ( %s ^ 2 ) <_ ( ( sqrt ` A ) ^ 2 ) )' % (FA, FA))
    le1b = st([le1, fle], 'mpbid', '( %s ^ 2 ) <_ ( ( sqrt ` A ) ^ 2 )' % FA)
    le2 = st([le1b, sq], 'breqtrd', '( %s ^ 2 ) <_ A' % FA)
    flt = st([sre, w.inst('flltp1')], 'syl', '( sqrt ` A ) < ( %s + 1 )' % FA)
    onere = st([], '1red', '1 e. RR')
    ole1 = st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')
    p1re = st([fre, onere], 'readdcld', '( %s + 1 ) e. RR' % FA)
    p1ge = st([fre, onere, fge, ole1], 'addge0d', '0 <_ ( %s + 1 )' % FA)
    ppair = st([p1re, p1ge], 'jca', '( ( %s + 1 ) e. RR /\\ 0 <_ ( %s + 1 ) )' % (FA, FA))
    both2 = st([spair, ppair], 'jca',
               '( ( ( sqrt ` A ) e. RR /\\ 0 <_ ( sqrt ` A ) ) /\\ '
               '( ( %s + 1 ) e. RR /\\ 0 <_ ( %s + 1 ) ) )' % (FA, FA))
    lt1 = st([both2, w.inst('lt2sq')], 'syl',
             '( ( sqrt ` A ) < ( %s + 1 ) <-> ( ( sqrt ` A ) ^ 2 ) < ( ( %s + 1 ) ^ 2 ) )'
             % (FA, FA))
    lt1b = st([lt1, flt], 'mpbid', '( ( sqrt ` A ) ^ 2 ) < ( ( %s + 1 ) ^ 2 )' % FA)
    lt2 = st([st([sq], 'eqcomd', 'A = ( ( sqrt ` A ) ^ 2 )'), lt1b], 'eqbrtrd',
             'A < ( ( %s + 1 ) ^ 2 )' % FA)
    w.qed([fn0, le2, lt2], '3jca',
          '( %s -> ( %s e. NN0 /\\ ( %s ^ 2 ) <_ A /\\ A < ( ( %s + 1 ) ^ 2 ) ) )'
          % (AA, FA, FA, FA))
    return w


U = FLS % 'Z'
CSU = CS('( 2 x. M )', U)
PHIF = '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )'
GAM = '( %s x. ( log ` %s ) )' % (PHIF, U)


def twinssge():
    w = WS('twinssge', 'The Selberg bounding sum of the twin sieve is at least the square of '
                       'the coprime density times the logarithm of the integer square root '
                       'of the sifting bound.')
    st = mkst(w, TB)
    sh = shparts(w, st, st([], 'simp1', SH))
    mnn = st([st([], 'simp2', TMR)], 'simp1d', 'M e. NN')
    znn = st([st([], 'simp2', TMR)], 'simp2d', 'Z e. NN')
    zre = st([znn], 'nnred', 'Z e. RR')
    zge = st([st([znn], 'nnnn0d', 'Z e. NN0')], 'nn0ge0d', '0 <_ Z')
    fl = st([st([zre, zge], 'jca', '( Z e. RR /\\ 0 <_ Z )'), w.inst('flsqrt2')], 'syl',
            '( %s e. NN0 /\\ ( %s ^ 2 ) <_ Z /\\ Z < ( ( %s + 1 ) ^ 2 ) )' % (U, U, U))
    un0 = st([fl], 'simp1d', '%s e. NN0' % U)
    usq = st([fl], 'simp2d', '( %s ^ 2 ) <_ Z' % U)
    ure = st([un0], 'nn0red', '%s e. RR' % U)
    # U is a positive integer
    z1 = st([znn, w.inst('nnge1')], 'syl', '1 <_ Z')
    srt1 = st([st([st([st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'),
                      st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')], 'jca',
                     '( 1 e. RR /\\ 0 <_ 1 )'),
                   st([zre, zge], 'jca', '( Z e. RR /\\ 0 <_ Z )')], 'jca',
                  '( ( 1 e. RR /\\ 0 <_ 1 ) /\\ ( Z e. RR /\\ 0 <_ Z ) )'),
               w.inst('sqrtle')], 'syl', '( 1 <_ Z <-> ( sqrt ` 1 ) <_ ( sqrt ` Z ) )')
    s1e1 = st([w.s([], 'sqrt1', '( sqrt ` 1 ) = 1')], 'a1i', '( sqrt ` 1 ) = 1')
    sge1 = st([st([s1e1], 'eqcomd', '1 = ( sqrt ` 1 )'),
               st([srt1, z1], 'mpbid', '( sqrt ` 1 ) <_ ( sqrt ` Z )')], 'eqbrtrd',
              '1 <_ ( sqrt ` Z )')
    sqre = st([st([zre, zge], 'jca', '( Z e. RR /\\ 0 <_ Z )'), w.inst('resqrtcl')], 'syl',
              '( sqrt ` Z ) e. RR')
    u1 = st([st([sqre, st([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), w.inst('flge')],
                'syl2anc', '( 1 <_ ( sqrt ` Z ) <-> 1 <_ %s )' % U), sge1], 'mpbid',
             '1 <_ %s' % U)
    unn = st([st([un0, u1], 'jca', '( %s e. NN0 /\\ 1 <_ %s )' % (U, U)),
              st([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )'
                      % (U, U, U))], 'a1i',
                 '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (U, U, U))], 'mpbird',
             '%s e. NN' % U)
    tmnn = st([st([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN'), mnn], 'nnmulcld',
              '( 2 x. M ) e. NN')
    # the coprime harmonic bound, squared
    coph = st([st([tmnn, unn], 'jca', '( ( 2 x. M ) e. NN /\\ %s e. NN )' % U),
               w.inst('cophrm')], 'syl',
              '%s <_ sum_ j e. %s ( 1 / j )' % (GAM, CSU))
    phinn = st([tmnn, w.inst('phicl')], 'syl', '( phi ` ( 2 x. M ) ) e. NN')
    phire = st([phinn], 'nnred', '( phi ` ( 2 x. M ) ) e. RR')
    phif = st([phire, st([tmnn], 'nnrpd', '( 2 x. M ) e. RR+')], 'rerpdivcld',
              '%s e. RR' % PHIF)
    phige = st([st([phire, st([st([phinn], 'nnnn0d', '( phi ` ( 2 x. M ) ) e. NN0')],
                              'nn0ge0d', '0 <_ ( phi ` ( 2 x. M ) )')], 'jca',
                   '( ( phi ` ( 2 x. M ) ) e. RR /\\ 0 <_ ( phi ` ( 2 x. M ) ) )'),
                st([st([tmnn], 'nnred', '( 2 x. M ) e. RR'),
                    st([tmnn], 'nngt0d', '0 < ( 2 x. M )')], 'jca',
                   '( ( 2 x. M ) e. RR /\\ 0 < ( 2 x. M ) )'), w.inst('divge0')], 'syl2anc',
               '0 <_ %s' % PHIF)
    logre = st([st([unn], 'nnrpd', '%s e. RR+' % U), w.inst('relogcl')], 'syl',
               '( log ` %s ) e. RR' % U)
    logge = st([st([ure, u1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (U, U)),
                w.inst('logge0')], 'syl', '0 <_ ( log ` %s )' % U)
    gamre = st([phif, logre], 'remulcld', '%s e. RR' % GAM)
    gamge = st([phif, logre, phige, logge], 'mulge0d', '0 <_ %s' % GAM)
    # the sum of reciprocals is real
    csufin = st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % U),
                 st([w.s([], 'ssrab2', '%s C_ ( 1 ... %s )' % (CSU, U))], 'a1i',
                    '%s C_ ( 1 ... %s )' % (CSU, U))], 'ssfid', '%s e. Fin' % CSU)
    AJ = '( %s /\\ j e. %s )' % (TB, CSU)
    sj = mkst(w, AJ)
    jnn = sj([sj([lift(w, st([w.s([], 'ssrab2', '%s C_ ( 1 ... %s )' % (CSU, U))], 'a1i',
                             '%s C_ ( 1 ... %s )' % (CSU, U)), AJ),
                  sj([], 'simpr', 'j e. %s' % CSU)], 'sseldd', 'j e. ( 1 ... %s )' % U),
              w.inst('elfznn')], 'syl', 'j e. NN')
    jre = sj([jnn], 'nnrecred', '( 1 / j ) e. RR')
    sumre = st([csufin, jre], 'fsumrecl', 'sum_ j e. %s ( 1 / j ) e. RR' % CSU)
    sq1 = st([st([st([gamre, gamge], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (GAM, GAM)),
                  st([sumre, coph], 'jca',
                     '( sum_ j e. %s ( 1 / j ) e. RR /\\ %s <_ sum_ j e. %s ( 1 / j ) )'
                     % (CSU, GAM, CSU))], 'jca',
                 '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( sum_ j e. %s ( 1 / j ) e. RR /\\ '
                 '%s <_ sum_ j e. %s ( 1 / j ) ) )' % (GAM, GAM, CSU, GAM, CSU)),
              w.inst('le2sq2')], 'syl',
             '( %s ^ 2 ) <_ ( sum_ j e. %s ( 1 / j ) ^ 2 )' % (GAM, CSU))
    # twinsq
    uu = st([st([st([ure], 'recnd', '%s e. CC' % U)], 'sqvald',
                '( %s ^ 2 ) = ( %s x. %s )' % (U, U, U)), usq], 'eqbrtrrd',
            '( %s x. %s ) <_ Z' % (U, U))
    tsq = st([st([st([tmnn, un0], 'jca', '( ( 2 x. M ) e. NN /\\ %s e. NN0 )' % U),
                 st([znn, uu], 'jca', '( Z e. NN /\\ ( %s x. %s ) <_ Z )' % (U, U))], 'jca',
                '( ( ( 2 x. M ) e. NN /\\ %s e. NN0 ) /\\ ( Z e. NN /\\ ( %s x. %s ) <_ Z ) )'
                % (U, U, U)), w.inst('twinsq')], 'syl',
             '( sum_ j e. %s ( 1 / j ) ^ 2 ) <_ sum_ l e. %s %s' % (CSU, CSZ, DEN('l')))
    cbv = w.s([w.s([w.s([], 'oveq2', '( l = j -> ( 0 sigma l ) = ( 0 sigma j ) )'),
                    w.s([], 'id', '( l = j -> l = j )')], 'oveq12d',
                   '( l = j -> %s = %s )' % (DEN('l'), DEN('j')))], 'cbvsumv',
              'sum_ l e. %s %s = sum_ j e. %s %s' % (CSZ, DEN('l'), CSZ, DEN('j')))
    tsq2 = st([tsq, st([cbv], 'a1i',
                       'sum_ l e. %s %s = sum_ j e. %s %s' % (CSZ, DEN('l'), CSZ, DEN('j')))],
              'breqtrd',
              '( sum_ j e. %s ( 1 / j ) ^ 2 ) <_ sum_ j e. %s %s' % (CSU, CSZ, DEN('j')))
    nuc = st([], 'twinnuc', 'sum_ j e. %s %s <_ %s' % (CSZ, DEN('j'), SS))
    # closures for the chain
    g2 = st([gamre, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'reexpcld',
            '( %s ^ 2 ) e. RR' % GAM)
    s2 = st([sumre, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'reexpcld',
            '( sum_ j e. %s ( 1 / j ) ^ 2 ) e. RR' % CSU)
    cszfin = st([st([], 'fzfid', '( 1 ... Z ) e. Fin'),
                 st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % CSZ)], 'a1i',
                    '%s C_ ( 1 ... Z )' % CSZ)], 'ssfid', '%s e. Fin' % CSZ)
    AJZ = '( %s /\\ j e. %s )' % (TB, CSZ)
    sjz = mkst(w, AJZ)
    jznn = sjz([sjz([lift(w, st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % CSZ)], 'a1i',
                                '%s C_ ( 1 ... Z )' % CSZ), AJZ),
                     sjz([], 'simpr', 'j e. %s' % CSZ)], 'sseldd', 'j e. ( 1 ... Z )'),
                w.inst('elfznn')], 'syl', 'j e. NN')
    denre = sjz([sjz([sjz([sjz([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), jznn,
                          w.inst('sgmnncl')], 'syl2anc', '( 0 sigma j ) e. NN')], 'nnred',
                     '( 0 sigma j ) e. RR'), sjz([jznn], 'nnrpd', 'j e. RR+')], 'rerpdivcld',
                '%s e. RR' % DEN('j'))
    nucre = st([cszfin, denre], 'fsumrecl', 'sum_ j e. %s %s e. RR' % (CSZ, DEN('j')))
    ALP = '( %s /\\ l e. %s )' % (TB, DVP)
    slp = mkst(w, ALP)
    ldv = w.s([w.s([], 'breq1', '( x = l -> ( x || P <-> l || P ) )')], 'elrab',
              '( l e. %s <-> ( l e. NN /\\ l || P ) )' % DVP)
    lmem = slp([slp([ldv], 'a1i', '( l e. %s <-> ( l e. NN /\\ l || P ) )' % DVP),
                slp([], 'simpr', 'l e. %s' % DVP)], 'mpbid', '( l e. NN /\\ l || P )')
    gtre = slp([slp([slp([lift(w, sh['sh'], ALP), lmem], 'jca',
                         '( %s /\\ ( l e. NN /\\ l || P ) )' % SH), w.inst('gtrp')], 'syl',
                    '%s e. RR+' % GT('l'))], 'rpred', '%s e. RR' % GT('l'))
    ifre = slp([gtre, slp([], '0red', '0 e. RR')], 'ifcld',
               'if ( ( l ^ 2 ) <_ Y , %s , 0 ) e. RR' % GT('l'))
    dvfin = st([sh['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    ssre = st([dvfin, ifre], 'fsumrecl', '%s e. RR' % SS)
    ch1 = st([g2, s2, nucre, sq1, tsq2], 'letrd',
             '( %s ^ 2 ) <_ sum_ j e. %s %s' % (GAM, CSZ, DEN('j')))
    w.qed([g2, nucre, ssre, ch1, nuc], 'letrd', '( %s -> ( %s ^ 2 ) <_ %s )' % (TB, GAM, SS))
    return w


ALL = {'flsqrt2': flsqrt2, 'twinssge': twinssge}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
