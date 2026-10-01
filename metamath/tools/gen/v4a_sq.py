"""Sortie v4a: the square of the coprime harmonic sum is dominated by the density sum."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import CS, DEN, mkst, csel
from cl import lift
from lin import linarith, nlinarith

AQ = '( ( K e. NN /\\ U e. NN0 ) /\\ ( Z e. NN /\\ ( U x. U ) <_ Z ) )'
I = CS('K', 'U')
J = CS('K', 'Z')
XII = '( %s X. %s )' % (I, I)
S = 'sum_ j e. %s ( 1 / j )' % I


def P(q):
    return '( ( 1st ` %s ) x. ( 2nd ` %s ) )' % (q, q)


RAB = '{ v e. %s | %s = %s }' % (XII, 'l', P('v'))
FMP = '( q e. %s |-> ( 1st ` q ) )' % RAB
DVL = '{ p e. NN | p || l }'


def twinsq():
    w = WS('twinsq', 'The square of the harmonic sum over the integers up to U coprime to K '
                     'is at most the sum of the divisor count over the integers up to Z '
                     'coprime to K, when U squared is at most Z.')
    st = mkst(w, AQ)
    knn = st([], 'simpll', 'K e. NN')
    un0 = st([], 'simplr', 'U e. NN0')
    znn = st([], 'simprl', 'Z e. NN')
    uuz = st([], 'simprr', '( U x. U ) <_ Z')
    kz = st([knn], 'nnzd', 'K e. ZZ')
    ure = st([un0], 'nn0red', 'U e. RR')
    zre = st([znn], 'nnred', 'Z e. RR')
    iss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... U )' % I)], 'a1i', '%s C_ ( 1 ... U )' % I)
    jss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % J)], 'a1i', '%s C_ ( 1 ... Z )' % J)
    ifin = st([st([], 'fzfid', '( 1 ... U ) e. Fin'), iss], 'ssfid', '%s e. Fin' % I)
    jfin = st([st([], 'fzfid', '( 1 ... Z ) e. Fin'), jss], 'ssfid', '%s e. Fin' % J)
    xfin = st([ifin, ifin, w.inst('xpfi')], 'syl2anc', '%s e. Fin' % XII)
    # the reciprocal of an element of I
    AJ = '( %s /\\ j e. %s )' % (AQ, I)
    sj = mkst(w, AJ)
    jnn = sj([sj([lift(w, iss, AJ), sj([], 'simpr', 'j e. %s' % I)], 'sseldd',
                 'j e. ( 1 ... U )'), w.inst('elfznn')], 'syl', 'j e. NN')
    jrp = sj([sj([jnn], 'nnrpd', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    jcc = sj([sj([jrp], 'rpred', '( 1 / j ) e. RR')], 'recnd', '( 1 / j ) e. CC')
    sre = st([ifin, sj([jrp], 'rpred', '( 1 / j ) e. RR')], 'fsumrecl', '%s e. RR' % S)
    scc = st([sre], 'recnd', '%s e. CC' % S)
    # expand the square
    sq = st([scc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (S, S, S))
    cbvi = w.s([w.s([], 'oveq2', '( j = i -> ( 1 / j ) = ( 1 / i ) )')], 'cbvsumv',
               '%s = sum_ i e. %s ( 1 / i )' % (S, I))
    sq2 = st([sq, st([st([cbvi], 'a1i', '%s = sum_ i e. %s ( 1 / i )' % (S, I))], 'oveq1d',
                     '( %s x. %s ) = ( sum_ i e. %s ( 1 / i ) x. %s )' % (S, S, I, S))],
             'eqtrd', '( %s ^ 2 ) = ( sum_ i e. %s ( 1 / i ) x. %s )' % (S, I, S))
    AI = '( %s /\\ i e. %s )' % (AQ, I)
    sii = mkst(w, AI)
    inn = sii([sii([lift(w, iss, AI), sii([], 'simpr', 'i e. %s' % I)], 'sseldd',
                   'i e. ( 1 ... U )'), w.inst('elfznn')], 'syl', 'i e. NN')
    irp = sii([sii([inn], 'nnrpd', 'i e. RR+')], 'rpreccld', '( 1 / i ) e. RR+')
    icc = sii([sii([irp], 'rpred', '( 1 / i ) e. RR')], 'recnd', '( 1 / i ) e. CC')
    mc1 = st([ifin, scc, icc], 'fsummulc1',
             '( sum_ i e. %s ( 1 / i ) x. %s ) = sum_ i e. %s ( ( 1 / i ) x. %s )' % (I, S, I, S))
    AIJ = '( %s /\\ j e. %s )' % (AI, I)
    sij = mkst(w, AIJ)
    jcc2 = sij([sij([sij([sij([lift(w, iss, AIJ), sij([], 'simpr', 'j e. %s' % I)], 'sseldd',
                              'j e. ( 1 ... U )'), w.inst('elfznn')], 'syl', 'j e. NN')],
                    'nnrecred', '( 1 / j ) e. RR')], 'recnd', '( 1 / j ) e. CC')
    mc2 = sii([lift(w, ifin, AI), icc, jcc2], 'fsummulc2',
              '( ( 1 / i ) x. %s ) = sum_ j e. %s ( ( 1 / i ) x. ( 1 / j ) )' % (S, I))
    dbl = st([mc1, st([mc2], 'sumeq2dv',
                      'sum_ i e. %s ( ( 1 / i ) x. %s ) = '
                      'sum_ i e. %s sum_ j e. %s ( ( 1 / i ) x. ( 1 / j ) )' % (I, S, I, I))],
             'eqtrd',
             '( sum_ i e. %s ( 1 / i ) x. %s ) = '
             'sum_ i e. %s sum_ j e. %s ( ( 1 / i ) x. ( 1 / j ) )' % (I, S, I, I))
    # the double sum is a sum over the product
    sbq = w.s([w.s([w.s([], 'op1st', '( 1st ` <. i , j >. ) = i')], 'id', 'a'),
               w.s([], 'id', 'b')], 'id', 'c')
    w.lines.pop(); w.lines.pop(); w.lines.pop()
    ivex = w.s([], 'vex', 'i e. _V')
    jvex = w.s([], 'vex', 'j e. _V')
    o1 = w.s([ivex, jvex], 'op1st', '( 1st ` <. i , j >. ) = i')
    o2 = w.s([ivex, jvex], 'op2nd', '( 2nd ` <. i , j >. ) = j')
    sub1 = w.s([w.s([], 'fveq2', '( q = <. i , j >. -> ( 1st ` q ) = ( 1st ` <. i , j >. ) )'),
                w.s([o1], 'a1i',
                    '( q = <. i , j >. -> ( 1st ` <. i , j >. ) = i )')], 'eqtrd',
               '( q = <. i , j >. -> ( 1st ` q ) = i )')
    sub2 = w.s([w.s([], 'fveq2', '( q = <. i , j >. -> ( 2nd ` q ) = ( 2nd ` <. i , j >. ) )'),
                w.s([o2], 'a1i',
                    '( q = <. i , j >. -> ( 2nd ` <. i , j >. ) = j )')], 'eqtrd',
               '( q = <. i , j >. -> ( 2nd ` q ) = j )')
    subd = w.s([w.s([sub1], 'oveq2d',
                    '( q = <. i , j >. -> ( 1 / ( 1st ` q ) ) = ( 1 / i ) )'),
                w.s([sub2], 'oveq2d',
                    '( q = <. i , j >. -> ( 1 / ( 2nd ` q ) ) = ( 1 / j ) )')], 'oveq12d',
               '( q = <. i , j >. -> ( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) ) = '
               '( ( 1 / i ) x. ( 1 / j ) ) )')
    bodycc = sij([lift(w, icc, AIJ), jcc2], 'mulcld', '( ( 1 / i ) x. ( 1 / j ) ) e. CC')
    AIJ2 = '( %s /\\ ( i e. %s /\\ j e. %s ) )' % (AQ, I, I)
    sij2 = mkst(w, AIJ2)
    ipair = sij2([sij2([], 'simpr', '( i e. %s /\\ j e. %s )' % (I, I))], 'simpld', 'i e. %s' % I)
    jpair = sij2([sij2([], 'simpr', '( i e. %s /\\ j e. %s )' % (I, I))], 'simprd', 'j e. %s' % I)
    iccp = sij2([sij2([sij2([sij2([lift(w, iss, AIJ2), ipair], 'sseldd', 'i e. ( 1 ... U )'),
                             w.inst('elfznn')], 'syl', 'i e. NN')], 'nnrecred',
                      '( 1 / i ) e. RR')], 'recnd', '( 1 / i ) e. CC')
    jccp = sij2([sij2([sij2([sij2([lift(w, iss, AIJ2), jpair], 'sseldd', 'j e. ( 1 ... U )'),
                             w.inst('elfznn')], 'syl', 'j e. NN')], 'nnrecred',
                      '( 1 / j ) e. RR')], 'recnd', '( 1 / j ) e. CC')
    bodycc2 = sij2([iccp, jccp], 'mulcld', '( ( 1 / i ) x. ( 1 / j ) ) e. CC')
    xp = st([subd, ifin, ifin, bodycc2], 'fsumxp',
            'sum_ i e. %s sum_ j e. %s ( ( 1 / i ) x. ( 1 / j ) ) = '
            'sum_ q e. %s ( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) )' % (I, I, XII))
    lhs = st([sq2, st([dbl, xp], 'eqtrd',
                      '( sum_ i e. %s ( 1 / i ) x. %s ) = '
                      'sum_ q e. %s ( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) )'
                      % (I, S, XII))], 'eqtrd',
              '( %s ^ 2 ) = sum_ q e. %s ( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) )'
              % (S, XII))
    # each element of the product maps into J
    AQQ = '( %s /\ q e. %s )' % (AQ, XII)
    sq_ = mkst(w, AQQ)
    qx = sq_([], 'simpr', 'q e. %s' % XII)
    q1i = sq_([qx, w.inst('xp1st')], 'syl', '( 1st ` q ) e. %s' % I)
    q2i = sq_([qx, w.inst('xp2nd')], 'syl', '( 2nd ` q ) e. %s' % I)
    e1 = csel(w, '( 1st ` q )', 'K', 'U')
    e2 = csel(w, '( 2nd ` q )', 'K', 'U')
    m1 = sq_([sq_([e1], 'a1i',
                  '( ( 1st ` q ) e. %s <-> ( ( 1st ` q ) e. ( 1 ... U ) /\ ( ( 1st ` q ) gcd K ) = 1 ) )'
                  % I), q1i], 'mpbid',
             '( ( 1st ` q ) e. ( 1 ... U ) /\ ( ( 1st ` q ) gcd K ) = 1 )')
    m2 = sq_([sq_([e2], 'a1i',
                  '( ( 2nd ` q ) e. %s <-> ( ( 2nd ` q ) e. ( 1 ... U ) /\ ( ( 2nd ` q ) gcd K ) = 1 ) )'
                  % I), q2i], 'mpbid',
             '( ( 2nd ` q ) e. ( 1 ... U ) /\ ( ( 2nd ` q ) gcd K ) = 1 )')
    f1z = sq_([m1], 'simpld', '( 1st ` q ) e. ( 1 ... U )')
    f2z = sq_([m2], 'simpld', '( 2nd ` q ) e. ( 1 ... U )')
    g1 = sq_([m1], 'simprd', '( ( 1st ` q ) gcd K ) = 1')
    g2 = sq_([m2], 'simprd', '( ( 2nd ` q ) gcd K ) = 1')
    n1 = sq_([f1z, w.inst('elfznn')], 'syl', '( 1st ` q ) e. NN')
    n2 = sq_([f2z, w.inst('elfznn')], 'syl', '( 2nd ` q ) e. NN')
    le1 = sq_([f1z, w.inst('elfzle2')], 'syl', '( 1st ` q ) <_ U')
    le2 = sq_([f2z, w.inst('elfzle2')], 'syl', '( 2nd ` q ) <_ U')
    pnn = sq_([n1, n2], 'nnmulcld', '%s e. NN' % P('q'))
    pre = sq_([pnn], 'nnred', '%s e. RR' % P('q'))
    r1 = sq_([n1], 'nnred', '( 1st ` q ) e. RR')
    r2 = sq_([n2], 'nnred', '( 2nd ` q ) e. RR')
    p1 = sq_([n1], 'nngt0d', '0 < ( 1st ` q )')
    p2 = sq_([n2], 'nngt0d', '0 < ( 2nd ` q )')
    ge01 = sq_([sq_([n1], 'nnnn0d', '( 1st ` q ) e. NN0')], 'nn0ge0d',
               '0 <_ ( 1st ` q )')
    ge02 = sq_([sq_([n2], 'nnnn0d', '( 2nd ` q ) e. NN0')], 'nn0ge0d',
               '0 <_ ( 2nd ` q )')
    ur2 = lift(w, ure, AQQ)
    zr2 = lift(w, zre, AQQ)
    s1 = sq_([sq_([sq_([r1, ur2, sq_([r2, ge02], 'jca',
                                     '( ( 2nd ` q ) e. RR /\\ 0 <_ ( 2nd ` q ) )')], '3jca',
                       '( ( 1st ` q ) e. RR /\\ U e. RR /\\ ( ( 2nd ` q ) e. RR /\\ 0 <_ ( 2nd ` q ) ) )'),
                   le1], 'jca',
                  '( ( ( 1st ` q ) e. RR /\\ U e. RR /\\ ( ( 2nd ` q ) e. RR /\\ 0 <_ ( 2nd ` q ) ) ) '
                  '/\\ ( 1st ` q ) <_ U )'), w.inst('lemul1a')], 'syl',
              '%s <_ ( U x. ( 2nd ` q ) )' % P('q'))
    s2 = sq_([sq_([sq_([r2, ur2, sq_([ur2, sq_([lift(w, un0, AQQ)], 'nn0ge0d', '0 <_ U')],
                                     'jca', '( U e. RR /\\ 0 <_ U )')], '3jca',
                       '( ( 2nd ` q ) e. RR /\\ U e. RR /\\ ( U e. RR /\\ 0 <_ U ) )'),
                   le2], 'jca',
                  '( ( ( 2nd ` q ) e. RR /\\ U e. RR /\\ ( U e. RR /\\ 0 <_ U ) ) '
                  '/\\ ( 2nd ` q ) <_ U )'), w.inst('lemul2a')], 'syl',
              '( U x. ( 2nd ` q ) ) <_ ( U x. U )')
    u2re = sq_([ur2, r2], 'remulcld', '( U x. ( 2nd ` q ) ) e. RR')
    uure = sq_([ur2, ur2], 'remulcld', '( U x. U ) e. RR')
    plez = sq_([pre, u2re, zr2, s1,
                sq_([u2re, uure, zr2, s2, lift(w, uuz, AQQ)], 'letrd',
                    '( U x. ( 2nd ` q ) ) <_ Z')], 'letrd', '%s <_ Z' % P('q'))
    pfz = sq_([sq_([pnn, lift(w, znn, AQQ), plez], '3jca',
                   '( %s e. NN /\ Z e. NN /\ %s <_ Z )' % (P('q'), P('q'))),
               sq_([w.s([], 'elfz1b',
                        '( %s e. ( 1 ... Z ) <-> ( %s e. NN /\ Z e. NN /\ %s <_ Z ) )'
                        % (P('q'), P('q'), P('q')))], 'a1i',
                   '( %s e. ( 1 ... Z ) <-> ( %s e. NN /\ Z e. NN /\ %s <_ Z ) )'
                   % (P('q'), P('q'), P('q')))], 'mpbird', '%s e. ( 1 ... Z )' % P('q'))
    c1 = sq_([sq_([lift(w, kz, AQQ), sq_([n1], 'nnzd', '( 1st ` q ) e. ZZ')], 'gcdcomd',
                  '( K gcd ( 1st ` q ) ) = ( ( 1st ` q ) gcd K )'), g1], 'eqtrd',
             '( K gcd ( 1st ` q ) ) = 1')
    c2 = sq_([sq_([lift(w, kz, AQQ), sq_([n2], 'nnzd', '( 2nd ` q ) e. ZZ')], 'gcdcomd',
                  '( K gcd ( 2nd ` q ) ) = ( ( 2nd ` q ) gcd K )'), g2], 'eqtrd',
             '( K gcd ( 2nd ` q ) ) = 1')
    cp0 = sq_([sq_([sq_([lift(w, kz, AQQ), sq_([n1], 'nnzd', '( 1st ` q ) e. ZZ'),
                        sq_([n2], 'nnzd', '( 2nd ` q ) e. ZZ')], '3jca',
                       '( K e. ZZ /\ ( 1st ` q ) e. ZZ /\ ( 2nd ` q ) e. ZZ )'),
                   w.inst('rpmul')], 'syl',
                  '( ( ( K gcd ( 1st ` q ) ) = 1 /\ ( K gcd ( 2nd ` q ) ) = 1 ) -> '
                  '( K gcd %s ) = 1 )' % P('q')),
               sq_([c1, c2], 'jca',
                   '( ( K gcd ( 1st ` q ) ) = 1 /\ ( K gcd ( 2nd ` q ) ) = 1 )')], 'mpd',
              '( K gcd %s ) = 1' % P('q'))
    cp = sq_([sq_([sq_([pnn], 'nnzd', '%s e. ZZ' % P('q')), lift(w, kz, AQQ)], 'gcdcomd',
                  '( %s gcd K ) = ( K gcd %s )' % (P('q'), P('q'))), cp0], 'eqtrd',
             '( %s gcd K ) = 1' % P('q'))
    ej = csel(w, P('q'), 'K', 'Z')
    pj = sq_([sq_([pfz, cp], 'jca',
                  '( %s e. ( 1 ... Z ) /\ ( %s gcd K ) = 1 )' % (P('q'), P('q'))),
              sq_([ej], 'a1i',
                  '( %s e. %s <-> ( %s e. ( 1 ... Z ) /\ ( %s gcd K ) = 1 ) )'
                  % (P('q'), J, P('q'), P('q')))], 'mpbird', '%s e. %s' % (P('q'), J))
    # the body is the reciprocal of the product
    prc = sq_([pnn], 'nnrpd', '%s e. RR+' % P('q'))
    recp = sq_([prc], 'rpreccld', '( 1 / %s ) e. RR+' % P('q'))
    dmd = sq_([sq_([sq_([sq_([], '1red', '1 e. RR')], 'recnd', '1 e. CC'),
                    sq_([sq_([], '1red', '1 e. RR')], 'recnd', '1 e. CC')], 'jca',
                   '( 1 e. CC /\ 1 e. CC )'),
               sq_([sq_([sq_([r1], 'recnd', '( 1st ` q ) e. CC'),
                         sq_([n1], 'nnne0d', '( 1st ` q ) =/= 0')], 'jca',
                        '( ( 1st ` q ) e. CC /\ ( 1st ` q ) =/= 0 )'),
                    sq_([sq_([r2], 'recnd', '( 2nd ` q ) e. CC'),
                         sq_([n2], 'nnne0d', '( 2nd ` q ) =/= 0')], 'jca',
                        '( ( 2nd ` q ) e. CC /\ ( 2nd ` q ) =/= 0 )')], 'jca',
                   '( ( ( 1st ` q ) e. CC /\ ( 1st ` q ) =/= 0 ) /\ '
                   '( ( 2nd ` q ) e. CC /\ ( 2nd ` q ) =/= 0 ) )'),
               w.inst('divmuldiv')], 'syl2anc',
              '( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) ) = ( ( 1 x. 1 ) / %s )' % P('q'))
    dmd2 = sq_([dmd, sq_([sq_([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')],
                         'oveq1d', '( ( 1 x. 1 ) / %s ) = ( 1 / %s )' % (P('q'), P('q')))],
               'eqtrd',
               '( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) ) = ( 1 / %s )' % P('q'))
    # sumite fibres it over J
    sbl = w.s([], 'oveq2', '( l = %s -> ( 1 / l ) = ( 1 / %s ) )' % (P('q'), P('q')))
    sit = sq_([sbl, lift(w, jfin, AQQ), pj, sq_([recp], 'rpcnd', '( 1 / %s ) e. CC' % P('q'))],
              'sumite',
              'sum_ l e. %s if ( l = %s , ( 1 / l ) , 0 ) = ( 1 / %s )' % (J, P('q'), P('q')))
    bodyeq = sq_([dmd2, sq_([sit], 'eqcomd',
                            '( 1 / %s ) = sum_ l e. %s if ( l = %s , ( 1 / l ) , 0 )'
                            % (P('q'), J, P('q')))], 'eqtrd',
                 '( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) ) = '
                 'sum_ l e. %s if ( l = %s , ( 1 / l ) , 0 )' % (J, P('q')))
    ins = st([bodyeq], 'sumeq2dv',
             'sum_ q e. %s ( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) ) = '
             'sum_ q e. %s sum_ l e. %s if ( l = %s , ( 1 / l ) , 0 )'
             % (XII, XII, J, P('q')))
    AQL = '( %s /\ ( q e. %s /\ l e. %s ) )' % (AQ, XII, J)
    sql = mkst(w, AQL)
    lnn2 = sql([sql([lift(w, jss, AQL), sql([sql([], 'simpr',
                                                 '( q e. %s /\ l e. %s )' % (XII, J))],
                                            'simprd', 'l e. %s' % J)], 'sseldd',
                    'l e. ( 1 ... Z )'), w.inst('elfznn')], 'syl', 'l e. NN')
    ifcc = sql([sql([sql([sql([lnn2], 'nnrpd', 'l e. RR+')], 'rpreccld', '( 1 / l ) e. RR+')],
                    'rpcnd', '( 1 / l ) e. CC'),
                sql([sql([], '0red', '0 e. RR')], 'recnd', '0 e. CC')], 'ifcld',
               'if ( l = %s , ( 1 / l ) , 0 ) e. CC' % P('q'))
    com = st([xfin, jfin, ifcc], 'fsumcom',
             'sum_ q e. %s sum_ l e. %s if ( l = %s , ( 1 / l ) , 0 ) = '
             'sum_ l e. %s sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 )'
             % (XII, J, P('q'), J, XII, P('q')))
    lhs2 = st([lhs, st([ins, com], 'eqtrd',
                       'sum_ q e. %s ( ( 1 / ( 1st ` q ) ) x. ( 1 / ( 2nd ` q ) ) ) = '
                       'sum_ l e. %s sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 )'
                       % (XII, J, XII, P('q')))], 'eqtrd',
              '( %s ^ 2 ) = sum_ l e. %s sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 )'
              % (S, J, XII, P('q')))
    # the fibre bound, for each l in J
    AL = '( %s /\ l e. %s )' % (AQ, J)
    sl = mkst(w, AL)
    lj = sl([], 'simpr', 'l e. %s' % J)
    lnn = sl([sl([lift(w, jss, AL), lj], 'sseldd', 'l e. ( 1 ... Z )'), w.inst('elfznn')],
             'syl', 'l e. NN')
    lrp = sl([lnn], 'nnrpd', 'l e. RR+')
    lirp = sl([lrp], 'rpreccld', '( 1 / l ) e. RR+')
    lire = sl([lirp], 'rpred', '( 1 / l ) e. RR')
    licc = sl([lire], 'recnd', '( 1 / l ) e. CC')
    rabss = sl([w.s([], 'ssrab2', '%s C_ %s' % (RAB, XII))], 'a1i', '%s C_ %s' % (RAB, XII))
    rabfin = sl([lift(w, xfin, AL), rabss], 'ssfid', '%s e. Fin' % RAB)
    elra = w.s([], 'fveq2', '( v = q -> ( 1st ` v ) = ( 1st ` q ) )')
    elrb0 = w.s([], 'fveq2', '( v = q -> ( 2nd ` v ) = ( 2nd ` q ) )')
    elrc = w.s([elra, elrb0], 'oveq12d', '( v = q -> %s = %s )' % (P('v'), P('q')))
    elr = w.s([elrc], 'eqeq2d',
              '( v = q -> ( l = %s <-> l = %s ) )' % (P('v'), P('q')))
    elrb = w.s([elr], 'elrab',
               '( q e. %s <-> ( q e. %s /\ l = %s ) )' % (RAB, XII, P('q')))
    ARQ = '( %s /\ q e. %s )' % (AL, RAB)
    srq = mkst(w, ARQ)
    qmem = srq([srq([elrb], 'a1i',
                    '( q e. %s <-> ( q e. %s /\ l = %s ) )' % (RAB, XII, P('q'))),
                srq([], 'simpr', 'q e. %s' % RAB)], 'mpbid',
               '( q e. %s /\ l = %s )' % (XII, P('q')))
    qxii = srq([qmem], 'simpld', 'q e. %s' % XII)
    qleq = srq([qmem], 'simprd', 'l = %s' % P('q'))
    # the body is 1 / l on the fibre and 0 off it
    AXQ = '( %s /\ q e. %s )' % (AL, XII)
    sxq = mkst(w, AXQ)
    ifcc2 = sxq([lift(w, licc, AXQ), sxq([sxq([], '0red', '0 e. RR')], 'recnd', '0 e. CC')],
                'ifcld', 'if ( l = %s , ( 1 / l ) , 0 ) e. CC' % P('q'))
    ADQ = '( %s /\ q e. ( %s \ %s ) )' % (AL, XII, RAB)
    sdq = mkst(w, ADQ)
    qin = sdq([sdq([], 'simpr', 'q e. ( %s \ %s )' % (XII, RAB)), w.inst('eldifi')], 'syl',
              'q e. %s' % XII)
    qnin = sdq([sdq([], 'simpr', 'q e. ( %s \ %s )' % (XII, RAB)), w.inst('eldifn')], 'syl',
               '-. q e. %s' % RAB)
    nand = sdq([sdq([elrb], 'a1i',
                    '( q e. %s <-> ( q e. %s /\ l = %s ) )' % (RAB, XII, P('q'))),
                qnin], 'mtbid', '-. ( q e. %s /\ l = %s )' % (XII, P('q')))
    imnan = w.s([], 'imnan',
                '( ( q e. %s -> -. l = %s ) <-> -. ( q e. %s /\ l = %s ) )'
                % (XII, P('q'), XII, P('q')))
    imp0 = sdq([sdq([sdq([imnan], 'a1i',
                         '( ( q e. %s -> -. l = %s ) <-> -. ( q e. %s /\ l = %s ) )'
                         % (XII, P('q'), XII, P('q'))), nand], 'mpbird',
                    '( q e. %s -> -. l = %s )' % (XII, P('q'))), qin], 'mpd',
               '-. l = %s' % P('q'))
    zerob = sdq([imp0], 'iffalsed', 'if ( l = %s , ( 1 / l ) , 0 ) = 0' % P('q'))
    ifccR = srq([lift(w, licc, ARQ), srq([srq([], '0red', '0 e. RR')], 'recnd', '0 e. CC')],
                'ifcld', 'if ( l = %s , ( 1 / l ) , 0 ) e. CC' % P('q'))
    ss1 = sl([rabss, ifccR, zerob, lift(w, xfin, AL)], 'fsumss',
             'sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 ) = '
             'sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 )' % (RAB, P('q'), XII, P('q')))
    oneb = srq([qleq], 'iftrued', 'if ( l = %s , ( 1 / l ) , 0 ) = ( 1 / l )' % P('q'))
    rsum = sl([sl([oneb], 'sumeq2dv',
                  'sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 ) = sum_ q e. %s ( 1 / l )'
                  % (RAB, P('q'), RAB)),
               sl([rabfin, licc, w.inst('fsumconst')], 'syl2anc',
                  'sum_ q e. %s ( 1 / l ) = ( ( # ` %s ) x. ( 1 / l ) )' % (RAB, RAB))],
              'eqtrd',
              'sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 ) = ( ( # ` %s ) x. ( 1 / l ) )'
              % (RAB, P('q'), RAB))
    # the fibre injects into the divisors of l
    q1nn = srq([srq([lift(w, iss, ARQ), srq([qxii, w.inst('xp1st')], 'syl',
                                            '( 1st ` q ) e. %s' % I)], 'sseldd',
                    '( 1st ` q ) e. ( 1 ... U )'), w.inst('elfznn')], 'syl',
               '( 1st ` q ) e. NN')
    q2nn = srq([srq([lift(w, iss, ARQ), srq([qxii, w.inst('xp2nd')], 'syl',
                                            '( 2nd ` q ) e. %s' % I)], 'sseldd',
                    '( 2nd ` q ) e. ( 1 ... U )'), w.inst('elfznn')], 'syl',
               '( 2nd ` q ) e. NN')
    dvd1 = srq([srq([srq([srq([q1nn], 'nnzd', '( 1st ` q ) e. ZZ'),
                          srq([q2nn], 'nnzd', '( 2nd ` q ) e. ZZ')], 'jca',
                         '( ( 1st ` q ) e. ZZ /\ ( 2nd ` q ) e. ZZ )'), w.inst('dvdsmul1')],
                    'syl', '( 1st ` q ) || %s' % P('q')), qleq], 'breqtrrd',
               '( 1st ` q ) || l')
    eldv = w.s([w.s([], 'breq1',
                    '( p = ( 1st ` q ) -> ( p || l <-> ( 1st ` q ) || l ) )')], 'elrab',
               '( ( 1st ` q ) e. %s <-> ( ( 1st ` q ) e. NN /\ ( 1st ` q ) || l ) )' % DVL)
    inD = srq([srq([q1nn, dvd1], 'jca', '( ( 1st ` q ) e. NN /\ ( 1st ` q ) || l )'),
               srq([eldv], 'a1i',
                   '( ( 1st ` q ) e. %s <-> ( ( 1st ` q ) e. NN /\ ( 1st ` q ) || l ) )' % DVL)],
              'mpbird', '( 1st ` q ) e. %s' % DVL)
    ral1 = sl([inD], 'ralrimiva', 'A. q e. %s ( 1st ` q ) e. %s' % (RAB, DVL))
    ANQ = '( %s /\ n e. %s )' % (ARQ, RAB)
    snq = mkst(w, ANQ)
    nsa = w.s([], 'fveq2', '( v = n -> ( 1st ` v ) = ( 1st ` n ) )')
    nsb = w.s([], 'fveq2', '( v = n -> ( 2nd ` v ) = ( 2nd ` n ) )')
    nsc = w.s([nsa, nsb], 'oveq12d', '( v = n -> %s = %s )' % (P('v'), P('n')))
    nsd = w.s([nsc], 'eqeq2d', '( v = n -> ( l = %s <-> l = %s ) )' % (P('v'), P('n')))
    nse = w.s([nsd], 'elrab', '( n e. %s <-> ( n e. %s /\\ l = %s ) )' % (RAB, XII, P('n')))
    nmem = snq([snq([nse], 'a1i',
                    '( n e. %s <-> ( n e. %s /\\ l = %s ) )' % (RAB, XII, P('n'))),
                snq([], 'simpr', 'n e. %s' % RAB)], 'mpbid',
               '( n e. %s /\\ l = %s )' % (XII, P('n')))
    nxii = snq([nmem], 'simpld', 'n e. %s' % XII)
    nleq2 = snq([nmem], 'simprd', 'l = %s' % P('n'))
    AEQ = '( %s /\ ( 1st ` q ) = ( 1st ` n ) )' % ANQ
    seq = mkst(w, AEQ)
    f1eq = seq([], 'simpr', '( 1st ` q ) = ( 1st ` n )')
    peq = seq([seq([lift(w, qleq, AEQ)], 'eqcomd', '%s = l' % P('q')),
               lift(w, nleq2, AEQ)], 'eqtrd', '%s = %s' % (P('q'), P('n')))
    peq2 = seq([peq, seq([f1eq], 'oveq1d',
                         '%s = ( ( 1st ` n ) x. ( 2nd ` q ) )' % P('q'))], 'eqtr3d',
               '( ( 1st ` n ) x. ( 2nd ` q ) ) = %s' % P('n'))
    n1nn = seq([seq([seq([lift(w, iss, AEQ), seq([lift(w, nxii, AEQ), w.inst('xp1st')], 'syl',
                                                 '( 1st ` n ) e. %s' % I)], 'sseldd',
                         '( 1st ` n ) e. ( 1 ... U )'), w.inst('elfznn')], 'syl',
                    '( 1st ` n ) e. NN')], 'nncnd', '( 1st ` n ) e. CC')
    n1n0 = seq([seq([seq([lift(w, iss, AEQ), seq([lift(w, nxii, AEQ), w.inst('xp1st')], 'syl',
                                                 '( 1st ` n ) e. %s' % I)], 'sseldd',
                         '( 1st ` n ) e. ( 1 ... U )'), w.inst('elfznn')], 'syl',
                    '( 1st ` n ) e. NN')], 'nnne0d', '( 1st ` n ) =/= 0')
    n2c = seq([seq([seq([lift(w, iss, AEQ), seq([lift(w, nxii, AEQ), w.inst('xp2nd')], 'syl',
                                                '( 2nd ` n ) e. %s' % I)], 'sseldd',
                        '( 2nd ` n ) e. ( 1 ... U )'), w.inst('elfznn')], 'syl',
                   '( 2nd ` n ) e. NN')], 'nncnd', '( 2nd ` n ) e. CC')
    q2c = seq([lift(w, q2nn, AEQ)], 'nncnd', '( 2nd ` q ) e. CC')
    canc = seq([seq([q2c, n2c, n1nn, n1n0], 'mulcand',
                    '( ( ( 1st ` n ) x. ( 2nd ` q ) ) = %s <-> ( 2nd ` q ) = ( 2nd ` n ) )'
                    % P('n')), peq2], 'mpbid', '( 2nd ` q ) = ( 2nd ` n )')
    qeqn = seq([seq([lift(w, qxii, AEQ), lift(w, nxii, AEQ), w.inst('xpopth')], 'syl2anc',
                    '( ( ( 1st ` q ) = ( 1st ` n ) /\ ( 2nd ` q ) = ( 2nd ` n ) ) <-> q = n )'),
                seq([f1eq, canc], 'jca',
                    '( ( 1st ` q ) = ( 1st ` n ) /\ ( 2nd ` q ) = ( 2nd ` n ) )')], 'mpbid',
               'q = n')
    inj0 = snq([qeqn], 'ex', '( ( 1st ` q ) = ( 1st ` n ) -> q = n )')
    inj1 = srq([inj0], 'ralrimiva',
               'A. n e. %s ( ( 1st ` q ) = ( 1st ` n ) -> q = n )' % RAB)
    ral2 = sl([inj1], 'ralrimiva',
              'A. q e. %s A. n e. %s ( ( 1st ` q ) = ( 1st ` n ) -> q = n )' % (RAB, RAB))
    f1b = w.s([w.s([], 'eqid', '%s = %s' % (FMP, FMP)),
               w.s([], 'fveq2', '( q = n -> ( 1st ` q ) = ( 1st ` n ) )')], 'f1mpt',
              '( %s : %s -1-1-> %s <-> ( A. q e. %s ( 1st ` q ) e. %s /\ '
              'A. q e. %s A. n e. %s ( ( 1st ` q ) = ( 1st ` n ) -> q = n ) ) )'
              % (FMP, RAB, DVL, RAB, DVL, RAB, RAB))
    f1s = sl([sl([ral1, ral2], 'jca',
                 '( A. q e. %s ( 1st ` q ) e. %s /\ '
                 'A. q e. %s A. n e. %s ( ( 1st ` q ) = ( 1st ` n ) -> q = n ) )'
                 % (RAB, DVL, RAB, RAB)),
              sl([f1b], 'a1i',
                 '( %s : %s -1-1-> %s <-> ( A. q e. %s ( 1st ` q ) e. %s /\ '
                 'A. q e. %s A. n e. %s ( ( 1st ` q ) = ( 1st ` n ) -> q = n ) ) )'
                 % (FMP, RAB, DVL, RAB, DVL, RAB, RAB))], 'mpbird',
             '%s : %s -1-1-> %s' % (FMP, RAB, DVL))
    fex = sl([rabfin, w.inst('mptexg')], 'syl', '%s e. _V' % FMP)
    dex = sl([sl([w.s([], 'nnex', 'NN e. _V')], 'a1i', 'NN e. _V'), w.inst('rabexg')], 'syl',
             '%s e. _V' % DVL)
    hle = sl([fex, dex, f1s, w.inst('hashf1dmcdm')], 'syl3anc',
             '( # ` %s ) <_ ( # ` %s )' % (RAB, DVL))
    sgl = sl([lnn, w.inst('0sgm')], 'syl', '( 0 sigma l ) = ( # ` %s )' % DVL)
    hle2 = sl([hle, sl([sgl], 'eqcomd', '( # ` %s ) = ( 0 sigma l )' % DVL)], 'breqtrd',
              '( # ` %s ) <_ ( 0 sigma l )' % RAB)
    hre = sl([rabfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RAB)
    hrer = sl([hre], 'nn0red', '( # ` %s ) e. RR' % RAB)
    sgre = sl([sl([sl([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), lnn,
                   w.inst('sgmnncl')], 'syl2anc', '( 0 sigma l ) e. NN')], 'nnred',
               '( 0 sigma l ) e. RR')
    mulle = sl([sl([sl([hrer, sgre, sl([lire, sl([lirp], 'rpge0d', '0 <_ ( 1 / l )')], 'jca',
                                       '( ( 1 / l ) e. RR /\ 0 <_ ( 1 / l ) )')], '3jca',
                       '( ( # ` %s ) e. RR /\ ( 0 sigma l ) e. RR /\ '
                       '( ( 1 / l ) e. RR /\ 0 <_ ( 1 / l ) ) )' % RAB), hle2], 'jca',
                   '( ( ( # ` %s ) e. RR /\ ( 0 sigma l ) e. RR /\ '
                   '( ( 1 / l ) e. RR /\ 0 <_ ( 1 / l ) ) ) /\ ( # ` %s ) <_ ( 0 sigma l ) )'
                   % (RAB, RAB)), w.inst('lemul1a')], 'syl',
               '( ( # ` %s ) x. ( 1 / l ) ) <_ ( ( 0 sigma l ) x. ( 1 / l ) )' % RAB)
    dvr = sl([sl([sl([sgre], 'recnd', '( 0 sigma l ) e. CC'), sl([lrp], 'rpcnd', 'l e. CC'),
                  sl([lrp], 'rpne0d', 'l =/= 0')], '3jca',
                 '( ( 0 sigma l ) e. CC /\ l e. CC /\ l =/= 0 )'), w.inst('divrec')], 'syl',
             '%s = ( ( 0 sigma l ) x. ( 1 / l ) )' % DEN('l'))
    fib1 = sl([ss1, rsum], 'eqtr3d',
              'sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 ) = ( ( # ` %s ) x. ( 1 / l ) )'
              % (XII, P('q'), RAB))
    fib2 = sl([mulle, sl([dvr], 'eqcomd',
                         '( ( 0 sigma l ) x. ( 1 / l ) ) = %s' % DEN('l'))], 'breqtrd',
              '( ( # ` %s ) x. ( 1 / l ) ) <_ %s' % (RAB, DEN('l')))
    fib = sl([fib1, fib2], 'eqbrtrd',
             'sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 ) <_ %s' % (XII, P('q'), DEN('l')))
    ifre = sxq([lift(w, lire, AXQ), sxq([], '0red', '0 e. RR')], 'ifcld',
               'if ( l = %s , ( 1 / l ) , 0 ) e. RR' % P('q'))
    innre = sl([lift(w, xfin, AL), ifre], 'fsumrecl',
               'sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 ) e. RR' % (XII, P('q')))
    denre = sl([sgre, lrp], 'rerpdivcld', '%s e. RR' % DEN('l'))
    fsle = st([jfin, innre, denre, fib], 'fsumle',
              'sum_ l e. %s sum_ q e. %s if ( l = %s , ( 1 / l ) , 0 ) <_ sum_ l e. %s %s'
              % (J, XII, P('q'), J, DEN('l')))
    w.qed([lhs2, fsle], 'eqbrtrd',
          '( %s -> ( %s ^ 2 ) <_ sum_ l e. %s %s )' % (AQ, S, J, DEN('l')))
    return w


ALL = {'twinsq': twinsq}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
