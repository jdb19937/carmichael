"""Sortie v4a: the support, the multiplicity sum, the remainder and the error sum."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import QF, RT, OM, mkst
from cl import lift
from v4a_tb import SH, TMR, TRAL, TB, shparts
from v4a_sh import FMAP, AAS, WWS, TPS, PP
from lin import linarith

AQ = '( M e. NN /\\ T e. NN0 )'


def twinmono():
    w = WS('twinmono', 'The quadratic X ( M X + 1 ) is strictly increasing on the positive '
                       'integers.')
    A = '( ( M e. NN /\\ I e. NN /\\ O e. NN ) /\\ I < O )'
    st = mkst(w, A)
    mnn = st([st([], 'simpl', '( M e. NN /\\ I e. NN /\\ O e. NN )')], 'simp1d', 'M e. NN')
    inn = st([st([], 'simpl', '( M e. NN /\\ I e. NN /\\ O e. NN )')], 'simp2d', 'I e. NN')
    onn = st([st([], 'simpl', '( M e. NN /\\ I e. NN /\\ O e. NN )')], 'simp3d', 'O e. NN')
    ilt = st([], 'simpr', 'I < O')
    mre = st([mnn], 'nnred', 'M e. RR')
    ire = st([inn], 'nnred', 'I e. RR')
    ore = st([onn], 'nnred', 'O e. RR')
    mge = st([st([mnn], 'nnnn0d', 'M e. NN0')], 'nn0ge0d', '0 <_ M')
    ige = st([st([inn], 'nnnn0d', 'I e. NN0')], 'nn0ge0d', '0 <_ I')
    mile = st([st([st([ire, ore, st([mre, mge], 'jca', '( M e. RR /\\ 0 <_ M )')], '3jca',
                   '( I e. RR /\\ O e. RR /\\ ( M e. RR /\\ 0 <_ M ) )'),
                st([inn, onn, ilt], 'id', 'z')], 'id', 'z')], 'id', 'z')
    for _ in range(3):
        w.lines.pop()
    ilew = st([ire, ore, ilt], 'ltled', 'I <_ O')
    m1 = st([st([st([ire, ore, st([mre, mge], 'jca', '( M e. RR /\\ 0 <_ M )')], '3jca',
                   '( I e. RR /\\ O e. RR /\\ ( M e. RR /\\ 0 <_ M ) )'), ilew], 'jca',
                '( ( I e. RR /\\ O e. RR /\\ ( M e. RR /\\ 0 <_ M ) ) /\\ I <_ O )'),
              w.inst('lemul2a')], 'syl', '( M x. I ) <_ ( M x. O )')
    mire = st([mre, ire], 'remulcld', '( M x. I ) e. RR')
    more = st([mre, ore], 'remulcld', '( M x. O ) e. RR')
    one = st([], '1red', '1 e. RR')
    p1 = st([mire, more, one, m1], 'leadd1dd', '( ( M x. I ) + 1 ) <_ ( ( M x. O ) + 1 )')
    pire = st([mire, one], 'readdcld', '( ( M x. I ) + 1 ) e. RR')
    pore = st([more, one], 'readdcld', '( ( M x. O ) + 1 ) e. RR')
    step1 = st([st([st([pire, pore, st([ire, ige], 'jca', '( I e. RR /\\ 0 <_ I )')], '3jca',
                      '( ( ( M x. I ) + 1 ) e. RR /\\ ( ( M x. O ) + 1 ) e. RR /\\ '
                      '( I e. RR /\\ 0 <_ I ) )'), p1], 'jca',
                   '( ( ( ( M x. I ) + 1 ) e. RR /\\ ( ( M x. O ) + 1 ) e. RR /\\ '
                   '( I e. RR /\\ 0 <_ I ) ) /\\ ( ( M x. I ) + 1 ) <_ ( ( M x. O ) + 1 ) )'),
                w.inst('lemul2a')], 'syl',
               '%s <_ ( I x. ( ( M x. O ) + 1 ) )' % QF('I'))
    ppos = st([st([st([mnn, onn], 'nnmulcld', '( M x. O ) e. NN'),
                   st([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')], 'nnaddcld',
                  '( ( M x. O ) + 1 ) e. NN')], 'nngt0d', '0 < ( ( M x. O ) + 1 )')
    step2 = st([ire, ore, st([pore, ppos], 'jca',
                             '( ( ( M x. O ) + 1 ) e. RR /\\ 0 < ( ( M x. O ) + 1 ) )')],
               'id', 'z')
    w.lines.pop()
    step2 = st([st([st([ire, ore, st([pore, ppos], 'jca',
                                     '( ( ( M x. O ) + 1 ) e. RR /\\ '
                                     '0 < ( ( M x. O ) + 1 ) )')], '3jca',
                       '( I e. RR /\\ O e. RR /\\ ( ( ( M x. O ) + 1 ) e. RR /\\ '
                       '0 < ( ( M x. O ) + 1 ) ) )'), w.inst('ltmul1')], 'syl',
                   '( I < O <-> ( I x. ( ( M x. O ) + 1 ) ) < %s )' % QF('O')), ilt], 'mpbid',
               '( I x. ( ( M x. O ) + 1 ) ) < %s' % QF('O'))
    qire = st([ire, pire], 'remulcld', '%s e. RR' % QF('I'))
    mid = st([ire, pore], 'remulcld', '( I x. ( ( M x. O ) + 1 ) ) e. RR')
    qore = st([ore, pore], 'remulcld', '%s e. RR' % QF('O'))
    w.qed([qire, mid, qore, step1, step2], 'lelttrd',
          '( %s -> %s < %s )' % (A, QF('I'), QF('O')))
    return w


def twinqinj():
    w = WS('twinqinj', 'The map taking n to n ( M n + 1 ) is injective on an initial segment.')
    st = mkst(w, AQ)
    mnn = st([], 'simpl', 'M e. NN')
    AI = '( %s /\\ i e. ( 1 ... T ) )' % AQ
    si = mkst(w, AI)
    inn = si([si([], 'simpr', 'i e. ( 1 ... T )'), w.inst('elfznn')], 'syl', 'i e. NN')
    qnn = si([inn, si([si([lift(w, mnn, AI), inn], 'nnmulcld', '( M x. i ) e. NN'),
                       si([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')], 'nnaddcld',
                      '( ( M x. i ) + 1 ) e. NN')], 'nnmulcld', '%s e. NN' % QF('i'))
    ral1 = st([qnn], 'ralrimiva', 'A. i e. ( 1 ... T ) %s e. NN' % QF('i'))
    AIO = '( %s /\\ o e. ( 1 ... T ) )' % AI
    sio = mkst(w, AIO)
    onn = sio([sio([], 'simpr', 'o e. ( 1 ... T )'), w.inst('elfznn')], 'syl', 'o e. NN')
    AE = '( %s /\ %s = %s )' % (AIO, QF('i'), QF('o'))
    se = mkst(w, AE)
    inn2 = lift(w, inn, AE)
    onn2 = lift(w, onn, AE)
    mnn2 = lift(w, mnn, AE)
    ire = se([inn2], 'nnred', 'i e. RR')
    ore = se([onn2], 'nnred', 'o e. RR')
    onenn = se([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    qinn = se([inn2, se([se([mnn2, inn2], 'nnmulcld', '( M x. i ) e. NN'), onenn],
                        'nnaddcld', '( ( M x. i ) + 1 ) e. NN')], 'nnmulcld',
              '%s e. NN' % QF('i'))
    qonn = se([onn2, se([se([mnn2, onn2], 'nnmulcld', '( M x. o ) e. NN'), onenn],
                        'nnaddcld', '( ( M x. o ) + 1 ) e. NN')], 'nnmulcld',
              '%s e. NN' % QF('o'))
    qire = se([qinn], 'nnred', '%s e. RR' % QF('i'))
    qore = se([qonn], 'nnred', '%s e. RR' % QF('o'))
    eqio = se([], 'simpr', '%s = %s' % (QF('i'), QF('o')))
    # i < o is impossible
    ALT = '( %s /\ i < o )' % AE
    slt = mkst(w, ALT)
    mono1 = slt([slt([slt([lift(w, mnn2, ALT), lift(w, inn2, ALT), lift(w, onn2, ALT)], '3jca',
                          '( M e. NN /\ i e. NN /\ o e. NN )'),
                      slt([], 'simpr', 'i < o')], 'jca',
                     '( ( M e. NN /\ i e. NN /\ o e. NN ) /\ i < o )'),
                 w.inst('twinmono')], 'syl', '%s < %s' % (QF('i'), QF('o')))
    neq = slt([lift(w, qire, ALT), mono1], 'ltned', '%s =/= %s' % (QF('i'), QF('o')))
    nlt = se([lift(w, eqio, ALT), slt([neq], 'neneqd',
                                      '-. %s = %s' % (QF('i'), QF('o')))], 'pm2.65da',
             '-. i < o')
    # o < i is impossible
    AGT = '( %s /\ o < i )' % AE
    sgt = mkst(w, AGT)
    mono2 = sgt([sgt([sgt([lift(w, mnn2, AGT), lift(w, onn2, AGT), lift(w, inn2, AGT)], '3jca',
                          '( M e. NN /\ o e. NN /\ i e. NN )'),
                      sgt([], 'simpr', 'o < i')], 'jca',
                     '( ( M e. NN /\ o e. NN /\ i e. NN ) /\ o < i )'),
                 w.inst('twinmono')], 'syl', '%s < %s' % (QF('o'), QF('i')))
    neq2 = sgt([lift(w, qore, AGT), mono2], 'ltned', '%s =/= %s' % (QF('o'), QF('i')))
    ngt = se([lift(w, eqio, AGT),
              sgt([sgt([neq2], 'necomd', '%s =/= %s' % (QF('i'), QF('o')))], 'neneqd',
                  '-. %s = %s' % (QF('i'), QF('o')))], 'pm2.65da', '-. o < i')
    ieqo = se([se([ire, ore, w.inst('lttri3')], 'syl2anc',
                  '( i = o <-> ( -. i < o /\ -. o < i ) )'),
               se([nlt, ngt], 'jca', '( -. i < o /\ -. o < i )')], 'mpbird', 'i = o')
    inj0 = sio([ieqo], 'ex', '( %s = %s -> i = o )' % (QF('i'), QF('o')))
    inj1 = si([inj0], 'ralrimiva',
              'A. o e. ( 1 ... T ) ( %s = %s -> i = o )' % (QF('i'), QF('o')))
    ral2 = st([inj1], 'ralrimiva',
              'A. i e. ( 1 ... T ) A. o e. ( 1 ... T ) ( %s = %s -> i = o )'
              % (QF('i'), QF('o')))
    sb = w.s([w.s([], 'id', '( i = o -> i = o )'),
              w.s([w.s([], 'oveq2', '( i = o -> ( M x. i ) = ( M x. o ) )')], 'oveq1d',
                  '( i = o -> ( ( M x. i ) + 1 ) = ( ( M x. o ) + 1 ) )')], 'oveq12d',
             '( i = o -> %s = %s )' % (QF('i'), QF('o')))
    bic = w.s([w.s([], 'eqid', '%s = %s' % (FMAP, FMAP)), sb], 'f1mpt',
              '( %s : ( 1 ... T ) -1-1-> NN <-> ( A. i e. ( 1 ... T ) %s e. NN /\\ '
              'A. i e. ( 1 ... T ) A. o e. ( 1 ... T ) ( %s = %s -> i = o ) ) )'
              % (FMAP, QF('i'), QF('i'), QF('o')))
    w.qed([st([ral1, ral2], 'jca',
              '( A. i e. ( 1 ... T ) %s e. NN /\\ '
              'A. i e. ( 1 ... T ) A. o e. ( 1 ... T ) ( %s = %s -> i = o ) )'
              % (QF('i'), QF('i'), QF('o'))),
           st([bic], 'a1i',
              '( %s : ( 1 ... T ) -1-1-> NN <-> ( A. i e. ( 1 ... T ) %s e. NN /\\ '
              'A. i e. ( 1 ... T ) A. o e. ( 1 ... T ) ( %s = %s -> i = o ) ) )'
              % (FMAP, QF('i'), QF('i'), QF('o')))], 'mpbird',
          '( %s -> %s : ( 1 ... T ) -1-1-> NN )' % (AQ, FMAP))
    return w


TC = ('( %s /\ ( ( T e. NN0 /\ X = T ) /\ ( A = %s /\ W = %s ) ) )' % (TB, AAS, WWS))


def transport(w, condn, condv, csub, extra=''):
    """the sum over the support equals the sum over ( 1 ... T ) with body 1"""
    ANT = '( %s%s )' % (TC, extra) if extra else TC
    st = mkst(w, ANT)
    if extra:
        tc = st([], 'simpl', TC)
        tb = st([tc], 'simpld', TB)
        rest = st([tc], 'simprd',
                  '( ( T e. NN0 /\\ X = T ) /\\ ( A = %s /\\ W = %s ) )' % (AAS, WWS))
    else:
        tb = st([], 'simpl', TB)
        rest = st([], 'simpr',
                  '( ( T e. NN0 /\\ X = T ) /\\ ( A = %s /\\ W = %s ) )' % (AAS, WWS))
    sh = shparts(w, st, st([tb], 'simp1d', SH))
    mnn = st([st([tb], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    tn0 = st([st([rest], 'simpld', '( T e. NN0 /\ X = T )')], 'simpld', 'T e. NN0')
    aeq = st([st([rest], 'simprd', '( A = %s /\ W = %s )' % (AAS, WWS)), ], 'simpld',
             'A = %s' % AAS)
    weq = st([st([rest], 'simprd', '( A = %s /\ W = %s )' % (AAS, WWS)), ], 'simprd',
             'W = %s' % WWS)
    inj = st([st([mnn, tn0], 'jca', AQ), w.inst('twinqinj')], 'syl',
             '%s : ( 1 ... T ) -1-1-> NN' % FMAP)
    f1o = st([inj, w.inst('f1f1orn')], 'syl',
             '%s : ( 1 ... T ) -1-1-onto-> %s' % (FMAP, AAS))
    # values of the two mappings
    AV = '( %s /\ v e. ( 1 ... T ) )' % ANT
    sv = mkst(w, AV)
    vnn = sv([sv([], 'simpr', 'v e. ( 1 ... T )'), w.inst('elfznn')], 'syl', 'v e. NN')
    onenn = sv([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    qvnn = sv([vnn, sv([sv([lift(w, mnn, AV), vnn], 'nnmulcld', '( M x. v ) e. NN'), onenn],
                       'nnaddcld', '( ( M x. v ) + 1 ) e. NN')], 'nnmulcld',
              '%s e. NN' % QF('v'))
    qvex = sv([sv([qvnn], 'nnred', '%s e. RR' % QF('v'))], 'elexd', '%s e. _V' % QF('v'))
    fsub = w.s([w.s([], 'id', '( i = v -> i = v )'),
                w.s([w.s([], 'oveq2', '( i = v -> ( M x. i ) = ( M x. v ) )')], 'oveq1d',
                    '( i = v -> ( ( M x. i ) + 1 ) = ( ( M x. v ) + 1 ) )')], 'oveq12d',
               '( i = v -> %s = %s )' % (QF('i'), QF('v')))
    fval = sv([sv([sv([], 'simpr', 'v e. ( 1 ... T )'), qvex], 'jca',
                  '( v e. ( 1 ... T ) /\ %s e. _V )' % QF('v')),
               sv([w.s([fsub, w.s([], 'eqid', '%s = %s' % (FMAP, FMAP))], 'fvmptg',
                       '( ( v e. ( 1 ... T ) /\ %s e. _V ) -> ( %s ` v ) = %s )'
                       % (QF('v'), FMAP, QF('v')))], 'a1i',
                  '( ( v e. ( 1 ... T ) /\ %s e. _V ) -> ( %s ` v ) = %s )'
                  % (QF('v'), FMAP, QF('v')))], 'mpd', '( %s ` v ) = %s' % (FMAP, QF('v')))
    onex = w.s([], '1ex', '1 e. _V')
    wsub = w.s([], 'eqidd', '( c = %s -> 1 = 1 )' % QF('v'))
    wvq = sv([sv([qvnn, sv([onex], 'a1i', '1 e. _V')], 'jca',
                 '( %s e. NN /\ 1 e. _V )' % QF('v')),
              sv([w.s([wsub, w.s([], 'eqid', '%s = %s' % (WWS, WWS))], 'fvmptg',
                      '( ( %s e. NN /\ 1 e. _V ) -> ( %s ` %s ) = 1 )'
                      % (QF('v'), WWS, QF('v')))], 'a1i',
                 '( ( %s e. NN /\ 1 e. _V ) -> ( %s ` %s ) = 1 )'
                 % (QF('v'), WWS, QF('v')))], 'mpd', '( %s ` %s ) = 1' % (WWS, QF('v')))
    wvq2 = sv([sv([lift(w, weq, AV)], 'fveq1d',
                  '( W ` %s ) = ( %s ` %s )' % (QF('v'), WWS, QF('v'))), wvq], 'eqtrd',
              '( W ` %s ) = 1' % QF('v'))
    # the body closure over the support
    AN = '( %s /\ n e. %s )' % (ANT, AAS)
    sn = mkst(w, AN)
    assn = sn([sn([lift(w, mnn, AN), lift(w, tn0, AN)], 'jca', AQ),
               w.inst('twinsupp')], 'syl', '( %s e. Fin /\ %s C_ NN )' % (AAS, AAS))
    nnn = sn([sn([assn], 'simprd', '%s C_ NN' % AAS), sn([], 'simpr', 'n e. %s' % AAS)],
             'sseldd', 'n e. NN')
    wnv = sn([sn([nnn, sn([onex], 'a1i', '1 e. _V')], 'jca', '( n e. NN /\ 1 e. _V )'),
              sn([w.s([w.s([], 'eqidd', '( c = n -> 1 = 1 )'),
                       w.s([], 'eqid', '%s = %s' % (WWS, WWS))], 'fvmptg',
                      '( ( n e. NN /\ 1 e. _V ) -> ( %s ` n ) = 1 )' % WWS)], 'a1i',
                 '( ( n e. NN /\ 1 e. _V ) -> ( %s ` n ) = 1 )' % WWS)], 'mpd',
             '( %s ` n ) = 1' % WWS)
    wn2 = sn([sn([lift(w, weq, AN)], 'fveq1d', '( W ` n ) = ( %s ` n )' % WWS), wnv], 'eqtrd',
             '( W ` n ) = 1')
    wncc = sn([wn2, sn([sn([], '1red', '1 e. RR')], 'recnd', '1 e. CC')], 'eqeltrd',
              '( W ` n ) e. CC')
    bodycc = sn([wncc, sn([sn([], '0red', '0 e. RR')], 'recnd', '0 e. CC')], 'ifcld',
                'if ( %s , ( W ` n ) , 0 ) e. CC' % condn)
    # fsumf1o
    bsub = w.s([csub(w),
                w.s([], 'fveq2', '( n = %s -> ( W ` n ) = ( W ` %s ) )' % (QF('v'), QF('v')))],
               'ifbieq1d',
               '( n = %s -> if ( %s , ( W ` n ) , 0 ) = if ( %s , ( W ` %s ) , 0 ) )'
               % (QF('v'), condn, condv, QF('v')))
    tr = st([bsub, st([], 'fzfid', '( 1 ... T ) e. Fin'), f1o, fval, bodycc], 'fsumf1o',
            'sum_ n e. %s if ( %s , ( W ` n ) , 0 ) = '
            'sum_ v e. ( 1 ... T ) if ( %s , ( W ` %s ) , 0 )' % (AAS, condn, condv, QF('v')))
    lhs = st([aeq], 'sumeq1d',
             'sum_ n e. A if ( %s , ( W ` n ) , 0 ) = '
             'sum_ n e. %s if ( %s , ( W ` n ) , 0 )' % (condn, AAS, condn))
    rhs = st([sv([wvq2], 'ifeq1d',
                 'if ( %s , ( W ` %s ) , 0 ) = if ( %s , 1 , 0 )'
                 % (condv, QF('v'), condv))], 'sumeq2dv',
             'sum_ v e. ( 1 ... T ) if ( %s , ( W ` %s ) , 0 ) = '
             'sum_ v e. ( 1 ... T ) if ( %s , 1 , 0 )' % (condv, QF('v'), condv))
    w.qed([st([lhs, tr], 'eqtrd',
              'sum_ n e. A if ( %s , ( W ` n ) , 0 ) = '
              'sum_ v e. ( 1 ... T ) if ( %s , ( W ` %s ) , 0 )'
              % (condn, condv, QF('v'))), rhs], 'eqtrd',
          '( %s -> sum_ n e. A if ( %s , ( W ` n ) , 0 ) = '
          'sum_ v e. ( 1 ... T ) if ( %s , 1 , 0 ) )' % (ANT, condn, condv))
    return w


def twinms():
    w = WS('twinms', 'The multiplicity sum of the twin sieve at D counts the n up to T with '
                     'D dividing n ( M n + 1 ).')

    def csub(w):
        return w.s([], 'breq2',
                   '( n = %s -> ( D || n <-> D || %s ) )' % (QF('v'), QF('v')))
    return transport(w, 'D || n', 'D || %s' % QF('v'), csub, extra=' /\\ D e. NN')


def twinsfe():
    w = WS('twinsfe', 'The sifted sum of the twin sieve counts the n up to T with '
                      'n ( M n + 1 ) coprime to the sifting product.')

    def csub(w):
        return w.s([w.s([], 'oveq2',
                        '( n = %s -> ( P gcd n ) = ( P gcd %s ) )' % (QF('v'), QF('v')))],
                   'eqeq1d',
                   '( n = %s -> ( ( P gcd n ) = 1 <-> ( P gcd %s ) = 1 ) )'
                   % (QF('v'), QF('v')))
    return transport(w, '( P gcd n ) = 1', '( P gcd %s ) = 1' % QF('v'), csub)


ALL = {'twinmono': twinmono, 'twinqinj': twinqinj, 'twinms': twinms, 'twinsfe': twinsfe}



# --------------------------------------------------- the count of twin-type primes
TWP = '( v e. Prime /\\ ( ( M x. v ) + 1 ) e. Prime )'
TT = '{ v e. ( 1 ... T ) | %s }' % TWP
TWPN = '( n e. Prime /\\ ( ( M x. n ) + 1 ) e. Prime )'
TT2 = '{ n e. ( 1 ... T ) | ( %s /\\ Z < n ) }' % TWPN
SF = 'sum_ n e. A if ( ( P gcd n ) = 1 , ( W ` n ) , 0 )'
SFV = 'sum_ v e. ( 1 ... T ) if ( ( P gcd %s ) = 1 , 1 , 0 )' % QF('v')
TZ = 'A. y e. Prime ( y || P -> y <_ Z )'
ACNT = '( %s /\\ %s )' % (TC, TZ)


def elttsub(w, el, bv='v'):
    a = w.s([], 'eleq1', '( %s = %s -> ( %s e. Prime <-> %s e. Prime ) )' % (bv, el, bv, el))
    b = w.s([w.s([], 'oveq2',
                 '( %s = %s -> ( M x. %s ) = ( M x. %s ) )' % (bv, el, bv, el))], 'oveq1d',
            '( %s = %s -> ( ( M x. %s ) + 1 ) = ( ( M x. %s ) + 1 ) )' % (bv, el, bv, el))
    c = w.s([b], 'eleq1d',
            '( %s = %s -> ( ( ( M x. %s ) + 1 ) e. Prime <-> ( ( M x. %s ) + 1 ) e. Prime ) )'
            % (bv, el, bv, el))
    return w.s([a, c], 'anbi12d',
               '( %s = %s -> ( ( %s e. Prime /\\ ( ( M x. %s ) + 1 ) e. Prime ) <-> '
               '( %s e. Prime /\\ ( ( M x. %s ) + 1 ) e. Prime ) ) )'
               % (bv, el, bv, bv, el, el))


def twincnt():
    w = WS('twincnt', 'The number of primes up to T whose twin-type shift is prime is at '
                      'most the sifted sum plus the sifting bound.')
    st = mkst(w, ACNT)
    tc = st([], 'simpl', TC)
    tz = st([], 'simpr', TZ)
    tb = st([tc], 'simpld', TB)
    rest = st([tc], 'simprd',
              '( ( T e. NN0 /\\ X = T ) /\\ ( A = %s /\\ W = %s ) )' % (AAS, WWS))
    sh = shparts(w, st, st([tb], 'simp1d', SH))
    mnn = st([st([tb], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    znn = st([st([tb], 'simp2d', TMR)], 'simp2d', 'Z e. NN')
    tn0 = st([st([rest], 'simpld', '( T e. NN0 /\\ X = T )')], 'simpld', 'T e. NN0')
    pnn = sh['pnn']
    zn0 = st([znn], 'nnnn0d', 'Z e. NN0')
    zre = st([znn], 'nnred', 'Z e. RR')
    ttfin = st([st([], 'fzfid', '( 1 ... T ) e. Fin'),
                st([w.s([], 'ssrab2', '%s C_ ( 1 ... T )' % TT)], 'a1i',
                   '%s C_ ( 1 ... T )' % TT)], 'ssfid', '%s e. Fin' % TT)
    tt2fin = st([st([], 'fzfid', '( 1 ... T ) e. Fin'),
                 st([w.s([], 'ssrab2', '%s C_ ( 1 ... T )' % TT2)], 'a1i',
                    '%s C_ ( 1 ... T )' % TT2)], 'ssfid', '%s e. Fin' % TT2)
    fzfin = st([st([], 'fzfid', '( 1 ... Z ) e. Fin')], 'id', '( 1 ... Z ) e. Fin')
    w.lines.pop()
    fzfin = st([], 'fzfid', '( 1 ... Z ) e. Fin')
    # TT is contained in TT2 union ( 1 ... Z )
    AD = '( %s /\ d e. %s )' % (ACNT, TT)
    sd = mkst(w, AD)
    eldb = w.s([elttsub(w, 'd')], 'elrab',
               '( d e. %s <-> ( d e. ( 1 ... T ) /\ '
               '( d e. Prime /\ ( ( M x. d ) + 1 ) e. Prime ) ) )' % TT)
    dmem = sd([sd([eldb], 'a1i',
                  '( d e. %s <-> ( d e. ( 1 ... T ) /\ '
                  '( d e. Prime /\ ( ( M x. d ) + 1 ) e. Prime ) ) )' % TT),
               sd([], 'simpr', 'd e. %s' % TT)], 'mpbid',
              '( d e. ( 1 ... T ) /\ ( d e. Prime /\ ( ( M x. d ) + 1 ) e. Prime ) )')
    dfz = sd([dmem], 'simpld', 'd e. ( 1 ... T )')
    dtw = sd([dmem], 'simprd', '( d e. Prime /\ ( ( M x. d ) + 1 ) e. Prime )')
    dnn = sd([dfz, w.inst('elfznn')], 'syl', 'd e. NN')
    dre = sd([dnn], 'nnred', 'd e. RR')
    sb2 = w.s([elttsub(w, 'd', 'n'),
               w.s([], 'breq2', '( n = d -> ( Z < n <-> Z < d ) )')], 'anbi12d',
              '( n = d -> ( ( %s /\ Z < n ) <-> ( ( d e. Prime /\ '
              '( ( M x. d ) + 1 ) e. Prime ) /\ Z < d ) ) )' % TWPN)
    eldb2 = w.s([sb2], 'elrab',
                '( d e. %s <-> ( d e. ( 1 ... T ) /\ ( ( d e. Prime /\ '
                '( ( M x. d ) + 1 ) e. Prime ) /\ Z < d ) ) )' % TT2)
    ss1 = w.s([], 'ssun1', '%s C_ ( %s u. ( 1 ... Z ) )' % (TT2, TT2))
    ss2 = w.s([], 'ssun2', '( 1 ... Z ) C_ ( %s u. ( 1 ... Z ) )' % TT2)
    ADL = '( %s /\ d <_ Z )' % AD
    sdl = mkst(w, ADL)
    dinfz = sdl([sdl([lift(w, dnn, ADL), lift(w, znn, ADL), sdl([], 'simpr', 'd <_ Z')], '3jca',
                     '( d e. NN /\ Z e. NN /\ d <_ Z )'),
                 sdl([w.s([], 'elfz1b',
                          '( d e. ( 1 ... Z ) <-> ( d e. NN /\ Z e. NN /\ d <_ Z ) )')], 'a1i',
                     '( d e. ( 1 ... Z ) <-> ( d e. NN /\ Z e. NN /\ d <_ Z ) )')], 'mpbird',
                'd e. ( 1 ... Z )')
    dun1 = sdl([sdl([ss2], 'a1i', '( 1 ... Z ) C_ ( %s u. ( 1 ... Z ) )' % TT2), dinfz],
               'sseldd', 'd e. ( %s u. ( 1 ... Z ) )' % TT2)
    ADN = '( %s /\ -. d <_ Z )' % AD
    sdn = mkst(w, ADN)
    zltd = sdn([sdn([lift(w, zre, ADN), lift(w, dre, ADN), w.inst('ltnle')], 'syl2anc',
                    '( Z < d <-> -. d <_ Z )'), sdn([], 'simpr', '-. d <_ Z')], 'mpbird',
               'Z < d')
    din2c = sdn([sdn([lift(w, dfz, ADN),
                      sdn([lift(w, dtw, ADN), zltd], 'jca',
                          '( ( d e. Prime /\ ( ( M x. d ) + 1 ) e. Prime ) /\ Z < d )')],
                     'jca',
                     '( d e. ( 1 ... T ) /\ ( ( d e. Prime /\ '
                     '( ( M x. d ) + 1 ) e. Prime ) /\ Z < d ) )'),
                 sdn([eldb2], 'a1i',
                     '( d e. %s <-> ( d e. ( 1 ... T ) /\ ( ( d e. Prime /\ '
                     '( ( M x. d ) + 1 ) e. Prime ) /\ Z < d ) ) )' % TT2)], 'mpbird',
                'd e. %s' % TT2)
    dun2d = sdn([sdn([ss1], 'a1i', '%s C_ ( %s u. ( 1 ... Z ) )' % (TT2, TT2)), din2c],
                'sseldd', 'd e. ( %s u. ( 1 ... Z ) )' % TT2)
    dunf = sd([dun1, dun2d], 'pm2.61dan', 'd e. ( %s u. ( 1 ... Z ) )' % TT2)
    ttsub = st([st([dunf], 'ex', '( d e. %s -> d e. ( %s u. ( 1 ... Z ) ) )' % (TT, TT2))],
               'ssrdv', '%s C_ ( %s u. ( 1 ... Z ) )' % (TT, TT2))
    hle1 = st([st([st([tt2fin, fzfin], 'jca',
                      '( %s e. Fin /\\ ( 1 ... Z ) e. Fin )' % TT2), w.inst('unfi')], 'syl',
                  '( %s u. ( 1 ... Z ) ) e. Fin' % TT2), ttsub, w.inst('hashss')], 'syl2anc',
              '( # ` %s ) <_ ( # ` ( %s u. ( 1 ... Z ) ) )' % (TT, TT2))
    hle2 = st([tt2fin, fzfin, w.inst('hashun2')], 'syl2anc',
              '( # ` ( %s u. ( 1 ... Z ) ) ) <_ ( ( # ` %s ) + ( # ` ( 1 ... Z ) ) )'
              % (TT2, TT2))
    hfz = st([zn0, w.inst('hashfz1')], 'syl', '( # ` ( 1 ... Z ) ) = Z')
    hle3 = st([hle2, st([hfz], 'oveq2d',
                        '( ( # ` %s ) + ( # ` ( 1 ... Z ) ) ) = ( ( # ` %s ) + Z )'
                        % (TT2, TT2))], 'breqtrd',
              '( # ` ( %s u. ( 1 ... Z ) ) ) <_ ( ( # ` %s ) + Z )' % (TT2, TT2))
    htt = st([ttfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TT)
    htt2 = st([tt2fin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TT2)
    httre = st([htt], 'nn0red', '( # ` %s ) e. RR' % TT)
    htt2re = st([htt2], 'nn0red', '( # ` %s ) e. RR' % TT2)
    unre = st([st([st([st([tt2fin, fzfin], 'jca',
                          '( %s e. Fin /\\ ( 1 ... Z ) e. Fin )' % TT2), w.inst('unfi')], 'syl',
                      '( %s u. ( 1 ... Z ) ) e. Fin' % TT2), w.inst('hashcl')], 'syl',
                  '( # ` ( %s u. ( 1 ... Z ) ) ) e. NN0' % TT2)], 'nn0red',
               '( # ` ( %s u. ( 1 ... Z ) ) ) e. RR' % TT2)
    sumre = st([htt2re, zre], 'readdcld', '( ( # ` %s ) + Z ) e. RR' % TT2)
    split = st([httre, unre, sumre, hle1, hle3], 'letrd',
               '( # ` %s ) <_ ( ( # ` %s ) + Z )' % (TT, TT2))
    # ---- the large twin-type primes survive the sieve
    AV = '( %s /\ v e. %s )' % (ACNT, TT2)
    sv = mkst(w, AV)
    sbv = w.s([elttsub(w, 'v', 'n'),
               w.s([], 'breq2', '( n = v -> ( Z < n <-> Z < v ) )')], 'anbi12d',
              '( n = v -> ( ( %s /\ Z < n ) <-> ( %s /\ Z < v ) ) )' % (TWPN, TWP))
    rid2 = w.s([sbv], 'elrab',
               '( v e. %s <-> ( v e. ( 1 ... T ) /\ ( %s /\ Z < v ) ) )' % (TT2, TWP))
    vmem = sv([sv([rid2], 'a1i',
                  '( v e. %s <-> ( v e. ( 1 ... T ) /\ ( %s /\ Z < v ) ) )' % (TT2, TWP)),
               sv([], 'simpr', 'v e. %s' % TT2)], 'mpbid',
              '( v e. ( 1 ... T ) /\ ( %s /\ Z < v ) )' % TWP)
    vfz = sv([vmem], 'simpld', 'v e. ( 1 ... T )')
    vrest = sv([vmem], 'simprd', '( %s /\ Z < v )' % TWP)
    vtw = sv([vrest], 'simpld', TWP)
    vgz = sv([vrest], 'simprd', 'Z < v')
    vprm = sv([vtw], 'simpld', 'v e. Prime')
    vsprm = sv([vtw], 'simprd', '( ( M x. v ) + 1 ) e. Prime')
    vnn = sv([vfz, w.inst('elfznn')], 'syl', 'v e. NN')
    vre = sv([vnn], 'nnred', 'v e. RR')
    mvnn = sv([lift(w, mnn, AV), vnn], 'nnmulcld', '( M x. v ) e. NN')
    mv1nn = sv([mvnn, sv([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')], 'nnaddcld',
               '( ( M x. v ) + 1 ) e. NN')
    qvnn = sv([vnn, mv1nn], 'nnmulcld', '%s e. NN' % QF('v'))
    mvre = sv([mvnn], 'nnred', '( M x. v ) e. RR')
    mv1re = sv([mv1nn], 'nnred', '( ( M x. v ) + 1 ) e. RR')
    # v <_ ( M x. v )
    mge1 = sv([lift(w, mnn, AV), w.inst('nnge1')], 'syl', '1 <_ M')
    vge0 = sv([sv([vnn], 'nnnn0d', 'v e. NN0')], 'nn0ge0d', '0 <_ v')
    onere2 = sv([], '1red', '1 e. RR')
    mre2 = sv([lift(w, mnn, AV)], 'nnred', 'M e. RR')
    vlemv0 = sv([sv([sv([onere2, mre2, sv([vre, vge0], 'jca', '( v e. RR /\ 0 <_ v )')], '3jca',
                        '( 1 e. RR /\ M e. RR /\ ( v e. RR /\ 0 <_ v ) )'), mge1], 'jca',
                    '( ( 1 e. RR /\ M e. RR /\ ( v e. RR /\ 0 <_ v ) ) /\ 1 <_ M )'),
                 w.inst('lemul1a')], 'syl', '( 1 x. v ) <_ ( M x. v )')
    vlemv = sv([sv([sv([sv([vre], 'recnd', 'v e. CC')], 'mullidd', '( 1 x. v ) = v')],
                   'eqcomd', 'v = ( 1 x. v )'), vlemv0], 'eqbrtrd', 'v <_ ( M x. v )')
    # no prime divides both P and the quadratic
    AVP = '( %s /\ p e. Prime )' % AV
    svp = mkst(w, AVP)
    pprm = svp([], 'simpr', 'p e. Prime')
    puz = svp([pprm, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )')
    pnn2 = svp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    pre = svp([pnn2], 'nnred', 'p e. RR')
    AVB = '( %s /\ ( p || P /\ p || %s ) )' % (AVP, QF('v'))
    svb = mkst(w, AVB)
    pdp = svb([svb([], 'simpr', '( p || P /\ p || %s )' % QF('v'))], 'simpld', 'p || P')
    pdq = svb([svb([], 'simpr', '( p || P /\ p || %s )' % QF('v'))], 'simprd',
              'p || %s' % QF('v'))
    idp = w.s([], 'id', '( y = p -> y = p )')
    zsb, znew = w.wcongr('( y || P -> y <_ Z )', {'y': 'p'}, 'y = p', {'y': idp})
    plez = svb([svb([zsb, lift(w, tz, AVB), lift(w, pprm, AVB)], 'rspcdva', znew), pdp],
               'mpd', 'p <_ Z')
    eucl = svb([lift(w, pprm, AVB), svb([lift(w, vnn, AVB)], 'nnzd', 'v e. ZZ'),
                svb([lift(w, mv1nn, AVB)], 'nnzd', '( ( M x. v ) + 1 ) e. ZZ'),
                w.inst('euclemma')], 'syl3anc',
               '( p || %s <-> ( p || v \/ p || ( ( M x. v ) + 1 ) ) )' % QF('v'))
    ordv = svb([eucl, pdq], 'mpbid', '( p || v \/ p || ( ( M x. v ) + 1 ) )')
    AV1 = '( %s /\ p || v )' % AVB
    sv1 = mkst(w, AV1)
    peqv = sv1([sv1([lift(w, puz, AV1), lift(w, vprm, AV1), w.inst('dvdsprm')], 'syl2anc',
                    '( p || v <-> p = v )'), sv1([], 'simpr', 'p || v')], 'mpbid', 'p = v')
    case1 = sv1([sv1([peqv], 'eqcomd', 'v = p'), lift(w, plez, AV1)], 'eqbrtrd', 'v <_ Z')
    AV2 = '( %s /\ p || ( ( M x. v ) + 1 ) )' % AVB
    sv2 = mkst(w, AV2)
    peqs = sv2([sv2([lift(w, puz, AV2), lift(w, vsprm, AV2), w.inst('dvdsprm')], 'syl2anc',
                    '( p || ( ( M x. v ) + 1 ) <-> p = ( ( M x. v ) + 1 ) )'),
                sv2([], 'simpr', 'p || ( ( M x. v ) + 1 )')], 'mpbid',
               'p = ( ( M x. v ) + 1 )')
    mv1lez = sv2([sv2([peqs], 'eqcomd', '( ( M x. v ) + 1 ) = p'), lift(w, plez, AV2)],
                 'eqbrtrd', '( ( M x. v ) + 1 ) <_ Z')
    case2 = linarith(w, AV2, [lift(w, vlemv, AV2), mv1lez], 'v <_ Z',
                     leaves={'v': lift(w, vre, AV2), '( M x. v )': lift(w, mvre, AV2),
                             'Z': lift(w, zre, AV2)})
    vlez = svb([case1, case2, ordv], 'mpjaodan', 'v <_ Z')
    nvle = svb([svb([svb([lift(w, zre, AVB), lift(w, vre, AVB), w.inst('ltnle')], 'syl2anc',
                         '( Z < v <-> -. v <_ Z )')], 'biimpd', '( Z < v -> -. v <_ Z )'),
                lift(w, vgz, AVB)], 'mpd', '-. v <_ Z')
    nand = svp([vlez, nvle], 'pm2.65da', '-. ( p || P /\ p || %s )' % QF('v'))
    ralp = sv([nand], 'ralrimiva', 'A. p e. Prime -. ( p || P /\ p || %s )' % QF('v'))
    nex = sv([sv([w.s([], 'ralnex',
                      '( A. p e. Prime -. ( p || P /\ p || %s ) <-> '
                      '-. E. p e. Prime ( p || P /\ p || %s ) )' % (QF('v'), QF('v')))], 'a1i',
                 '( A. p e. Prime -. ( p || P /\ p || %s ) <-> '
                 '-. E. p e. Prime ( p || P /\ p || %s ) )' % (QF('v'), QF('v'))), ralp],
              'mpbid', '-. E. p e. Prime ( p || P /\ p || %s )' % QF('v'))
    bicop = sv([lift(w, pnn, AV), qvnn], 'prmdvdsncoprmbd',
               '( E. p e. Prime ( p || P /\ p || %s ) <-> ( P gcd %s ) =/= 1 )'
               % (QF('v'), QF('v')))
    cop = sv([sv([bicop, nex], 'mtbid', '-. ( P gcd %s ) =/= 1' % QF('v')), w.inst('nne')],
             'sylib', '( P gcd %s ) = 1' % QF('v'))
    onev = sv([cop], 'iftrued', 'if ( ( P gcd %s ) = 1 , 1 , 0 ) = 1' % QF('v'))
    # the sum over TT2 is its cardinality
    sum1 = st([st([onev], 'sumeq2dv',
                  'sum_ v e. %s if ( ( P gcd %s ) = 1 , 1 , 0 ) = sum_ v e. %s 1'
                  % (TT2, QF('v'), TT2)),
               st([st([tt2fin, st([st([], '1red', '1 e. RR')], 'recnd', '1 e. CC')], 'jca',
                      '( %s e. Fin /\ 1 e. CC )' % TT2), w.inst('fsumconst')], 'syl',
                  'sum_ v e. %s 1 = ( ( # ` %s ) x. 1 )' % (TT2, TT2))], 'eqtrd',
              'sum_ v e. %s if ( ( P gcd %s ) = 1 , 1 , 0 ) = ( ( # ` %s ) x. 1 )'
              % (TT2, QF('v'), TT2))
    sum2 = st([sum1, st([st([htt2re], 'recnd', '( # ` %s ) e. CC' % TT2)], 'mulridd',
                        '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (TT2, TT2))], 'eqtrd',
              'sum_ v e. %s if ( ( P gcd %s ) = 1 , 1 , 0 ) = ( # ` %s )'
              % (TT2, QF('v'), TT2))
    # the sum over TT2 is at most the sum over ( 1 ... T )
    AVT = '( %s /\ v e. ( 1 ... T ) )' % ACNT
    svt = mkst(w, AVT)
    ifre = svt([svt([], '1red', '1 e. RR'), svt([], '0red', '0 e. RR')], 'ifcld',
               'if ( ( P gcd %s ) = 1 , 1 , 0 ) e. RR' % QF('v'))
    AVTT = '( %s /\\ ( P gcd %s ) = 1 )' % (AVT, QF('v'))
    svtt = mkst(w, AVTT)
    ifg1 = svtt([svtt([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'),
                 svtt([svtt([], 'simpr', '( P gcd %s ) = 1' % QF('v'))], 'iftrued',
                      'if ( ( P gcd %s ) = 1 , 1 , 0 ) = 1' % QF('v'))], 'breqtrrd',
                '0 <_ if ( ( P gcd %s ) = 1 , 1 , 0 )' % QF('v'))
    AVTF = '( %s /\\ -. ( P gcd %s ) = 1 )' % (AVT, QF('v'))
    svtf = mkst(w, AVTF)
    ifg0 = svtf([svtf([svtf([], '0red', '0 e. RR')], 'leidd', '0 <_ 0'),
                 svtf([svtf([], 'simpr', '-. ( P gcd %s ) = 1' % QF('v'))], 'iffalsed',
                      'if ( ( P gcd %s ) = 1 , 1 , 0 ) = 0' % QF('v'))], 'breqtrrd',
                '0 <_ if ( ( P gcd %s ) = 1 , 1 , 0 )' % QF('v'))
    ifge = svt([ifg1, ifg0], 'pm2.61dan',
               '0 <_ if ( ( P gcd %s ) = 1 , 1 , 0 )' % QF('v'))
    less = st([st([], 'fzfid', '( 1 ... T ) e. Fin'), ifre, ifge,
               st([w.s([], 'ssrab2', '%s C_ ( 1 ... T )' % TT2)], 'a1i',
                  '%s C_ ( 1 ... T )' % TT2)], 'fsumless',
              'sum_ v e. %s if ( ( P gcd %s ) = 1 , 1 , 0 ) <_ %s' % (TT2, QF('v'), SFV))
    sfe = st([tc, w.inst('twinsfe')], 'syl', '%s = %s' % (SF, SFV))
    httle = st([sum2, less], 'eqbrtrrd', '( # ` %s ) <_ %s' % (TT2, SFV))
    httle2 = st([httle, st([sfe], 'eqcomd', '%s = %s' % (SFV, SF))], 'breqtrd',
                '( # ` %s ) <_ %s' % (TT2, SF))
    sfre = st([sfe, st([st([], 'fzfid', '( 1 ... T ) e. Fin'), ifre], 'fsumrecl',
                       '%s e. RR' % SFV)], 'eqeltrd', '%s e. RR' % SF)
    addle = st([htt2re, sfre, zre, httle2], 'leadd1dd',
               '( ( # ` %s ) + Z ) <_ ( %s + Z )' % (TT2, SF))
    w.qed([sfre, httre,
           st([httre, sumre, st([sfre, zre], 'readdcld', '( %s + Z ) e. RR' % SF), split,
               addle], 'letrd', '( # ` %s ) <_ ( %s + Z )' % (TT, SF))], '3jca',
          '( %s -> ( %s e. RR /\\ ( # ` %s ) e. RR /\\ ( # ` %s ) <_ ( %s + Z ) ) )'
          % (ACNT, SF, TT, TT, SF))
    return w


ALL['twincnt'] = twincnt



if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
