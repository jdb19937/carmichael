"""Sortie v4a: the root count of a product of distinct primes avoiding M."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import QF, RT, mkst
from cl import lift

YZ = '( y u. { z } )'
QN = '( Q u. { N } )'


def PR(E):
    return 'prod_ p e. %s p' % E


def CNT(E):
    return '( # ` %s )' % RT(PR(E))


def PROP(E):
    return ('( ( M e. NN /\\ %s C_ Prime /\\ A. n e. %s -. n || M ) -> '
            '%s = ( 2 ^ ( # ` %s ) ) )' % (E, E, CNT(E), E))


def subst(w, E):
    a1 = w.s([], 'sseq1', '( x = %s -> ( x C_ Prime <-> %s C_ Prime ) )' % (E, E))
    a2 = w.s([], 'raleq',
             '( x = %s -> ( A. n e. x -. n || M <-> A. n e. %s -. n || M ) )' % (E, E))
    a3 = w.s([a1, a2], '3anbi23d',
             '( x = %s -> ( ( M e. NN /\\ x C_ Prime /\\ A. n e. x -. n || M ) <-> '
             '( M e. NN /\\ %s C_ Prime /\\ A. n e. %s -. n || M ) ) )' % (E, E, E))
    b1 = w.s([], 'prodeq1', '( x = %s -> %s = %s )' % (E, PR('x'), PR(E)))
    b2 = w.s([b1], 'oveq2d', '( x = %s -> ( 0 ..^ %s ) = ( 0 ..^ %s ) )' % (E, PR('x'), PR(E)))
    b3 = w.s([b1], 'breq1d',
             '( x = %s -> ( %s || %s <-> %s || %s ) )' % (E, PR('x'), QF('v'), PR(E), QF('v')))
    b4 = w.s([b2, b3], 'rabeqbidv', '( x = %s -> %s = %s )' % (E, RT(PR('x')), RT(PR(E))))
    b5 = w.s([b4], 'fveq2d', '( x = %s -> %s = %s )' % (E, CNT('x'), CNT(E)))
    c1 = w.s([], 'fveq2', '( x = %s -> ( # ` x ) = ( # ` %s ) )' % (E, E))
    c2 = w.s([c1], 'oveq2d', '( x = %s -> ( 2 ^ ( # ` x ) ) = ( 2 ^ ( # ` %s ) ) )' % (E, E))
    d = w.s([b5, c2], 'eqeq12d',
            '( x = %s -> ( %s = ( 2 ^ ( # ` x ) ) <-> %s = ( 2 ^ ( # ` %s ) ) ) )'
            % (E, CNT('x'), CNT(E), E))
    return w.s([a3, d], 'imbi12d', '( x = %s -> ( %s <-> %s ) )' % (E, PROP('x'), PROP(E)))


def rteq(stf, eq, P1, P2):
    o = stf([eq], 'oveq2d', '( 0 ..^ %s ) = ( 0 ..^ %s )' % (P1, P2))
    b = stf([eq], 'breq1d', '( %s || %s <-> %s || %s )' % (P1, QF('v'), P2, QF('v')))
    r = stf([o, b], 'rabeqbidv', '%s = %s' % (RT(P1), RT(P2)))
    return stf([r], 'fveq2d', '( # ` %s ) = ( # ` %s )' % (RT(P1), RT(P2)))


AS = ('( ( Q e. Fin /\\ Q C_ Prime /\\ A. n e. Q -. n || M ) /\\ '
      '( M e. NN /\\ N e. Prime /\\ -. N || M ) /\\ -. N e. Q )')


def rcpstep():
    w = WS('rcpstep', 'The inductive step of the root count: adjoining one prime not '
                      'dividing M to the modulus set doubles the number of roots.')
    st = mkst(w, AS)
    c1 = st([], 'simp1', '( Q e. Fin /\\ Q C_ Prime /\\ A. n e. Q -. n || M )')
    c2 = st([], 'simp2', '( M e. NN /\\ N e. Prime /\\ -. N || M )')
    qfin = st([c1], 'simp1d', 'Q e. Fin')
    yprm = st([c1], 'simp2d', 'Q C_ Prime')
    mnn = st([c2], 'simp1d', 'M e. NN')
    zprm = st([c2], 'simp2d', 'N e. Prime')
    nzm = st([c2], 'simp3d', '-. N || M')
    nzq = st([], 'simp3', '-. N e. Q')
    # the product over Q is a positive integer and N is coprime to it
    AP = '( %s /\\ p e. Q )' % AS
    sp = mkst(w, AP)
    pprm = sp([lift(w, yprm, AP), sp([], 'simpr', 'p e. Q')], 'sseldd', 'p e. Prime')
    pnn = sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    prynn = st([qfin, pnn], 'fprodnncl', '%s e. NN' % PR('Q'))
    pryz = st([prynn], 'nnzd', '%s e. ZZ' % PR('Q'))
    znn = st([zprm, w.inst('prmnn')], 'syl', 'N e. NN')
    zex = st([st([znn], 'nnred', 'N e. RR')], 'elexd', 'N e. _V')
    ypw = st([qfin, yprm], 'elpwd', 'Q e. ~P Prime')
    yin = st([ypw, qfin], 'elind', 'Q e. ( ~P Prime i^i Fin )')
    cbvq = w.s([w.s([], 'id', '( q = p -> q = p )')], 'cbvprodv',
               'prod_ q e. Q q = %s' % PR('Q'))
    ndvd0 = st([yin, zprm, nzq, w.inst('prmprodndvds')], 'syl3anc', '-. N || prod_ q e. Q q')
    ndvd = st([st([st([cbvq], 'a1i', 'prod_ q e. Q q = %s' % PR('Q'))], 'breq2d',
                  '( N || prod_ q e. Q q <-> N || %s )' % PR('Q')), ndvd0], 'mtbid',
              '-. N || %s' % PR('Q'))
    cop0 = st([st([zprm, pryz, w.inst('coprm')], 'syl2anc',
                  '( -. N || %s <-> ( N gcd %s ) = 1 )' % (PR('Q'), PR('Q'))), ndvd], 'mpbid',
              '( N gcd %s ) = 1' % PR('Q'))
    cop = st([st([pryz, st([znn], 'nnzd', 'N e. ZZ'), w.inst('gcdcom')], 'syl2anc',
                 '( %s gcd N ) = ( N gcd %s )' % (PR('Q'), PR('Q'))), cop0], 'eqtrd',
             '( %s gcd N ) = 1' % PR('Q'))
    # split the product
    nfp = w.s([], 'nfv', 'F/ p %s' % AS)
    nfz = w.s([], 'nfcv', 'F/_ p N')
    sbp = w.s([], 'id', '( p = N -> p = N )')
    pcc = sp([pnn], 'nncnd', 'p e. CC')
    zcc = st([znn], 'nncnd', 'N e. CC')
    split = st([nfp, nfz, qfin, zex, nzq, pcc, sbp, zcc], 'fprodsplitsn',
               '%s = ( %s x. N )' % (PR(QN), PR('Q')))
    hsplit = rteq(st, split, PR(QN), '( %s x. N )' % PR('Q'))
    rm = st([st([mnn, st([prynn, znn, cop], '3jca',
                         '( %s e. NN /\\ N e. NN /\\ ( %s gcd N ) = 1 )' % (PR('Q'), PR('Q')))],
                'jca',
                '( M e. NN /\\ ( %s e. NN /\\ N e. NN /\\ ( %s gcd N ) = 1 ) )'
                % (PR('Q'), PR('Q'))), w.inst('rcmul')], 'syl',
            '( # ` %s ) = ( %s x. ( # ` %s ) )'
            % (RT('( %s x. N )' % PR('Q')), CNT('Q'), RT('N')))
    rp = st([st([mnn, zprm, nzm], '3jca', '( M e. NN /\\ N e. Prime /\\ -. N || M )'),
             w.inst('rcprm')], 'syl', '( # ` %s ) = 2' % RT('N'))
    lhs0 = st([hsplit, rm], 'eqtrd',
              '%s = ( %s x. ( # ` %s ) )' % (CNT(QN), CNT('Q'), RT('N')))
    hu = st([zex, st([qfin, nzq], 'jca', '( Q e. Fin /\\ -. N e. Q )'),
             w.inst('hashunsng')], 'sylc', '( # ` %s ) = ( ( # ` Q ) + 1 )' % QN)
    hyn0 = st([qfin, w.inst('hashcl')], 'syl', '( # ` Q ) e. NN0')
    ep1 = st([st([], '2cnd', '2 e. CC'), hyn0, w.inst('expp1')], 'syl2anc',
             '( 2 ^ ( ( # ` Q ) + 1 ) ) = ( ( 2 ^ ( # ` Q ) ) x. 2 )')
    rhs = st([st([hu], 'oveq2d', '( 2 ^ ( # ` %s ) ) = ( 2 ^ ( ( # ` Q ) + 1 ) )' % QN),
              ep1], 'eqtrd', '( 2 ^ ( # ` %s ) ) = ( ( 2 ^ ( # ` Q ) ) x. 2 )' % QN)
    # under the induction hypothesis
    AI = '( %s /\\ %s = ( 2 ^ ( # ` Q ) ) )' % (AS, CNT('Q'))
    si = mkst(w, AI)
    ih = si([], 'simpr', '%s = ( 2 ^ ( # ` Q ) )' % CNT('Q'))
    mid = si([ih, lift(w, rp, AI)], 'oveq12d',
             '( %s x. ( # ` %s ) ) = ( ( 2 ^ ( # ` Q ) ) x. 2 )' % (CNT('Q'), RT('N')))
    conc = si([si([lift(w, lhs0, AI), mid], 'eqtrd',
                  '%s = ( ( 2 ^ ( # ` Q ) ) x. 2 )' % CNT(QN)),
               si([lift(w, rhs, AI)], 'eqcomd',
                  '( ( 2 ^ ( # ` Q ) ) x. 2 ) = ( 2 ^ ( # ` %s ) )' % QN)], 'eqtrd',
              '%s = ( 2 ^ ( # ` %s ) )' % (CNT(QN), QN))
    w.qed([conc], 'ex',
          '( %s -> ( %s = ( 2 ^ ( # ` Q ) ) -> %s = ( 2 ^ ( # ` %s ) ) ) )'
          % (AS, CNT('Q'), CNT(QN), QN))
    return w


def rcprod():
    w = WS('rcprod', 'The quadratic X ( M X + 1 ) has 2 ^ n roots modulo a product of n '
                     'distinct primes none of which divides M.')
    h1 = subst(w, '(/)')
    h2 = subst(w, 'y')
    h3 = subst(w, YZ)
    h4 = subst(w, 'Q')
    # base case
    A0 = '( M e. NN /\\ (/) C_ Prime /\\ A. n e. (/) -. n || M )'
    s0 = mkst(w, A0)
    mnn0 = s0([], 'simp1', 'M e. NN')
    p0 = s0([w.s([], 'prod0', '%s = 1' % PR('(/)'))], 'a1i', '%s = 1' % PR('(/)'))
    h0 = rteq(s0, p0, PR('(/)'), '1')
    r10 = s0([s0([mnn0], 'nnzd', 'M e. ZZ'), w.inst('rc1')], 'syl', '( # ` %s ) = 1' % RT('1'))
    lhs0 = s0([h0, r10], 'eqtrd', '%s = 1' % CNT('(/)'))
    hz0 = s0([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( # ` (/) ) = 0')
    e20 = s0([s0([], '2cnd', '2 e. CC'), w.inst('exp0')], 'syl', '( 2 ^ 0 ) = 1')
    rhs0 = s0([s0([hz0], 'oveq2d', '( 2 ^ ( # ` (/) ) ) = ( 2 ^ 0 )'), e20], 'eqtrd',
              '( 2 ^ ( # ` (/) ) ) = 1')
    base = w.s([lhs0, s0([rhs0], 'eqcomd', '1 = ( 2 ^ ( # ` (/) ) )')], 'eqtrd', PROP('(/)'))
    # inductive step
    BS = ('( ( y e. Fin /\\ -. z e. y ) /\\ '
          '( M e. NN /\\ %s C_ Prime /\\ A. n e. %s -. n || M ) )' % (YZ, YZ))
    st = mkst(w, BS)
    yfin = st([], 'simpll', 'y e. Fin')
    nzy = st([], 'simplr', '-. z e. y')
    mnn = st([], 'simpr1', 'M e. NN')
    unss = st([], 'simpr2', '%s C_ Prime' % YZ)
    ralu = st([], 'simpr3', 'A. n e. %s -. n || M' % YZ)
    ysub = st([w.s([], 'ssun1', 'y C_ %s' % YZ)], 'a1i', 'y C_ %s' % YZ)
    yprm = st([ysub, unss], 'sstrd', 'y C_ Prime')
    raly2 = st([st([ysub, w.inst('ssralv')], 'syl',
                   '( A. n e. %s -. n || M -> A. n e. y -. n || M )' % YZ), ralu], 'mpd',
               'A. n e. y -. n || M')
    zun = st([st([w.s([], 'ssun2', '{ z } C_ %s' % YZ)], 'a1i', '{ z } C_ %s' % YZ),
              st([w.s([], 'snid', 'z e. { z }')], 'a1i', 'z e. { z }')], 'sseldd',
             'z e. %s' % YZ)
    zprm = st([unss, zun], 'sseldd', 'z e. Prime')
    sbz = w.s([w.s([], 'breq1', '( n = z -> ( n || M <-> z || M ) )')], 'notbid',
              '( n = z -> ( -. n || M <-> -. z || M ) )')
    nzm = st([sbz, ralu, zun], 'rspcdva', '-. z || M')
    stepi = st([st([st([yfin, yprm, raly2], '3jca',
                       '( y e. Fin /\\ y C_ Prime /\\ A. n e. y -. n || M )'),
                    st([mnn, zprm, nzm], '3jca',
                       '( M e. NN /\\ z e. Prime /\\ -. z || M )'), nzy], '3jca',
                   '( ( y e. Fin /\\ y C_ Prime /\\ A. n e. y -. n || M ) /\\ '
                   '( M e. NN /\\ z e. Prime /\\ -. z || M ) /\\ -. z e. y )'),
                w.inst('rcpstep')], 'syl',
               '( %s = ( 2 ^ ( # ` y ) ) -> %s = ( 2 ^ ( # ` %s ) ) )'
               % (CNT('y'), CNT(YZ), YZ))
    AI2 = '( %s /\\ %s )' % (BS, PROP('y'))
    si = mkst(w, AI2)
    ihyp = si([], 'simpr', PROP('y'))
    ihc = si([ihyp, si([lift(w, mnn, AI2), lift(w, yprm, AI2), lift(w, raly2, AI2)], '3jca',
                       '( M e. NN /\\ y C_ Prime /\\ A. n e. y -. n || M )')], 'mpd',
             '%s = ( 2 ^ ( # ` y ) )' % CNT('y'))
    fin1 = si([lift(w, stepi, AI2), ihc], 'mpd', '%s = ( 2 ^ ( # ` %s ) )' % (CNT(YZ), YZ))
    ex0 = w.s([fin1], 'exp31',
              '( ( y e. Fin /\\ -. z e. y ) -> '
              '( ( M e. NN /\\ %s C_ Prime /\\ A. n e. %s -. n || M ) -> ( %s -> %s = ( 2 ^ ( # ` %s ) ) ) ) )'
              % (YZ, YZ, PROP('y'), CNT(YZ), YZ))
    h6 = w.s([ex0], 'com23',
             '( ( y e. Fin /\\ -. z e. y ) -> ( %s -> %s ) )' % (PROP('y'), PROP(YZ)))
    fin = w.s([h1, h2, h3, h4, base, h6], 'findcard2s', '( Q e. Fin -> %s )' % PROP('Q'))
    w.qed([fin], 'imp',
          '( ( Q e. Fin /\\ ( M e. NN /\\ Q C_ Prime /\\ A. n e. Q -. n || M ) ) -> '
          '%s = ( 2 ^ ( # ` Q ) ) )' % CNT('Q'))
    return w


ALL = {'rcpstep': rcpstep, 'rcprod': rcprod}



# ---------------------------------------------------------------- rcdvds
QD = '{ q e. Prime | q || D }'
AD = ('( M e. NN /\\ ( D e. NN /\\ ( mmu ` D ) =/= 0 ) /\\ '
      'A. r e. Prime ( r || D -> -. r || M ) )')


def rcdvds():
    w = WS('rcdvds', 'The number of roots of X ( M X + 1 ) modulo a squarefree D none of '
                     'whose prime divisors divides M is 2 raised to the number of those primes.')
    st = mkst(w, AD)
    mnn = st([], 'simp1', 'M e. NN')
    dpair = st([], 'simp2', '( D e. NN /\\ ( mmu ` D ) =/= 0 )')
    dnn = st([dpair], 'simpld', 'D e. NN')
    hyp = st([], 'simp3', 'A. r e. Prime ( r || D -> -. r || M )')
    qfin = st([dnn, w.inst('pffinq')], 'syl', '%s e. Fin' % QD)
    qprm = st([w.s([], 'ssrab2', '%s C_ Prime' % QD)], 'a1i', '%s C_ Prime' % QD)
    AN = '( %s /\\ n e. %s )' % (AD, QD)
    sn = mkst(w, AN)
    sbq = w.s([w.s([], 'breq1', '( q = n -> ( q || D <-> n || D ) )')], 'elrab',
              '( n e. %s <-> ( n e. Prime /\\ n || D ) )' % QD)
    nmem = sn([sn([sbq], 'a1i', '( n e. %s <-> ( n e. Prime /\\ n || D ) )' % QD),
               sn([], 'simpr', 'n e. %s' % QD)], 'mpbid', '( n e. Prime /\\ n || D )')
    nprm = sn([nmem], 'simpld', 'n e. Prime')
    ndvd = sn([nmem], 'simprd', 'n || D')
    sbr = w.s([w.s([w.s([], 'breq1', '( r = n -> ( r || D <-> n || D ) )'),
                    w.s([w.s([], 'breq1', '( r = n -> ( r || M <-> n || M ) )')], 'notbid',
                        '( r = n -> ( -. r || M <-> -. n || M ) )')], 'imbi12d',
                   '( r = n -> ( ( r || D -> -. r || M ) <-> ( n || D -> -. n || M ) ) )')],
              'id', '( r = n -> ( ( r || D -> -. r || M ) <-> ( n || D -> -. n || M ) ) )')
    w.lines.pop()
    sbr = w.lines[-1].split(':')[0]
    nimp = sn([sbr, lift(w, hyp, AN), nprm], 'rspcdva', '( n || D -> -. n || M )')
    nnm = sn([nimp, ndvd], 'mpd', '-. n || M')
    ral = st([nnm], 'ralrimiva', 'A. n e. %s -. n || M' % QD)
    rcp = st([st([qfin, st([mnn, qprm, ral], '3jca',
                           '( M e. NN /\\ %s C_ Prime /\\ A. n e. %s -. n || M )' % (QD, QD))],
                 'jca',
                 '( %s e. Fin /\\ ( M e. NN /\\ %s C_ Prime /\\ A. n e. %s -. n || M ) )'
                 % (QD, QD, QD)), w.inst('rcprod')], 'syl',
             '%s = ( 2 ^ ( # ` %s ) )' % (CNT(QD), QD))
    pid = st([dpair, w.inst('sqfprodid')], 'syl', '%s = D' % PR(QD))
    hq = rteq(st, pid, PR(QD), 'D')
    w.qed([st([hq], 'eqcomd', '( # ` %s ) = %s' % (RT('D'), CNT(QD))), rcp], 'eqtrd',
          '( %s -> ( # ` %s ) = ( 2 ^ ( # ` %s ) ) )' % (AD, RT('D'), QD))
    return w


ALL['rcdvds'] = rcdvds

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
