"""Sortie C6 section A: the Taylor expansion with vanishing lower coefficients
and the quotient identities (holtayz, holqval, holqval2, holrmq)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *

ZER = 'A. i e. ( 0 ..^ N ) ( C ` i ) = 0'
A0 = '( ( %s /\\ N e. NN0 ) /\\ %s )' % (BASE, ZER)


def SUM(s):
    return 'sum_ k e. ( 0 ..^ %s ) ( H ` k )' % s


def ctx0(w):
    """the standard steps under A0 (section A): returns dict"""
    d = {}
    d['bn'] = bn = w.s([], 'simpl', '( %s -> ( %s /\\ N e. NN0 ) )' % (A0, BASE))
    d['bs'] = bs = w.s([bn, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, BASE))
    d['hn'] = w.s([bn, w.inst('simpr')], 'syl', '( %s -> N e. NN0 )' % A0)
    d['zer'] = w.s([], 'simpr', '( %s -> %s )' % (A0, ZER))
    d.update(basectx(w, A0, bs))
    return d


def zn_steps(w, ante, d, K, kn):
    """steps ( ante -> ( ( Z - P ) ^ K ) e. CC ), ( ante -> ( ( Z - P ) ^ K ) =/= 0 )"""
    zk = w.s([d['zp'], kn], 'expcld', '( %s -> ( ( Z - P ) ^ %s ) e. CC )' % (ante, K))
    zkn = w.s([d['zp'], d['zpne'], w.s([kn], 'nn0zd', '( %s -> %s e. ZZ )' % (ante, K)), w.inst('expne0i')], 'syl3anc',
              '( %s -> ( ( Z - P ) ^ %s ) =/= 0 )' % (ante, K))
    return zk, zkn


if __name__ == '__main__':
    # ---- holtayz ---------------------------------------------------------------
    w = W('holtayz', 'The Taylor expansion when the first N coefficients vanish: 2 pi i times the value at Z is the remainder of order N.')
    hyp(w, '1', 'holtayz.g', GDEF)
    hyp(w, '2', 'holtayz.h', HDEF)
    hyp(w, '3', 'holtayz.c', CDEF)
    d = ctx0(w)
    tay0 = w.s(['1', '2'], 'rectinttay', '( ( %s /\\ N e. NN0 ) -> %s = ( %s + ( G ` N ) ) )' % (BASE, LHS, SUM('N')))
    tay = w.s([d['bn'], tay0], 'syl', '( %s -> %s = ( %s + ( G ` N ) ) )' % (A0, LHS, SUM('N')))
    cb = w.s([w.s([w.s([], 'fveq2', '( i = k -> ( C ` i ) = ( C ` k ) )')], 'eqeq1d', '( i = k -> ( ( C ` i ) = 0 <-> ( C ` k ) = 0 ) )')], 'cbvralvw',
             '( %s <-> A. k e. ( 0 ..^ N ) ( C ` k ) = 0 )' % ZER)
    zerk = w.s([d['zer'], cb], 'sylib', '( %s -> A. k e. ( 0 ..^ N ) ( C ` k ) = 0 )' % A0)
    AK = '( %s /\\ k e. ( 0 ..^ N ) )' % A0
    kfz = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ N ) )' % AK)
    knn = w.s([closed(w, AK, 'fzo0ssnn0', '( 0 ..^ N ) C_ NN0'), kfz], 'sseldd', '( %s -> k e. NN0 )' % AK)
    ck0 = w.s([ad(w, zerk, AK, 'A. k e. ( 0 ..^ N ) ( C ` k ) = 0'), kfz, w.inst('rspa')], 'syl2anc', '( %s -> ( C ` k ) = 0 )' % AK)
    hv0 = w.s(['2', '3'], 'holcfval', '( k e. NN0 -> ( H ` k ) = ( ( ( Z - P ) ^ k ) x. ( C ` k ) ) )')
    hv = w.s([knn, hv0], 'syl', '( %s -> ( H ` k ) = ( ( ( Z - P ) ^ k ) x. ( C ` k ) ) )' % AK)
    zk = w.s([ad(w, d['zp'], AK, '( Z - P ) e. CC'), knn], 'expcld', '( %s -> ( ( Z - P ) ^ k ) e. CC )' % AK)
    hk0 = w.s([hv, w.s([w.s([ck0], 'oveq2d', '( %s -> ( ( ( Z - P ) ^ k ) x. ( C ` k ) ) = ( ( ( Z - P ) ^ k ) x. 0 ) )' % AK), w.s([zk], 'mul01d', '( %s -> ( ( ( Z - P ) ^ k ) x. 0 ) = 0 )' % AK)],
                        'eqtrd', '( %s -> ( ( ( Z - P ) ^ k ) x. ( C ` k ) ) = 0 )' % AK)], 'eqtrd', '( %s -> ( H ` k ) = 0 )' % AK)
    sz = w.s([w.s([hk0], 'sumeq2dv', '( %s -> %s = sum_ k e. ( 0 ..^ N ) 0 )' % (A0, SUM('N'))),
              w.s([w.s([closed(w, A0, 'fzofi', '( 0 ..^ N ) e. Fin')], 'olcd', '( %s -> ( ( 0 ..^ N ) C_ ( ZZ>= ` 0 ) \\/ ( 0 ..^ N ) e. Fin ) )' % A0), w.inst('sumz')], 'syl',
                  '( %s -> sum_ k e. ( 0 ..^ N ) 0 = 0 )' % A0)], 'eqtrd', '( %s -> %s = 0 )' % (A0, SUM('N')))
    gn = gcl(w, A0, 'N', d['hn'], d['bs'], '1')
    w.qed([tay, w.s([w.s([sz], 'oveq1d', '( %s -> ( %s + ( G ` N ) ) = ( 0 + ( G ` N ) ) )' % (A0, SUM('N'))), w.s([gn], 'addlidd', '( %s -> ( 0 + ( G ` N ) ) = ( G ` N ) )' % A0)], 'eqtrd',
                     '( %s -> ( %s + ( G ` N ) ) = ( G ` N ) )' % (A0, SUM('N')))], 'eqtrd', '( %s -> %s = ( G ` N ) )' % (A0, LHS))
    run1(w, h=True)

    # ---- holqval ---------------------------------------------------------------
    ZN = '( ( Z - P ) ^ N )'
    w = W('holqval', 'The quotient of 2 pi i times the value at Z by ( Z - P ) ^ N, when the first N Taylor coefficients vanish: the N-th coefficient plus the remainder of order N + 1 over ( Z - P ) ^ N.')
    hyp(w, '1', 'holqval.g', GDEF)
    hyp(w, '2', 'holqval.h', HDEF)
    hyp(w, '3', 'holqval.c', CDEF)
    d = ctx0(w)
    tz0 = w.s(['1', '2', '3'], 'holtayz', '( %s -> %s = ( G ` N ) )' % (A0, LHS))
    rm = w.s([d['bs'], d['hn'], w.inst('rectintrm')], 'syl2anc', '( %s -> %s = ( %s + %s ) )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'), HT('N'), RINT(RM(E2, '( N + 1 )'), 'A', 'B')))
    hn1 = w.s([d['hn'], w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
    gvn = gval(w, A0, 'N', d['hn'], '1'); gvn1 = gval(w, A0, '( N + 1 )', hn1, '1'); cvn = cval(w, A0, 'N', d['hn'], '3')
    CN = '( C ` N )'; G1 = '( G ` ( N + 1 ) )'
    geq = w.s([w.s([gvn, rm], 'eqtrd', '( %s -> ( G ` N ) = ( %s + %s ) )' % (A0, HT('N'), RINT(RM(E2, '( N + 1 )'), 'A', 'B'))),
               w.s([w.s([cvn], 'oveq2d', '( %s -> ( %s x. %s ) = %s )' % (A0, ZN, CN, HT('N'))), gvn1], 'oveq12d',
                   '( %s -> ( ( %s x. %s ) + %s ) = ( %s + %s ) )' % (A0, ZN, CN, G1, HT('N'), RINT(RM(E2, '( N + 1 )'), 'A', 'B')))], 'eqtr4d',
              '( %s -> ( G ` N ) = ( ( %s x. %s ) + %s ) )' % (A0, ZN, CN, G1))
    lhs = w.s([tz0, geq], 'eqtrd', '( %s -> %s = ( ( %s x. %s ) + %s ) )' % (A0, LHS, ZN, CN, G1))
    zk, zkn = zn_steps(w, A0, d, 'N', d['hn'])
    cn = ccl(w, A0, 'N', d['hn'], d['abih'], '3')
    g1 = gcl(w, A0, '( N + 1 )', hn1, d['bs'], '1')
    zc_ = w.s([zk, cn], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A0, ZN, CN))
    dd = w.s([zc_, g1, zk, zkn], 'divdird', '( %s -> ( ( ( %s x. %s ) + %s ) / %s ) = ( ( ( %s x. %s ) / %s ) + ( %s / %s ) ) )' % (A0, ZN, CN, G1, ZN, ZN, CN, ZN, G1, ZN))
    dc = w.s([cn, zk, zkn], 'divcan3d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (A0, ZN, CN, ZN, CN))
    w.qed([w.s([lhs], 'oveq1d', '( %s -> ( %s / %s ) = ( ( ( %s x. %s ) + %s ) / %s ) )' % (A0, LHS, ZN, ZN, CN, G1, ZN)),
           w.s([dd, w.s([dc], 'oveq1d', '( %s -> ( ( ( %s x. %s ) / %s ) + ( %s / %s ) ) = ( %s + ( %s / %s ) ) )' % (A0, ZN, CN, ZN, G1, ZN, CN, G1, ZN))], 'eqtrd',
               '( %s -> ( ( ( %s x. %s ) + %s ) / %s ) = ( %s + ( %s / %s ) ) )' % (A0, ZN, CN, G1, ZN, CN, G1, ZN))], 'eqtrd',
          '( %s -> ( %s / %s ) = ( %s + ( %s / %s ) ) )' % (A0, LHS, ZN, CN, G1, ZN))
    run1(w, h=True)

    # ---- holqval2 --------------------------------------------------------------
    Z1 = '( ( Z - P ) ^ ( N + 1 ) )'
    C1 = '( C ` ( N + 1 ) )'; G2 = '( G ` ( N + 2 ) )'; G11 = '( G ` ( ( N + 1 ) + 1 ) )'
    QD = '( ( ( %s / %s ) - %s ) / ( Z - P ) )' % (LHS, ZN, CN)
    w = W('holqval2', 'The difference quotient of the normalised quotient at Z, when the first N Taylor coefficients vanish: the ( N + 1 )-th coefficient plus the remainder of order N + 2 over ( Z - P ) ^ ( N + 1 ).')
    hyp(w, '1', 'holqval2.g', GDEF)
    hyp(w, '2', 'holqval2.h', HDEF)
    hyp(w, '3', 'holqval2.c', CDEF)
    d = ctx0(w)
    qv = w.s(['1', '2', '3'], 'holqval', '( %s -> ( %s / %s ) = ( %s + ( %s / %s ) ) )' % (A0, LHS, ZN, CN, G1, ZN))
    hn1 = w.s([d['hn'], w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
    hn2 = w.s([hn1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( N + 1 ) + 1 ) e. NN0 )' % A0)
    zk, zkn = zn_steps(w, A0, d, 'N', d['hn'])
    z1, z1n = zn_steps(w, A0, d, '( N + 1 )', hn1)
    cn = ccl(w, A0, 'N', d['hn'], d['abih'], '3')
    c1 = ccl(w, A0, '( N + 1 )', hn1, d['abih'], '3')
    g1 = gcl(w, A0, '( N + 1 )', hn1, d['bs'], '1')
    g11 = gcl(w, A0, '( ( N + 1 ) + 1 )', hn2, d['bs'], '1')
    q1 = w.s([cn, w.s([g1, zk, zkn], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, G1, ZN))], 'pncan2d', '( %s -> ( ( %s + ( %s / %s ) ) - %s ) = ( %s / %s ) )' % (A0, CN, G1, ZN, CN, G1, ZN))
    num = w.s([w.s([qv], 'oveq1d', '( %s -> ( ( %s / %s ) - %s ) = ( ( %s + ( %s / %s ) ) - %s ) )' % (A0, LHS, ZN, CN, CN, G1, ZN, CN)), q1], 'eqtrd',
              '( %s -> ( ( %s / %s ) - %s ) = ( %s / %s ) )' % (A0, LHS, ZN, CN, G1, ZN))
    dd1 = w.s([g1, zk, d['zp'], zkn, d['zpne']], 'divdiv1d', '( %s -> ( ( %s / %s ) / ( Z - P ) ) = ( %s / ( %s x. ( Z - P ) ) ) )' % (A0, G1, ZN, G1, ZN))
    ep = w.s([d['zp'], d['hn']], 'expp1d', '( %s -> %s = ( %s x. ( Z - P ) ) )' % (A0, Z1, ZN))
    q2 = w.s([w.s([num], 'oveq1d', '( %s -> %s = ( ( %s / %s ) / ( Z - P ) ) )' % (A0, QD, G1, ZN)),
              w.s([dd1, w.s([w.s([ep], 'eqcomd', '( %s -> ( %s x. ( Z - P ) ) = %s )' % (A0, ZN, Z1))], 'oveq2d', '( %s -> ( %s / ( %s x. ( Z - P ) ) ) = ( %s / %s ) )' % (A0, G1, ZN, G1, Z1))], 'eqtrd',
                  '( %s -> ( ( %s / %s ) / ( Z - P ) ) = ( %s / %s ) )' % (A0, G1, ZN, G1, Z1))], 'eqtrd', '( %s -> %s = ( %s / %s ) )' % (A0, QD, G1, Z1))
    # G ` ( N + 1 ) = Z1 x. C1 + G ` ( N + 2 )
    rm = w.s([d['bs'], hn1, w.inst('rectintrm')], 'syl2anc', '( %s -> %s = ( %s + %s ) )' % (A0, RINT(RM(E2, '( N + 1 )'), 'A', 'B'), HT('( N + 1 )'), RINT(RM(E2, '( ( N + 1 ) + 1 )'), 'A', 'B')))
    gvn1 = gval(w, A0, '( N + 1 )', hn1, '1'); gvn2 = gval(w, A0, '( ( N + 1 ) + 1 )', hn2, '1'); cvn1 = cval(w, A0, '( N + 1 )', hn1, '3')
    geq = w.s([w.s([gvn1, rm], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (A0, G1, HT('( N + 1 )'), RINT(RM(E2, '( ( N + 1 ) + 1 )'), 'A', 'B'))),
               w.s([w.s([cvn1], 'oveq2d', '( %s -> ( %s x. %s ) = %s )' % (A0, Z1, C1, HT('( N + 1 )'))), gvn2], 'oveq12d',
                   '( %s -> ( ( %s x. %s ) + %s ) = ( %s + %s ) )' % (A0, Z1, C1, G11, HT('( N + 1 )'), RINT(RM(E2, '( ( N + 1 ) + 1 )'), 'A', 'B')))], 'eqtr4d',
              '( %s -> %s = ( ( %s x. %s ) + %s ) )' % (A0, G1, Z1, C1, G11))
    a12 = w.s([w.s([w.s([d['hn']], 'nn0cnd', '( %s -> N e. CC )' % A0), w.inst('add1p1')], 'syl', '( %s -> ( ( N + 1 ) + 1 ) = ( N + 2 ) )' % A0)], 'fveq2d', '( %s -> %s = %s )' % (A0, G11, G2))
    geq2 = w.s([geq, w.s([a12], 'oveq2d', '( %s -> ( ( %s x. %s ) + %s ) = ( ( %s x. %s ) + %s ) )' % (A0, Z1, C1, G11, Z1, C1, G2))], 'eqtrd', '( %s -> %s = ( ( %s x. %s ) + %s ) )' % (A0, G1, Z1, C1, G2))
    g2 = w.s([a12, g11], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, G2))
    zc1 = w.s([z1, c1], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A0, Z1, C1))
    dd = w.s([zc1, g2, z1, z1n], 'divdird', '( %s -> ( ( ( %s x. %s ) + %s ) / %s ) = ( ( ( %s x. %s ) / %s ) + ( %s / %s ) ) )' % (A0, Z1, C1, G2, Z1, Z1, C1, Z1, G2, Z1))
    dc = w.s([c1, z1, z1n], 'divcan3d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (A0, Z1, C1, Z1, C1))
    w.qed([q2, w.s([w.s([geq2], 'oveq1d', '( %s -> ( %s / %s ) = ( ( ( %s x. %s ) + %s ) / %s ) )' % (A0, G1, Z1, Z1, C1, G2, Z1)),
                    w.s([dd, w.s([dc], 'oveq1d', '( %s -> ( ( ( %s x. %s ) / %s ) + ( %s / %s ) ) = ( %s + ( %s / %s ) ) )' % (A0, Z1, C1, Z1, G2, Z1, C1, G2, Z1))], 'eqtrd',
                        '( %s -> ( ( ( %s x. %s ) + %s ) / %s ) = ( %s + ( %s / %s ) ) )' % (A0, Z1, C1, G2, Z1, C1, G2, Z1))], 'eqtrd',
                   '( %s -> ( %s / %s ) = ( %s + ( %s / %s ) ) )' % (A0, G1, Z1, C1, G2, Z1))], 'eqtrd',
          '( %s -> %s = ( %s + ( %s / %s ) ) )' % (A0, QD, C1, G2, Z1))
    run1(w, h=True)

    # ---- holrmq: the remainder over the power, bounded by the distance ---------
    AR0 = '( ( %s /\\ N e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) )' % (BASE, RBDP, ALF)
    AR1 = '( ( %s /\\ ( N + 1 ) e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) )' % (BASE, RBDP, ALF)
    AZ = '( abs ` ( Z - P ) )'; R1 = '( R ^ ( N + 1 ) )'
    w = W('holrmq', 'The Taylor remainder of order N + 1 divided by ( Z - P ) ^ N is bounded by a constant times the distance from Z to the centre.')
    hyp(w, '1', 'holrmq.g', GDEF)
    A0 = AR0
    bn = w.s([], 'simp1', '( %s -> ( %s /\\ N e. NN0 ) )' % (A0, BASE))
    bs = w.s([bn, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, BASE))
    hn = w.s([bn, w.inst('simpr')], 'syl', '( %s -> N e. NN0 )' % A0)
    rz = w.s([], 'simp2', '( %s -> ( ( %s /\\ 0 < R ) /\\ %s <_ ( R / 2 ) ) )' % (A0, RBDP, AZ))
    mm = w.s([], 'simp3', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
    d = basectx(w, A0, bs)
    hn1 = w.s([hn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
    a1 = w.s([w.s([bs, hn1], 'jca', '( %s -> ( %s /\\ ( N + 1 ) e. NN0 ) )' % (A0, BASE)), rz, mm], '3jca', '( %s -> %s )' % (A0, AR1))
    rmb0 = w.s([], 'holrmb', '( %s -> ( abs ` %s ) <_ ( %s x. ( ( %s / R ) ^ ( N + 1 ) ) ) )' % (AR1, RINT(RM(E2, '( N + 1 )'), 'A', 'B'), KK, AZ))
    rmb = w.s([a1, rmb0], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. ( ( %s / R ) ^ ( N + 1 ) ) ) )' % (A0, RINT(RM(E2, '( N + 1 )'), 'A', 'B'), KK, AZ))
    gv1 = gval(w, A0, '( N + 1 )', hn1, '1')
    G1 = '( G ` ( N + 1 ) )'
    rmb1 = w.s([w.s([gv1], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, G1, RINT(RM(E2, '( N + 1 )'), 'A', 'B'))), rmb], 'eqbrtrd',
               '( %s -> ( abs ` %s ) <_ ( %s x. ( ( %s / R ) ^ ( N + 1 ) ) ) )' % (A0, G1, KK, AZ))
    # reals and positivity
    rbd = w.s([w.s([rz, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP)), w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP))
    rpos = w.s([w.s([rz, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP)), w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
    rr = w.s([rbd, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
    Rrp = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
    mr = w.s([mm, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
    perr = w.s([w.s([w.s([d['bc']], 'recld', '( %s -> %s e. RR )' % (A0, RB)), w.s([d['ac']], 'recld', '( %s -> %s e. RR )' % (A0, RA))], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)),
                w.s([w.s([d['bc']], 'imcld', '( %s -> %s e. RR )' % (A0, IB)), w.s([d['ac']], 'imcld', '( %s -> %s e. RR )' % (A0, IA))], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld',
               '( %s -> %s e. RR )' % (A0, PER))
    kr = w.s([w.s([closed(w, A0, '2re', '2 e. RR'), w.s([mr, w.s([Rrp], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % A0)], 'rerpdivcld', '( %s -> ( M / ( R / 2 ) ) e. RR )' % A0)], 'remulcld',
                   '( %s -> ( 2 x. ( M / ( R / 2 ) ) ) e. RR )' % A0), perr], 'remulcld', '( %s -> %s e. RR )' % (A0, KK))
    kc = w.s([kr], 'recnd', '( %s -> %s e. CC )' % (A0, KK))
    az = w.s([d['zp']], 'abscld', '( %s -> %s e. RR )' % (A0, AZ))
    azc = w.s([az], 'recnd', '( %s -> %s e. CC )' % (A0, AZ))
    azpos = w.s([w.s([d['zp'], w.inst('absgt0')], 'syl', '( %s -> ( ( Z - P ) =/= 0 <-> 0 < %s ) )' % (A0, AZ)), d['zpne']], 'mpbid' if False else 'mpbid', '( %s -> 0 < %s )' % (A0, AZ)) if False else \
        w.s([d['zpne'], w.s([d['zp'], w.inst('absgt0')], 'syl', '( %s -> ( ( Z - P ) =/= 0 <-> 0 < %s ) )' % (A0, AZ))], 'mpbid', '( %s -> 0 < %s )' % (A0, AZ))
    azrp = w.s([az, azpos], 'elrpd', '( %s -> %s e. RR+ )' % (A0, AZ))
    nz = w.s([hn], 'nn0zd', '( %s -> N e. ZZ )' % A0)
    anrp = w.s([azrp, nz], 'rpexpcld', '( %s -> ( %s ^ N ) e. RR+ )' % (A0, AZ))
    anr = w.s([anrp], 'rpred', '( %s -> ( %s ^ N ) e. RR )' % (A0, AZ))
    anc = w.s([anr], 'recnd', '( %s -> ( %s ^ N ) e. CC )' % (A0, AZ))
    r1rp = w.s([Rrp, w.s([hn1], 'nn0zd', '( %s -> ( N + 1 ) e. ZZ )' % A0)], 'rpexpcld', '( %s -> %s e. RR+ )' % (A0, R1))
    r1c = w.s([w.s([r1rp], 'rpred', '( %s -> %s e. RR )' % (A0, R1))], 'recnd', '( %s -> %s e. CC )' % (A0, R1))
    r1ne = w.s([r1rp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, R1))
    rc = w.s([rr], 'recnd', '( %s -> R e. CC )' % A0)
    rne = w.s([Rrp], 'rpne0d', '( %s -> R =/= 0 )' % A0)
    kq = w.s([kc, r1c, r1ne], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, KK, R1))
    kqr = w.s([kr, r1rp], 'rerpdivcld', '( %s -> ( %s / %s ) e. RR )' % (A0, KK, R1))
    Y = '( ( %s / %s ) x. %s )' % (KK, R1, AZ)
    yr = w.s([kqr, az], 'remulcld', '( %s -> %s e. RR )' % (A0, Y))
    # a^N x. Y = K x. ( ( a / R ) ^ ( N + 1 ) )
    W_ = '( ( %s ^ N ) x. %s )' % (AZ, AZ)
    e1 = w.s([anc, kq, azc], 'mul12d', '( %s -> ( ( %s ^ N ) x. %s ) = ( ( %s / %s ) x. %s ) )' % (A0, AZ, Y, KK, R1, W_))
    wc = w.s([anc, azc], 'mulcld', '( %s -> %s e. CC )' % (A0, W_))
    e2 = w.s([w.s([kc, wc, r1c, r1ne], 'div23d', '( %s -> ( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s ) )' % (A0, KK, W_, R1, KK, R1, W_))], 'eqcomd',
             '( %s -> ( ( %s / %s ) x. %s ) = ( ( %s x. %s ) / %s ) )' % (A0, KK, R1, W_, KK, W_, R1))
    e3 = w.s([kc, wc, r1c, r1ne], 'divassd', '( %s -> ( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) ) )' % (A0, KK, W_, R1, KK, W_, R1))
    ep = w.s([w.s([azc, hn], 'expp1d', '( %s -> ( %s ^ ( N + 1 ) ) = %s )' % (A0, AZ, W_))], 'eqcomd', '( %s -> %s = ( %s ^ ( N + 1 ) ) )' % (A0, W_, AZ))
    ed = w.s([w.s([azc, rc, rne, hn1], 'expdivd', '( %s -> ( ( %s / R ) ^ ( N + 1 ) ) = ( ( %s ^ ( N + 1 ) ) / %s ) )' % (A0, AZ, AZ, R1))], 'eqcomd',
             '( %s -> ( ( %s ^ ( N + 1 ) ) / %s ) = ( ( %s / R ) ^ ( N + 1 ) ) )' % (A0, AZ, R1, AZ))
    e4 = w.s([w.s([ep], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s ^ ( N + 1 ) ) / %s ) )' % (A0, W_, R1, AZ, R1)), ed], 'eqtrd', '( %s -> ( %s / %s ) = ( ( %s / R ) ^ ( N + 1 ) ) )' % (A0, W_, R1, AZ))
    chain = w.s([w.s([w.s([e1, e2], 'eqtrd', '( %s -> ( ( %s ^ N ) x. %s ) = ( ( %s x. %s ) / %s ) )' % (A0, AZ, Y, KK, W_, R1)), e3], 'eqtrd',
                      '( %s -> ( ( %s ^ N ) x. %s ) = ( %s x. ( %s / %s ) ) )' % (A0, AZ, Y, KK, W_, R1)),
                 w.s([e4], 'oveq2d', '( %s -> ( %s x. ( %s / %s ) ) = ( %s x. ( ( %s / R ) ^ ( N + 1 ) ) ) )' % (A0, KK, W_, R1, KK, AZ))], 'eqtrd',
                '( %s -> ( ( %s ^ N ) x. %s ) = ( %s x. ( ( %s / R ) ^ ( N + 1 ) ) ) )' % (A0, AZ, Y, KK, AZ))
    g1c = gcl(w, A0, '( N + 1 )', hn1, bs, '1')
    ag1 = w.s([g1c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, G1))
    le1 = w.s([rmb1, w.s([chain], 'eqcomd', '( %s -> ( %s x. ( ( %s / R ) ^ ( N + 1 ) ) ) = ( ( %s ^ N ) x. %s ) )' % (A0, KK, AZ, AZ, Y))], 'breqtrd',
              '( %s -> ( abs ` %s ) <_ ( ( %s ^ N ) x. %s ) )' % (A0, G1, AZ, Y))
    ldm = w.s([ag1, yr, w.s([anr, w.s([anrp], 'rpgt0d', '( %s -> 0 < ( %s ^ N ) )' % (A0, AZ))], 'jca', '( %s -> ( ( %s ^ N ) e. RR /\\ 0 < ( %s ^ N ) ) )' % (A0, AZ, AZ)), w.inst('ledivmul')], 'syl3anc',
              '( %s -> ( ( ( abs ` %s ) / ( %s ^ N ) ) <_ %s <-> ( abs ` %s ) <_ ( ( %s ^ N ) x. %s ) ) )' % (A0, G1, AZ, Y, G1, AZ, Y))
    le2 = w.s([le1, ldm], 'mpbird', '( %s -> ( ( abs ` %s ) / ( %s ^ N ) ) <_ %s )' % (A0, G1, AZ, Y))
    zk, zkn = zn_steps(w, A0, d, 'N', hn)
    absq = w.s([g1c, zk, zkn], 'absdivd', '( %s -> ( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) ) )' % (A0, G1, ZN, G1, ZN))
    absp = w.s([d['zp'], hn, w.inst('absexp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( %s ^ N ) )' % (A0, ZN, AZ))
    w.qed([w.s([absq, w.s([absp], 'oveq2d', '( %s -> ( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / ( %s ^ N ) ) )' % (A0, G1, ZN, G1, AZ))], 'eqtrd',
                '( %s -> ( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( %s ^ N ) ) )' % (A0, G1, ZN, G1, AZ)), le2], 'eqbrtrd',
          '( %s -> ( abs ` ( %s / %s ) ) <_ %s )' % (A0, G1, ZN, Y))
    run1(w, h=True)
