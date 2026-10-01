"""Sortie ZBV: the zeta series and BVL2's tsum_rpow_multiples.

zetacvg1   ( ( S e. RR /\\ 1 < S ) -> seq 1 ( + , ( t e. NN |-> ( t ^c -u S ) ) ) e. dom ~~> )
zetacvgm   ( ( ( S e. RR /\\ 1 < S ) /\\ C e. CC ) -> seq 1 ( + , ( t e. NN |-> ( C x. ( t ^c -u S ) ) ) ) e. dom ~~> )
zetasumcl  ( ( S e. RR /\\ 1 < S ) -> sum_ n e. NN ( n ^c -u S ) e. RR )
bvmult     ( ( ( S e. RR /\\ 1 < S ) /\\ M e. NN ) ->
             sum_ n e. NN if ( M || n , ( n ^c -u S ) , 0 ) = ( ( M ^c -u S ) x. sum_ n e. NN ( n ^c -u S ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbvlib import *


HS = '( S e. RR /\\ 1 < S )'
F0 = '( t e. NN |-> ( t ^c -u S ) )'
SEQ = lambda F: 'seq 1 ( + , %s )' % F


def sfacts(w, ante, sre, s1):
    """S e. CC, -u S e. CC, -u S e. RR under ante from sre: S e. RR, s1: 1 < S"""
    st = mkst(w, ante)
    scc = st([sre], 'recnd', 'S e. CC')
    nsr = st([sre], 'renegcld', '-u S e. RR')
    nsc = st([nsr], 'recnd', '-u S e. CC')
    return scc, nsr, nsc


def zetacvg1():
    w = W('zetacvg1', 'The zeta series at a real exponent above one converges (zetacvg for the '
                      'mapping written out).')
    st = mkst(w, HS)
    sre = st([], 'simpl', 'S e. RR'); s1 = st([], 'simpr', '1 < S')
    scc, nsr, nsc = sfacts(w, HS, sre, s1)
    res = st([sre], 'rered' if False else 'a1i', '( S e. RR -> ( Re ` S ) = S )') if False else None
    re1 = st([sre, w.inst('rere')], 'syl', '( Re ` S ) = S')
    lt = st([s1, re1], 'breqtrrd', '1 < ( Re ` S )')
    AK = '( %s /\\ k e. NN )' % HS
    sk = mkst(w, AK)
    val, _ = mpv(w, AK, 't', 'NN', '( t ^c -u S )', 'k', sk([], 'simpr', 'k e. NN'))
    w.qed([scc, lt, val], 'zetacvg', '( %s -> %s e. dom ~~> )' % (HS, SEQ(F0)))
    return w


def zetacvgm():
    w = W('zetacvgm', 'A constant multiple of the zeta series converges.')
    A = '( %s /\\ C e. CC )' % HS
    st = mkst(w, A)
    hs = st([], 'simpl', HS); ccc = st([], 'simpr', 'C e. CC')
    sre = st([hs], 'simpld', 'S e. RR'); s1 = st([hs], 'simprd', '1 < S')
    scc, nsr, nsc = sfacts(w, A, sre, s1)
    H = '( t e. NN |-> ( C x. ( t ^c -u S ) ) )'
    cv = st([hs, w.inst('zetacvg1')], 'syl', '%s e. dom ~~>' % SEQ(F0))
    L = '( ~~> ` %s )' % SEQ(F0)
    lim = st([cv, st([w.s([], 'climdm', '( %s e. dom ~~> <-> %s ~~> %s )' % (SEQ(F0), SEQ(F0), L))],
                     'a1i', '( %s e. dom ~~> <-> %s ~~> %s )' % (SEQ(F0), SEQ(F0), L))], 'mpbid',
             '%s ~~> %s' % (SEQ(F0), L))
    AK = '( %s /\\ k e. NN )' % A
    sk = mkst(w, AK)
    knn = sk([], 'simpr', 'k e. NN')
    v0, _ = mpv(w, AK, 't', 'NN', '( t ^c -u S )', 'k', knn)
    kcc = sk([sk([knn], 'nncnd', 'k e. CC'), lift(w, nsc, AK)], 'cxpcld', '( k ^c -u S ) e. CC')
    f0c = sk([v0, kcc], 'eqeltrd', '( %s ` k ) e. CC' % F0)
    vh, _ = mpv(w, AK, 't', 'NN', '( C x. ( t ^c -u S ) )', 'k', knn)
    hv = sk([vh, sk([v0], 'oveq2d', '( C x. ( %s ` k ) ) = ( C x. ( k ^c -u S ) )' % F0)], 'eqtr4d',
            '( %s ` k ) = ( C x. ( %s ` k ) )' % (H, F0))
    z = clo(w, 'nnuz', NNUZ)
    one = st([], '1zzd', '1 e. ZZ')
    ml = st([z, one, ccc, lim, f0c, hv], 'isermulc2', '%s ~~> ( C x. %s )' % (SEQ(H), L))
    w.qed([st([w.s([], 'climrel', 'Rel ~~>')], 'a1i', 'Rel ~~>'), ml, w.inst('releldm')], 'syl2anc',
          '( %s -> %s e. dom ~~> )' % (A, SEQ(H)))
    return w


def zetasumcl():
    w = W('zetasumcl', 'The zeta series at a real exponent above one sums to a real number.')
    st = mkst(w, HS)
    sre = st([], 'simpl', 'S e. RR'); s1 = st([], 'simpr', '1 < S')
    scc, nsr, nsc = sfacts(w, HS, sre, s1)
    AK = '( %s /\\ n e. NN )' % HS
    sk = mkst(w, AK)
    knn = sk([], 'simpr', 'n e. NN')
    v0, _ = mpv(w, AK, 't', 'NN', '( t ^c -u S )', 'n', knn)
    kre = sk([sk([knn], 'nnrpd', 'n e. RR+'), lift(w, nsr, AK)], 'rpcxpcld', '( n ^c -u S ) e. RR+')
    kre = sk([kre], 'rpred', '( n ^c -u S ) e. RR')
    z = clo(w, 'nnuz', NNUZ)
    one = st([], '1zzd', '1 e. ZZ')
    cv = st([], 'zetacvg1', '%s e. dom ~~>' % SEQ(F0))
    w.qed([z, one, v0, kre, cv], 'isumrecl', '( %s -> sum_ n e. NN ( n ^c -u S ) e. RR )' % HS)
    return w


def bvmult():
    w = W('bvmult', 'The zeta series restricted to the multiples of M is M ^c -u S times the '
                    'zeta series (Lean tsum_rpow_multiples): the reindexing n = M k through '
                    'isumcoll.')
    PH = '( %s /\\ M e. NN )' % HS
    st = mkst(w, PH)
    hs = st([], 'simpl', HS); mnn = st([], 'simpr', 'M e. NN')
    sre = st([hs], 'simpld', 'S e. RR'); s1 = st([hs], 'simprd', '1 < S')
    scc, nsr, nsc = sfacts(w, PH, sre, s1)
    MS = '( M ^c -u S )'
    IF = lambda v: 'if ( M || %s , ( %s ^c -u S ) , 0 )' % (v, v)
    F = '( t e. NN |-> %s )' % IF('t')
    G = '( t e. NN |-> ( M x. t ) )'
    H = '( t e. NN |-> ( %s x. ( t ^c -u S ) ) )' % MS
    msrp = st([st([mnn], 'nnrpd', 'M e. RR+'), nsr], 'rpcxpcld', '%s e. RR+' % MS)
    mscc = st([msrp], 'rpcnd', '%s e. CC' % MS)
    # .g
    AT = '( %s /\\ t e. NN )' % PH
    stt = mkst(w, AT)
    hg = st([stt([lift(w, mnn, AT), stt([], 'simpr', 't e. NN')], 'nnmulcld', '( M x. t ) e. NN')],
            'fmpttd', '%s : NN --> NN' % G)
    # .i
    AK = '( %s /\\ k e. NN )' % PH
    sk = mkst(w, AK)
    knn = sk([], 'simpr', 'k e. NN')
    k1nn = sk([knn], 'peano2nnd', '( k + 1 ) e. NN')
    gk, _ = mpv(w, AK, 't', 'NN', '( M x. t )', 'k', knn)
    gk1, _ = mpv(w, AK, 't', 'NN', '( M x. t )', '( k + 1 )', k1nn)
    kre = sk([knn], 'nnred', 'k e. RR')
    lt = sk([kre, sk([k1nn], 'nnred', '( k + 1 ) e. RR'), sk([lift(w, mnn, AK)], 'nnrpd', 'M e. RR+'),
             sk([kre], 'ltp1d', 'k < ( k + 1 )')], 'ltmul2dd', '( M x. k ) < ( M x. ( k + 1 ) )')
    hi = sk([gk, gk1, lt], '3brtr4d', '( %s ` k ) < ( %s ` ( k + 1 ) )' % (G, G))
    # .0
    AN = '( %s /\\ n e. ( NN \\ ran %s ) )' % (PH, G)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. ( NN \\ ran %s )' % G)
    nnn = sn([nel], 'eldifad', 'n e. NN')
    nrn = sn([nel], 'eldifbd', '-. n e. ran %s' % G)
    AD = '( %s /\\ M || n )' % AN
    sd = mkst(w, AD)
    dv = sd([], 'simpr', 'M || n')
    qnn = sd([dv, sd([lift(w, nnn, AD), lift(w, mnn, AD), w.inst('nndivdvds')], 'syl2anc',
                     '( M || n <-> ( n / M ) e. NN )')], 'mpbid', '( n / M ) e. NN')
    gq, _ = mpv(w, AD, 't', 'NN', '( M x. t )', '( n / M )', qnn)
    canc = sd([sd([lift(w, nnn, AD)], 'nncnd', 'n e. CC'), sd([lift(w, mnn, AD)], 'nncnd', 'M e. CC'),
               sd([lift(w, mnn, AD)], 'nnne0d', 'M =/= 0')], 'divcan2d', '( M x. ( n / M ) ) = n')
    gqn = sd([gq, canc], 'eqtrd', '( %s ` ( n / M ) ) = n' % G)
    gfn = sd([lift(w, hg, AD)], 'ffnd', '%s Fn NN' % G)
    inr = sd([gfn, qnn, w.inst('fnfvelrn')], 'syl2anc', '( %s ` ( n / M ) ) e. ran %s' % (G, G))
    ninr = sd([gqn, inr], 'eqeltrrd', 'n e. ran %s' % G)
    ndv = sn([nrn, ninr], 'mtand', '-. M || n')
    fn, _ = mpv(w, AN, 't', 'NN', IF('t'), 'n', nnn)
    h0 = sn([fn, sn([ndv], 'iffalsed', '%s = 0' % IF('n'))], 'eqtrd', '( %s ` n ) = 0' % F)
    # .f
    AN2 = '( %s /\\ n e. NN )' % PH
    sn2 = mkst(w, AN2)
    nnn2 = sn2([], 'simpr', 'n e. NN')
    fn2, _ = mpv(w, AN2, 't', 'NN', IF('t'), 'n', nnn2)
    ncx = sn2([sn2([nnn2], 'nncnd', 'n e. CC'), lift(w, nsc, AN2)], 'cxpcld', '( n ^c -u S ) e. CC')
    ifc = sn2([ncx, sn2([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF('n'))
    hf = sn2([fn2, ifc], 'eqeltrd', '( %s ` n ) e. CC' % F)
    # .h
    hk, _ = mpv(w, AK, 't', 'NN', '( %s x. ( t ^c -u S ) )' % MS, 'k', knn)
    mk = sk([lift(w, mnn, AK), knn], 'nnmulcld', '( M x. k ) e. NN')
    fmk, _ = mpv(w, AK, 't', 'NN', IF('t'), '( M x. k )', mk)
    dvm = sk([sk([lift(w, mnn, AK)], 'nnzd', 'M e. ZZ'), sk([knn], 'nnzd', 'k e. ZZ'), w.inst('dvdsmul1')],
             'syl2anc', 'M || ( M x. k )')
    ift = sk([dvm], 'iftrued', '%s = ( ( M x. k ) ^c -u S )' % IF('( M x. k )'))
    mre = sk([lift(w, mnn, AK)], 'nnred', 'M e. RR')
    mge = sk([sk([lift(w, mnn, AK)], 'nnrpd', 'M e. RR+')], 'rpge0d', '0 <_ M')
    kge = sk([sk([knn], 'nnrpd', 'k e. RR+')], 'rpge0d', '0 <_ k')
    mcx = sk([mre, mge, kre, kge, lift(w, nsc, AK)], 'mulcxpd',
             '( ( M x. k ) ^c -u S ) = ( %s x. ( k ^c -u S ) )' % MS)
    fgk = sk([gk], 'fveq2d', '( %s ` ( %s ` k ) ) = ( %s ` ( M x. k ) )' % (F, G, F))
    ch = sk([sk([fgk, fmk], 'eqtrd', '( %s ` ( %s ` k ) ) = %s' % (F, G, IF('( M x. k )'))),
             sk([ift, mcx], 'eqtrd', '%s = ( %s x. ( k ^c -u S ) )' % (IF('( M x. k )'), MS))], 'eqtrd',
            '( %s ` ( %s ` k ) ) = ( %s x. ( k ^c -u S ) )' % (F, G, MS))
    hh = sk([hk, ch], 'eqtr4d', '( %s ` k ) = ( %s ` ( %s ` k ) )' % (H, F, G))
    # .c
    hc = st([hs, mscc, w.inst('zetacvgm')], 'syl2anc', '%s e. dom ~~>' % SEQ(H))
    # isumcoll
    SUMF = 'sum_ n e. NN ( %s ` n )' % F
    SUMH = 'sum_ j e. NN ( %s ` j )' % H
    ic = st([hg, hi, h0, hf, hh, hc], 'isumcoll', '%s = %s' % (SUMF, SUMH))
    # LHS rewrite
    lhs = st([fn2], 'sumeq2dv', '%s = sum_ n e. NN %s' % (SUMF, IF('n')))
    # RHS rewrite
    AJ = '( %s /\\ j e. NN )' % PH
    sj = mkst(w, AJ)
    jnn = sj([], 'simpr', 'j e. NN')
    hj, _ = mpv(w, AJ, 't', 'NN', '( %s x. ( t ^c -u S ) )' % MS, 'j', jnn)
    rhs = st([hj], 'sumeq2dv', '%s = sum_ j e. NN ( %s x. ( j ^c -u S ) )' % (SUMH, MS))
    f0j, _ = mpv(w, AJ, 't', 'NN', '( t ^c -u S )', 'j', jnn)
    jcx = sj([sj([jnn], 'nncnd', 'j e. CC'), lift(w, nsc, AJ)], 'cxpcld', '( j ^c -u S ) e. CC')
    z = clo(w, 'nnuz', NNUZ)
    one = st([], '1zzd', '1 e. ZZ')
    cv0 = st([hs, w.inst('zetacvg1')], 'syl', '%s e. dom ~~>' % SEQ(F0))
    mc = st([z, one, f0j, jcx, cv0, mscc], 'isummulc2',
            '( %s x. sum_ j e. NN ( j ^c -u S ) ) = sum_ j e. NN ( %s x. ( j ^c -u S ) )' % (MS, MS))
    cb = w.s([w.s([], 'oveq1', '( j = n -> ( j ^c -u S ) = ( n ^c -u S ) )')], 'cbvsumv',
             'sum_ j e. NN ( j ^c -u S ) = sum_ n e. NN ( n ^c -u S )')
    cb2 = st([st([cb], 'a1i', 'sum_ j e. NN ( j ^c -u S ) = sum_ n e. NN ( n ^c -u S )')], 'oveq2d',
             '( %s x. sum_ j e. NN ( j ^c -u S ) ) = ( %s x. sum_ n e. NN ( n ^c -u S ) )' % (MS, MS))
    rhs2 = st([st([rhs, mc], 'eqtr4d', '%s = ( %s x. sum_ j e. NN ( j ^c -u S ) )' % (SUMH, MS)), cb2],
              'eqtrd', '%s = ( %s x. sum_ n e. NN ( n ^c -u S ) )' % (SUMH, MS))
    w.qed([st([lhs, ic], 'eqtr3d', 'sum_ n e. NN %s = %s' % (IF('n'), SUMH)), rhs2], 'eqtrd',
          '( %s -> sum_ n e. NN %s = ( %s x. sum_ n e. NN ( n ^c -u S ) ) )' % (PH, IF('n'), MS))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['zetacvg1', 'zetacvgm', 'zetasumcl', 'bvmult']:
        globals()[f]().run()
