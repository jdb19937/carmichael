"""Sortie C8, section 2: the logarithm LAM is holomorphic (hlogh) and exp LAM = F (hlogexp)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
from congr import mptval

CCPR = 'CC e. { RR , CC }'
CZ = '( CC \\ { 0 } )'


def unit(w, ante, jn0, jltn, nn, j='j', N='N'):
    """from j e. NN0, j < N, N e. NN: ( j / N ) and ( ( j + 1 ) / N ) in ( 0 [,] 1 )"""
    jr = w.s([jn0], 'nn0red', '( %s -> %s e. RR )' % (ante, j))
    j0 = w.s([jn0], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ante, j))
    nrp = w.s([nn], 'nnrpd', '( %s -> %s e. RR+ )' % (ante, N))
    nr = w.s([nn], 'nnred', '( %s -> %s e. RR )' % (ante, N))
    T0 = '( %s / %s )' % (j, N); T1 = '( ( %s + 1 ) / %s )' % (j, N)
    t0r = w.s([jr, nrp], 'rerpdivcld', '( %s -> %s e. RR )' % (ante, T0))
    t00 = w.s([jr, nrp, j0], 'divge0d', '( %s -> 0 <_ %s )' % (ante, T0))
    t01 = w.s([w.s([jr, nr, jltn], 'ltled', '( %s -> %s <_ %s )' % (ante, j, N)), w.s([jr, nrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> %s <_ %s ) )' % (ante, T0, j, N))],
              'mpbird', '( %s -> %s <_ 1 )' % (ante, T0))
    t0in = w.s([w.s([t0r, t00, t01], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (ante, T0, T0, T0)),
                w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (T0, T0, T0, T0))], 'sylibr', '( %s -> %s e. ( 0 [,] 1 ) )' % (ante, T0))
    one = w.s([], '1red', '( %s -> 1 e. RR )' % ante)
    j1r = w.s([jr, one], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (ante, j))
    j10 = w.s([jr, one, j0, w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % ante)], 'addge0d', '( %s -> 0 <_ ( %s + 1 ) )' % (ante, j))
    t1r = w.s([j1r, nrp], 'rerpdivcld', '( %s -> %s e. RR )' % (ante, T1))
    t10 = w.s([j1r, nrp, j10], 'divge0d', '( %s -> 0 <_ %s )' % (ante, T1))
    j1le = w.s([jltn, w.s([w.s([jn0], 'nn0zd', '( %s -> %s e. ZZ )' % (ante, j)), w.s([nn], 'nnzd', '( %s -> %s e. ZZ )' % (ante, N)), w.inst('zltp1le')], 'syl2anc',
                          '( %s -> ( %s < %s <-> ( %s + 1 ) <_ %s ) )' % (ante, j, N, j, N))], 'mpbid', '( %s -> ( %s + 1 ) <_ %s )' % (ante, j, N))
    t11 = w.s([j1le, w.s([j1r, nrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> ( %s + 1 ) <_ %s ) )' % (ante, T1, j, N))], 'mpbird', '( %s -> %s <_ 1 )' % (ante, T1))
    t1in = w.s([w.s([t1r, t10, t11], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (ante, T1, T1, T1)),
                w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (T1, T1, T1, T1))], 'sylibr', '( %s -> %s e. ( 0 [,] 1 ) )' % (ante, T1))
    return t0in, t1in, t0r, t1r


def ptfacts(w, ante, c, Z, kfzo, zinK, k='k', N='N'):
    """at a point Z of K and an index k e. ( 0 ..^ N ): the two affine points in K and D,
    F there in CC, nonzero at the second, the quotient in the slit plane.  c: dict of
    context steps ab, geo, kd, ff, nz (NZ0), slp (SLITP(N))"""
    jfz = w.s([kfzo, w.s([], 'elfzo0', '( %s e. ( 0 ..^ %s ) <-> ( %s e. NN0 /\\ %s e. NN /\\ %s < %s ) )' % (k, N, k, N, k, N))], 'sylib',
              '( %s -> ( %s e. NN0 /\\ %s e. NN /\\ %s < %s ) )' % (ante, k, N, k, N))
    kn0 = w.s([jfz, w.inst('simp1')], 'syl', '( %s -> %s e. NN0 )' % (ante, k))
    nn = w.s([jfz, w.inst('simp2')], 'syl', '( %s -> %s e. NN )' % (ante, N))
    kltn = w.s([jfz, w.inst('simp3')], 'syl', '( %s -> %s < %s )' % (ante, k, N))
    t0in, t1in, t0r, t1r = unit(w, ante, kn0, kltn, nn, k, N)
    U = KP1(k, N); T = KN(k, N)
    abgeo = w.s([c['ab'], c['geo']], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, AB, GEO))
    pu = w.s([abgeo, w.s([zinK, t1in], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( 0 [,] 1 ) ) )' % (ante, Z, U)), w.inst('crectaff')], 'syl2anc',
             '( %s -> %s e. ( A crect B ) )' % (ante, AFF(U, Z)))
    pt = w.s([abgeo, w.s([zinK, t0in], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( 0 [,] 1 ) ) )' % (ante, Z, T)), w.inst('crectaff')], 'syl2anc',
             '( %s -> %s e. ( A crect B ) )' % (ante, AFF(T, Z)))
    pud = w.s([c['kd'], pu], 'sseldd', '( %s -> %s e. D )' % (ante, AFF(U, Z)))
    ptd = w.s([c['kd'], pt], 'sseldd', '( %s -> %s e. D )' % (ante, AFF(T, Z)))
    fu = w.s([c['ff'], pud], 'ffvelcdmd', '( %s -> %s e. CC )' % (ante, FA(U, Z)))
    ft = w.s([c['ff'], ptd], 'ffvelcdmd', '( %s -> %s e. CC )' % (ante, FA(T, Z)))
    idy = w.s([], 'id', '( y = %s -> y = %s )' % (AFF(T, Z), AFF(T, Z)))
    cgy, _ = w.wcongr('( F ` y ) =/= 0', {'y': AFF(T, Z)}, 'y = %s' % AFF(T, Z), {'y': idy})
    ftn = w.s([cgy, c['nz'], pt], 'rspcdva', '( %s -> %s =/= 0 )' % (ante, FA(T, Z)))
    BODY = '%s e. %s' % (QT(KP1('j', N), KN('j', N), 'p'), SLIT)
    idp = w.s([], 'id', '( p = %s -> p = %s )' % (Z, Z))
    cgp, b1 = w.wcongr(BODY, {'p': Z}, 'p = %s' % Z, {'p': idp})
    idj = w.s([], 'id', '( j = %s -> j = %s )' % (k, k))
    cgj, b2 = w.wcongr(b1, {'j': k}, 'j = %s' % k, {'j': idj})
    assert b2 == '%s e. %s' % (QT(U, T, Z), SLIT), b2
    sl = w.s([w.s([zinK, kfzo], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( 0 ..^ %s ) ) )' % (ante, Z, k, N)), c['slp'],
              w.s([cgp, cgj], 'rspc2va', '( ( ( %s e. ( A crect B ) /\\ %s e. ( 0 ..^ %s ) ) /\\ %s ) -> %s )' % (Z, k, N, SLITP(N), b2))], 'syl2anc',
             '( %s -> %s )' % (ante, b2))
    return dict(pud=pud, ptd=ptd, fu=fu, ft=ft, ftn=ftn, sl=sl, nn=nn, t0r=t0r, t1r=t1r)


def gen_hlogh():
    w = W('hlogh', 'The grid logarithm ` LAM ` is holomorphic on every open subset of the rectangle.')
    H1 = '( %s /\\ %s )' % (ABG, NZ0)
    H2 = '( N e. NN /\\ %s )' % SLITP('N')
    H3 = '( %s /\\ ( A crect B ) C_ D )' % EOPN
    A0 = '( %s /\\ %s /\\ %s )' % (H1, H2, H3)
    h1 = w.s([], 'simp1', '( %s -> %s )' % (A0, H1)); h2 = w.s([], 'simp2', '( %s -> %s )' % (A0, H2)); h3 = w.s([], 'simp3', '( %s -> %s )' % (A0, H3))
    abg = w.s([h1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ABG))
    nz = w.s([h1, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, NZ0))
    hol = w.s([abg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    abgg = w.s([abg, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
    ab = w.s([abgg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
    geo = w.s([abgg, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, GEO))
    nn = w.s([h2, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    slp = w.s([h2, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, SLITP('N')))
    eop = w.s([h3, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, EOPN))
    kd = w.s([h3, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    eto = w.s([eop, w.inst('simpl')], 'syl', '( %s -> E e. %s )' % (A0, TOP))
    ek = w.s([eop, w.inst('simpr')], 'syl', '( %s -> E C_ ( A crect B ) )' % A0)
    fcn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    ecc = w.s([w.s([eto, w.inst('elssuni')], 'syl', '( %s -> E C_ U. %s )' % (A0, TOP)), w.s([], 'unicntop', 'CC = U. %s' % TOP)], 'sseqtrrdi', '( %s -> E C_ CC )' % A0)
    cc = w.s([w.s([], 'cnelprrecn', CCPR)], 'a1i', '( %s -> %s )' % (A0, CCPR))
    # F ( A ) and its logarithm
    ain = w.s([abgg, w.inst('crectcnr1')], 'syl', '( %s -> A e. ( A crect B ) )' % A0)
    fac = w.s([ff, w.s([kd, ain], 'sseldd', '( %s -> A e. D )' % A0)], 'ffvelcdmd', '( %s -> ( F ` A ) e. CC )' % A0)
    fa0 = w.s([w.s([w.s([], 'fveq2', '( y = A -> ( F ` y ) = ( F ` A ) )')], 'neeq1d', '( y = A -> ( ( F ` y ) =/= 0 <-> ( F ` A ) =/= 0 ) )'), nz, ain], 'rspcdva',
              '( %s -> ( F ` A ) =/= 0 )' % A0)
    LFA = '( log ` ( F ` A ) )'
    lfa = w.s([fac, fa0], 'logcld', '( %s -> %s e. CC )' % (A0, LFA))

    def ctx(ante):
        return {k: w.s([v], 'adantr', '( %s -> %s )' % (ante, f)) for k, (v, f) in
                {'ab': (ab, AB), 'geo': (geo, GEO), 'kd': (kd, '( A crect B ) C_ D'), 'ff': (ff, 'F : D --> CC'), 'nz': (nz, NZ0), 'slp': (slp, SLITP('N'))}.items()}
    # ---- per index k: the derivative of the term is a function on E
    PK = '( %s /\\ k e. ( 0 ..^ N ) )' % A0
    kin = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ N ) )' % PK)
    U = KP1('k', 'N'); T = KN('k', 'N')
    PKV = '( %s /\\ v e. E )' % PK
    vin = w.s([], 'simpr', '( %s -> v e. E )' % PKV)
    cv = {k_: w.s([v_], 'adantr', '( %s -> %s )' % (PKV, f)) for k_, (v_, f) in
          {'ab': (w.s([ab], 'adantr', '( %s -> %s )' % (PK, AB)), AB), 'geo': (w.s([geo], 'adantr', '( %s -> %s )' % (PK, GEO)), GEO),
           'kd': (w.s([kd], 'adantr', '( %s -> ( A crect B ) C_ D )' % PK), '( A crect B ) C_ D'), 'ff': (w.s([ff], 'adantr', '( %s -> F : D --> CC )' % PK), 'F : D --> CC'),
           'nz': (w.s([nz], 'adantr', '( %s -> %s )' % (PK, NZ0)), NZ0), 'slp': (w.s([slp], 'adantr', '( %s -> %s )' % (PK, SLITP('N'))), SLITP('N'))}.items()}
    vk = w.s([w.s([w.s([ek], 'adantr', '( %s -> E C_ ( A crect B ) )' % PK)], 'adantr', '( %s -> E C_ ( A crect B ) )' % PKV), vin], 'sseldd', '( %s -> v e. ( A crect B ) )' % PKV)
    pf = ptfacts(w, PKV, cv, 'v', w.s([kin], 'adantr', '( %s -> k e. ( 0 ..^ N ) )' % PKV), vk)
    BODYV = '( ( %s e. D /\\ %s e. D ) /\\ ( %s =/= 0 /\\ %s e. %s ) )' % (AFF(U, 'v'), AFF(T, 'v'), FA(T, 'v'), QT(U, T, 'v'), SLIT)
    bv = w.s([w.s([pf['pud'], pf['ptd']], 'jca', '( %s -> ( %s e. D /\\ %s e. D ) )' % (PKV, AFF(U, 'v'), AFF(T, 'v'))),
              w.s([pf['ftn'], pf['sl']], 'jca', '( %s -> ( %s =/= 0 /\\ %s e. %s ) )' % (PKV, FA(T, 'v'), QT(U, T, 'v'), SLIT))], 'jca', '( %s -> %s )' % (PKV, BODYV))
    allv = w.s([bv], 'ralrimiva', '( %s -> A. v e. E %s )' % (PK, BODYV))
    nnk = w.s([nn], 'adantr', '( %s -> N e. NN )' % PK)
    kn0 = w.s([w.s([kin, w.s([], 'elfzo0', '( k e. ( 0 ..^ N ) <-> ( k e. NN0 /\\ N e. NN /\\ k < N ) )')], 'sylib', '( %s -> ( k e. NN0 /\\ N e. NN /\\ k < N ) )' % PK), w.inst('simp1')],
              'syl', '( %s -> k e. NN0 )' % PK)
    nc = w.s([nnk], 'nncnd', '( %s -> N e. CC )' % PK)
    nne = w.s([nnk], 'nnne0d', '( %s -> N =/= 0 )' % PK)
    kc = w.s([kn0], 'nn0cnd', '( %s -> k e. CC )' % PK)
    uc = w.s([w.s([kc, w.s([], '1cnd', '( %s -> 1 e. CC )' % PK)], 'addcld', '( %s -> ( k + 1 ) e. CC )' % PK), nc, nne], 'divcld', '( %s -> %s e. CC )' % (PK, U))
    tcc = w.s([kc, nc, nne], 'divcld', '( %s -> %s e. CC )' % (PK, T))
    TERMW = '( log ` %s )' % QT(U, T, 'w')
    tdv = w.s([w.s([hol], 'adantr', '( %s -> %s )' % (PK, HOL)),
               w.s([w.s([eto], 'adantr', '( %s -> E e. %s )' % (PK, TOP)), w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % PK), w.s([uc, tcc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (PK, U, T))],
                                                                                'jca', '( %s -> ( A e. CC /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (PK, U, T))], 'jca',
                   '( %s -> ( E e. %s /\\ ( A e. CC /\\ ( %s e. CC /\\ %s e. CC ) ) ) )' % (PK, TOP, U, T)),
               allv, w.inst('hlogtdv')], 'syl3anc', '( %s -> ( CC _D ( w e. E |-> %s ) ) : E --> CC )' % (PK, TERMW))
    G = '( CC _D ( w e. E |-> %s ) )' % TERMW
    BX = '( %s ` x )' % G
    TERMX = TERM('k', 'N', 'x')
    # the derivative equation in x
    cbv = w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( x = w -> ( x - A ) = ( w - A ) )')], 'oveq2d', '( x = w -> ( %s x. ( x - A ) ) = ( %s x. ( w - A ) ) )' % (U, U))], 'oveq2d',
                          '( x = w -> %s = %s )' % (AFF(U, 'x'), AFF(U, 'w')))], 'fveq2d', '( x = w -> %s = %s )' % (FA(U, 'x'), FA(U, 'w'))),
                w.s([w.s([w.s([w.s([], 'oveq1', '( x = w -> ( x - A ) = ( w - A ) )')], 'oveq2d', '( x = w -> ( %s x. ( x - A ) ) = ( %s x. ( w - A ) ) )' % (T, T))], 'oveq2d',
                          '( x = w -> %s = %s )' % (AFF(T, 'x'), AFF(T, 'w')))], 'fveq2d', '( x = w -> %s = %s )' % (FA(T, 'x'), FA(T, 'w')))], 'oveq12d',
               '( x = w -> %s = %s )' % (QT(U, T, 'x'), QT(U, T, 'w')))
    cbv2 = w.s([cbv], 'fveq2d', '( x = w -> %s = %s )' % (TERMX, TERMW))
    cbm = w.s([cbv2], 'cbvmptv', '( x e. E |-> %s ) = ( w e. E |-> %s )' % (TERMX, TERMW))
    dx1 = w.s([w.s([cbm], 'oveq2i', '( CC _D ( x e. E |-> %s ) ) = %s' % (TERMX, G))], 'a1i', '( %s -> ( CC _D ( x e. E |-> %s ) ) = %s )' % (PK, TERMX, G))
    dx2 = w.s([tdv], 'feqmptd', '( %s -> %s = ( x e. E |-> %s ) )' % (PK, G, BX))
    dxk = w.s([dx1, dx2], 'eqtrd', '( %s -> ( CC _D ( x e. E |-> %s ) ) = ( x e. E |-> %s ) )' % (PK, TERMX, BX))
    # closures on ( A0 /\ k e. I /\ x e. E )
    P3 = '( %s /\\ k e. ( 0 ..^ N ) /\\ x e. E )' % A0
    a03 = w.s([], 'simp1', '( %s -> %s )' % (P3, A0))
    k3 = w.s([], 'simp2', '( %s -> k e. ( 0 ..^ N ) )' % P3)
    x3 = w.s([], 'simp3', '( %s -> x e. E )' % P3)
    c3 = {k_: w.s([a03, v_], 'syl', '( %s -> %s )' % (P3, f)) for k_, (v_, f) in
          {'ab': (ab, AB), 'geo': (geo, GEO), 'kd': (kd, '( A crect B ) C_ D'), 'ff': (ff, 'F : D --> CC'), 'nz': (nz, NZ0), 'slp': (slp, SLITP('N'))}.items()}
    xk = w.s([w.s([a03, ek], 'syl', '( %s -> E C_ ( A crect B ) )' % P3), x3], 'sseldd', '( %s -> x e. ( A crect B ) )' % P3)
    pf3 = ptfacts(w, P3, c3, 'x', k3, xk)
    q3 = w.s([pf3['fu'], pf3['ft'], pf3['ftn']], 'divcld', '( %s -> %s e. CC )' % (P3, QT(U, T, 'x')))
    q30 = w.s([w.s([w.s([w.s([], 'slitss', '%s C_ %s' % (SLIT, CZ))], 'a1i', '( %s -> %s C_ %s )' % (P3, SLIT, CZ)), pf3['sl']], 'sseldd', '( %s -> %s e. %s )' % (P3, QT(U, T, 'x'), CZ)),
                w.inst('eldifsni')], 'syl', '( %s -> %s =/= 0 )' % (P3, QT(U, T, 'x')))
    tx3 = w.s([q3, q30], 'logcld', '( %s -> %s e. CC )' % (P3, TERMX))
    tdv3 = w.s([w.s([a03, k3], 'jca', '( %s -> ( %s /\\ k e. ( 0 ..^ N ) ) )' % (P3, A0)), tdv], 'syl', '( %s -> %s : E --> CC )' % (P3, G))
    bx3 = w.s([tdv3, x3], 'ffvelcdmd', '( %s -> %s e. CC )' % (P3, BX))
    jeq = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    fz = w.s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % A0)
    SUMT_ = 'sum_ k e. ( 0 ..^ N ) %s' % TERMX
    SUMB = 'sum_ k e. ( 0 ..^ N ) %s' % BX
    dfs = w.s([jeq, keq, cc, eto, fz, tx3, bx3, dxk], 'dvmptfsum', '( %s -> ( CC _D ( x e. E |-> %s ) ) = ( x e. E |-> %s ) )' % (A0, SUMT_, SUMB))
    # the constant
    dc0 = w.s([cc, lfa], 'dvmptc', '( %s -> ( CC _D ( x e. CC |-> %s ) ) = ( x e. CC |-> 0 ) )' % (A0, LFA))
    PX = '( %s /\\ x e. CC )' % A0
    dcr = w.s([cc, w.s([lfa], 'adantr', '( %s -> %s e. CC )' % (PX, LFA)), w.s([], '0cnd', '( %s -> 0 e. CC )' % PX), dc0, ecc, jeq, keq, eto], 'dvmptres',
              '( %s -> ( CC _D ( x e. E |-> %s ) ) = ( x e. E |-> 0 ) )' % (A0, LFA))
    PE = '( %s /\\ x e. E )' % A0
    PEK = '( %s /\\ k e. ( 0 ..^ N ) )' % PE
    # closures of the sums under ( A0 /\ x e. E )
    tk = w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (PEK, A0)), w.s([], 'simpr', '( %s -> k e. ( 0 ..^ N ) )' % PEK), w.s([], 'simplr', '( %s -> x e. E )' % PEK)], '3jca',
                  '( %s -> %s )' % (PEK, P3)), tx3], 'syl', '( %s -> %s e. CC )' % (PEK, TERMX))
    bk = w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (PEK, A0)), w.s([], 'simpr', '( %s -> k e. ( 0 ..^ N ) )' % PEK), w.s([], 'simplr', '( %s -> x e. E )' % PEK)], '3jca',
                  '( %s -> %s )' % (PEK, P3)), bx3], 'syl', '( %s -> %s e. CC )' % (PEK, BX))
    fze = w.s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % PE)
    st = w.s([fze, tk], 'fsumcl', '( %s -> %s e. CC )' % (PE, SUMT_))
    sb = w.s([fze, bk], 'fsumcl', '( %s -> %s e. CC )' % (PE, SUMB))
    lfae = w.s([lfa], 'adantr', '( %s -> %s e. CC )' % (PE, LFA))
    z0 = w.s([], '0cnd', '( %s -> 0 e. CC )' % PE)
    dl = w.s([cc, lfae, z0, dcr, st, sb, dfs], 'dvmptadd', '( %s -> ( CC _D %s ) = ( x e. E |-> ( 0 + %s ) ) )' % (A0, LAM('N'), SUMB))
    cl = w.s([z0, sb], 'addcld', '( %s -> ( 0 + %s ) e. CC )' % (PE, SUMB))
    # domain and continuity
    MAPD = '( x e. E |-> ( 0 + %s ) )' % SUMB
    mfd = w.s([cl], 'fmpttd', '( %s -> %s : E --> CC )' % (A0, MAPD))
    dm = w.s([w.s([dl], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, LAM('N'), MAPD)), w.s([mfd, w.inst('fdm')], 'syl', '( %s -> dom %s = E )' % (A0, MAPD))],
             'eqtrd', '( %s -> dom ( CC _D %s ) = E )' % (A0, LAM('N')))
    lamf = w.s([w.s([lfae, st], 'addcld', '( %s -> %s e. CC )' % (PE, LAMB('N', 'x')))], 'fmpttd', '( %s -> %s : E --> CC )' % (A0, LAM('N')))
    cn = w.s([w.s([w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), lamf, ecc], '3jca', '( %s -> ( CC C_ CC /\\ %s : E --> CC /\\ E C_ CC ) )' % (A0, LAM('N'))),
              dm, w.inst('dvcn')], 'syl2anc', '( %s -> %s e. ( E -cn-> CC ) )' % (A0, LAM('N')))
    w.qed([cn, w.s([w.s([dm], 'eqcomd', '( %s -> E = dom ( CC _D %s ) )' % (A0, LAM('N')))], 'eqimssd', '( %s -> E C_ dom ( CC _D %s ) )' % (A0, LAM('N')))], 'jca',
          '( %s -> %s )' % (A0, HOLE(LAM('N'))))
    return run8(w)


def gen_hlogexp():
    w = W('hlogexp', 'The grid logarithm is a logarithm of ` F ` : ` exp ( LAM ( X ) ) = F ( X ) ` at every point of the rectangle ( ~ eftel ).')
    H1 = '( %s /\\ %s )' % (ABG, NZ0)
    H2 = '( N e. NN /\\ ( A crect B ) C_ D )'
    A0 = '( %s /\\ %s /\\ X e. ( A crect B ) )' % (H1, H2)
    h1 = w.s([], 'simp1', '( %s -> %s )' % (A0, H1)); h2 = w.s([], 'simp2', '( %s -> %s )' % (A0, H2))
    xin = w.s([], 'simp3', '( %s -> X e. ( A crect B ) )' % A0)
    abg = w.s([h1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ABG))
    nz = w.s([h1, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, NZ0))
    hol = w.s([abg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    abgg = w.s([abg, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
    ab = w.s([abgg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
    nn = w.s([h2, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    kd = w.s([h2, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    ff = w.s([w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    xc = w.s([crss, xin], 'sseldd', '( %s -> X e. CC )' % A0)
    nc = w.s([nn], 'nncnd', '( %s -> N e. CC )' % A0)
    nne = w.s([nn], 'nnne0d', '( %s -> N =/= 0 )' % A0)
    nn0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    VB = FA('( t / N )', 'X')
    V = '( t e. ( 0 ... N ) |-> %s )' % VB
    # V maps into CC \ { 0 }
    PT = '( %s /\\ t e. ( 0 ... N ) )' % A0
    tin = w.s([], 'simpr', '( %s -> t e. ( 0 ... N ) )' % PT)
    t3 = w.s([tin, w.s([], 'elfz2nn0', '( t e. ( 0 ... N ) <-> ( t e. NN0 /\\ N e. NN0 /\\ t <_ N ) )')], 'sylib', '( %s -> ( t e. NN0 /\\ N e. NN0 /\\ t <_ N ) )' % PT)
    tn0 = w.s([t3, w.inst('simp1')], 'syl', '( %s -> t e. NN0 )' % PT)
    tle = w.s([t3, w.inst('simp3')], 'syl', '( %s -> t <_ N )' % PT)
    tr = w.s([tn0], 'nn0red', '( %s -> t e. RR )' % PT)
    nrp = w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % PT)], 'nnrpd', '( %s -> N e. RR+ )' % PT)
    Tt = '( t / N )'
    ttr = w.s([tr, nrp], 'rerpdivcld', '( %s -> %s e. RR )' % (PT, Tt))
    tt0 = w.s([tr, nrp, w.s([tn0], 'nn0ge0d', '( %s -> 0 <_ t )' % PT)], 'divge0d', '( %s -> 0 <_ %s )' % (PT, Tt))
    tt1 = w.s([tle, w.s([tr, nrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> t <_ N ) )' % (PT, Tt))], 'mpbird', '( %s -> %s <_ 1 )' % (PT, Tt))
    ttin = w.s([w.s([ttr, tt0, tt1], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (PT, Tt, Tt, Tt)),
                w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (Tt, Tt, Tt, Tt))], 'sylibr', '( %s -> %s e. ( 0 [,] 1 ) )' % (PT, Tt))
    ptk = w.s([w.s([w.s([abgg], 'adantr', '( %s -> ( %s /\\ %s ) )' % (PT, AB, GEO)), w.s([w.s([xin], 'adantr', '( %s -> X e. ( A crect B ) )' % PT), ttin], 'jca',
                                                                                        '( %s -> ( X e. ( A crect B ) /\\ %s e. ( 0 [,] 1 ) ) )' % (PT, Tt))], 'jca',
                   '( %s -> ( ( %s /\\ %s ) /\\ ( X e. ( A crect B ) /\\ %s e. ( 0 [,] 1 ) ) ) )' % (PT, AB, GEO, Tt)), w.inst('crectaff')], 'syl', '( %s -> %s e. ( A crect B ) )' % (PT, AFF(Tt, 'X')))
    fv = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % PT), w.s([w.s([kd], 'adantr', '( %s -> ( A crect B ) C_ D )' % PT), ptk], 'sseldd', '( %s -> %s e. D )' % (PT, AFF(Tt, 'X')))],
             'ffvelcdmd', '( %s -> %s e. CC )' % (PT, VB))
    idy = w.s([], 'id', '( y = %s -> y = %s )' % (AFF(Tt, 'X'), AFF(Tt, 'X')))
    cgy, _ = w.wcongr('( F ` y ) =/= 0', {'y': AFF(Tt, 'X')}, 'y = %s' % AFF(Tt, 'X'), {'y': idy})
    fv0 = w.s([cgy, w.s([nz], 'adantr', '( %s -> %s )' % (PT, NZ0)), ptk], 'rspcdva', '( %s -> %s =/= 0 )' % (PT, VB))
    fvz = w.s([w.s([fv, fv0], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (PT, VB, VB)), w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 0 ) )' % (VB, CZ, VB, VB))],
              'sylibr', '( %s -> %s e. %s )' % (PT, VB, CZ))
    vf = w.s([fvz], 'fmpttd', '( %s -> %s : ( 0 ... N ) --> %s )' % (A0, V, CZ))
    SUMV = 'sum_ k e. ( 0 ..^ N ) ( log ` ( ( %s ` ( k + 1 ) ) / ( %s ` k ) ) )' % (V, V)
    tel = w.s([nn0, vf, w.inst('eftel')], 'syl2anc', '( %s -> ( exp ` %s ) = ( ( %s ` N ) / ( %s ` 0 ) ) )' % (A0, SUMV, V, V))
    # the sum in LAM's form
    PK = '( %s /\\ k e. ( 0 ..^ N ) )' % A0
    kin = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ N ) )' % PK)
    k1 = w.s([kin, w.inst('fzofzp1')], 'syl', '( %s -> ( k + 1 ) e. ( 0 ... N ) )' % PK)
    k0 = w.s([kin, w.inst('elfzofz')], 'syl', '( %s -> k e. ( 0 ... N ) )' % PK)
    MG = StepGen('mv')
    v1, _ = mptval(w, PK, 't', '( 0 ... N )', VB, '( k + 1 )', k1, mp=V, gen=MG)
    v0, _ = mptval(w, PK, 't', '( 0 ... N )', VB, 'k', k0, mp=V, gen=MG)
    tq = w.s([w.s([v1, v0], 'oveq12d', '( %s -> ( ( %s ` ( k + 1 ) ) / ( %s ` k ) ) = %s )' % (PK, V, V, QT(KP1('k', 'N'), KN('k', 'N'), 'X')))], 'fveq2d',
             '( %s -> ( log ` ( ( %s ` ( k + 1 ) ) / ( %s ` k ) ) ) = %s )' % (PK, V, V, TERM('k', 'N', 'X')))
    se = w.s([tq], 'sumeq2dv', '( %s -> %s = %s )' % (A0, SUMV, SUMT('N', 'X')))
    # closure of SUMV
    vf1 = w.s([w.s([vf], 'adantr', '( %s -> %s : ( 0 ... N ) --> %s )' % (PK, V, CZ)), k1], 'ffvelcdmd', '( %s -> ( %s ` ( k + 1 ) ) e. %s )' % (PK, V, CZ))
    vf0 = w.s([w.s([vf], 'adantr', '( %s -> %s : ( 0 ... N ) --> %s )' % (PK, V, CZ)), k0], 'ffvelcdmd', '( %s -> ( %s ` k ) e. %s )' % (PK, V, CZ))
    a1c = w.s([vf1, w.inst('eldifi')], 'syl', '( %s -> ( %s ` ( k + 1 ) ) e. CC )' % (PK, V)); a1n = w.s([vf1, w.inst('eldifsni')], 'syl', '( %s -> ( %s ` ( k + 1 ) ) =/= 0 )' % (PK, V))
    a0c = w.s([vf0, w.inst('eldifi')], 'syl', '( %s -> ( %s ` k ) e. CC )' % (PK, V)); a0n = w.s([vf0, w.inst('eldifsni')], 'syl', '( %s -> ( %s ` k ) =/= 0 )' % (PK, V))
    qv = w.s([a1c, a0c, a0n], 'divcld', '( %s -> ( ( %s ` ( k + 1 ) ) / ( %s ` k ) ) e. CC )' % (PK, V, V))
    qv0 = w.s([a1c, a0c, a1n, a0n], 'divne0d', '( %s -> ( ( %s ` ( k + 1 ) ) / ( %s ` k ) ) =/= 0 )' % (PK, V, V))
    lqv = w.s([qv, qv0], 'logcld', '( %s -> ( log ` ( ( %s ` ( k + 1 ) ) / ( %s ` k ) ) ) e. CC )' % (PK, V, V))
    svc = w.s([w.s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % A0), lqv], 'fsumcl', '( %s -> %s e. CC )' % (A0, SUMV))
    # the end values
    nfz = w.s([nn0, w.inst('nn0fz0')], 'sylib', '( %s -> N e. ( 0 ... N ) )' % A0)
    zfz = w.s([nn0, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... N ) )' % A0)
    vn, vnv = mptval(w, A0, 't', '( 0 ... N )', VB, 'N', nfz, mp=V, gen=MG)
    vz, vzv = mptval(w, A0, 't', '( 0 ... N )', VB, '0', zfz, mp=V, gen=MG)
    XA = '( X - A )'
    xac = w.s([xc, ac], 'subcld', '( %s -> %s e. CC )' % (A0, XA))
    n1 = w.s([w.s([w.s([nc, nne], 'dividd', '( %s -> ( N / N ) = 1 )' % A0)], 'oveq1d', '( %s -> ( ( N / N ) x. %s ) = ( 1 x. %s ) )' % (A0, XA, XA)),
              w.s([xac], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, XA, XA))], 'eqtrd', '( %s -> ( ( N / N ) x. %s ) = %s )' % (A0, XA, XA))
    n2 = w.s([w.s([n1], 'oveq2d', '( %s -> %s = ( A + %s ) )' % (A0, AFF('( N / N )', 'X'), XA)), w.s([ac, xc, w.inst('pncan3')], 'syl2anc', '( %s -> ( A + %s ) = X )' % (A0, XA))],
             'eqtrd', '( %s -> %s = X )' % (A0, AFF('( N / N )', 'X')))
    vnx = w.s([vn, w.s([n2], 'fveq2d', '( %s -> %s = ( F ` X ) )' % (A0, FA('( N / N )', 'X')))], 'eqtrd', '( %s -> ( %s ` N ) = ( F ` X ) )' % (A0, V))
    z1 = w.s([w.s([w.s([nc, nne], 'div0d', '( %s -> ( 0 / N ) = 0 )' % A0)], 'oveq1d', '( %s -> ( ( 0 / N ) x. %s ) = ( 0 x. %s ) )' % (A0, XA, XA)),
              w.s([xac], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (A0, XA))], 'eqtrd', '( %s -> ( ( 0 / N ) x. %s ) = 0 )' % (A0, XA))
    z2 = w.s([w.s([z1], 'oveq2d', '( %s -> %s = ( A + 0 ) )' % (A0, AFF('( 0 / N )', 'X'))), w.s([ac], 'addridd', '( %s -> ( A + 0 ) = A )' % A0)],
             'eqtrd', '( %s -> %s = A )' % (A0, AFF('( 0 / N )', 'X')))
    vza = w.s([vz, w.s([z2], 'fveq2d', '( %s -> %s = ( F ` A ) )' % (A0, FA('( 0 / N )', 'X')))], 'eqtrd', '( %s -> ( %s ` 0 ) = ( F ` A ) )' % (A0, V))
    tel2 = w.s([tel, w.s([vnx, vza], 'oveq12d', '( %s -> ( ( %s ` N ) / ( %s ` 0 ) ) = ( ( F ` X ) / ( F ` A ) ) )' % (A0, V, V))], 'eqtrd',
               '( %s -> ( exp ` %s ) = ( ( F ` X ) / ( F ` A ) ) )' % (A0, SUMV))
    # F ( A )
    ain = w.s([abgg, w.inst('crectcnr1')], 'syl', '( %s -> A e. ( A crect B ) )' % A0)
    fac = w.s([ff, w.s([kd, ain], 'sseldd', '( %s -> A e. D )' % A0)], 'ffvelcdmd', '( %s -> ( F ` A ) e. CC )' % A0)
    fa0 = w.s([w.s([w.s([], 'fveq2', '( y = A -> ( F ` y ) = ( F ` A ) )')], 'neeq1d', '( y = A -> ( ( F ` y ) =/= 0 <-> ( F ` A ) =/= 0 ) )'), nz, ain], 'rspcdva',
              '( %s -> ( F ` A ) =/= 0 )' % A0)
    fxc = w.s([ff, w.s([kd, xin], 'sseldd', '( %s -> X e. D )' % A0)], 'ffvelcdmd', '( %s -> ( F ` X ) e. CC )' % A0)
    LFA = '( log ` ( F ` A ) )'
    lfa = w.s([fac, fa0], 'logcld', '( %s -> %s e. CC )' % (A0, LFA))
    f1 = w.s([w.s([w.s([se], 'eqcomd', '( %s -> %s = %s )' % (A0, SUMT('N', 'X'), SUMV))], 'oveq2d', '( %s -> %s = ( %s + %s ) )' % (A0, LAMB('N', 'X'), LFA, SUMV))], 'fveq2d',
             '( %s -> ( exp ` %s ) = ( exp ` ( %s + %s ) ) )' % (A0, LAMB('N', 'X'), LFA, SUMV))
    f2 = w.s([lfa, svc, w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (A0, LFA, SUMV, LFA, SUMV))
    f3 = w.s([w.s([fac, fa0, w.inst('eflog')], 'syl2anc', '( %s -> ( exp ` %s ) = ( F ` A ) )' % (A0, LFA)), tel2], 'oveq12d',
             '( %s -> ( ( exp ` %s ) x. ( exp ` %s ) ) = ( ( F ` A ) x. ( ( F ` X ) / ( F ` A ) ) ) )' % (A0, LFA, SUMV))
    f4 = w.s([fxc, fac, fa0], 'divcan2d', '( %s -> ( ( F ` A ) x. ( ( F ` X ) / ( F ` A ) ) ) = ( F ` X ) )' % A0)
    w.qed([w.s([w.s([f1, f2], 'eqtrd', '( %s -> ( exp ` %s ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (A0, LAMB('N', 'X'), LFA, SUMV)), f3], 'eqtrd',
                '( %s -> ( exp ` %s ) = ( ( F ` A ) x. ( ( F ` X ) / ( F ` A ) ) ) )' % (A0, LAMB('N', 'X'))), f4], 'eqtrd', '( %s -> ( exp ` %s ) = ( F ` X ) )' % (A0, LAMB('N', 'X')))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_hlogh, gen_hlogexp]:
        g()
