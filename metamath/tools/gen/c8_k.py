"""Sortie C8, section 3: Cauchy's estimate and the maximum modulus principle
with one continuity-only point (rectintce0x, holexpx, rectintmmnx, rectintmmx)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
from c8_freeze import S, EXC, EXO, INTQ, ALF

TPI = '( 2 x. ( _i x. _pi ) )'
RBDQ = RBD('Q', 'R')
AP = '( abs ` ( F ` Q ) )'


def CAU(X, E):
    return '( ( z e. ( ( A crect B ) \\ { %s } ) |-> ( ( F ` z ) / ( z - %s ) ) ) rectint <. A , B >. ) = ( %s x. ( F ` %s ) )' % (E, E, TPI, X)


def gen_rectintce0x():
    w = W('rectintce0x', 'Cauchy estimate of order zero at a strictly interior point ` Q ` for a function continuous on the rectangle and differentiable off one further interior point ` P ` ( ~ z6cau2 , ~ rectintce0g ).')
    A0 = S['rectintce0x'].split(' -> ( ( _pi x. R )')[0][2:]
    C1 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s )' % (AB, INTP, INTQ, EXC)
    C2 = '( %s /\\ 0 < R )' % RBDQ
    C3 = '( M e. RR /\\ %s )' % ALF
    assert A0 == '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
    c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1))
    c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2))
    c3 = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
    ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    pq = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INTP, INTQ))
    ex = w.s([c1, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, EXC))
    ip = w.s([pq, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
    iq = w.s([pq, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
    ne = w.s([pq, w.inst('simp3')], 'syl', '( %s -> P =/= Q )' % A0)
    qp = w.s([ne], 'necomd', '( %s -> Q =/= P )' % A0)
    Z6 = tsub(stmt('z6cau2'), {'P': 'Q', 'Q': 'P'})
    z6a, z6c = ante_of(Z6)
    assert z6c == CAU('Q', 'Q')
    ZA = '( %s /\\ ( %s /\\ %s ) /\\ Q =/= P )' % (AB, INTQ, INTP)
    assert z6a == '( %s /\\ %s )' % (ZA, EXC)
    za = w.s([ab, w.s([iq, ip], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, INTQ, INTP)), qp], '3jca', '( %s -> %s )' % (A0, ZA))
    cau = w.s([za, ex, w.inst('z6cau2')], 'syl2anc', '( %s -> %s )' % (A0, CAU('Q', 'Q')))
    fcn = w.s([ex, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    kd = w.s([ex, w.inst('simp2')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    G = tsub(stmt('rectintce0g'), {'P': 'Q'})
    ga, gc = ante_of(G)
    HC = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D )'
    G1 = '( ( %s /\\ %s /\\ %s ) /\\ %s /\\ %s )' % (AB, INTQ, HC, C2, C3)
    assert ga == '( %s /\\ %s )' % (G1, CAU('Q', 'Q')), ga
    g1 = w.s([w.s([ab, iq, w.s([fcn, kd], 'jca', '( %s -> %s )' % (A0, HC))], '3jca',
                  '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTQ, HC)), c2, c3], '3jca', '( %s -> %s )' % (A0, G1))
    w.qed([g1, cau, w.inst('rectintce0g')], 'syl2anc', '( %s -> %s )' % (A0, gc))
    assert '( %s -> %s )' % (A0, gc) == S['rectintce0x']
    return run8(w)


GN = '( z e. D |-> ( ( F ` z ) ^ N ) )'
PW = '( y e. CC |-> ( y ^ N ) )'
DPW = '( y e. CC |-> ( N x. ( y ^ ( N - 1 ) ) ) )'


def gen_dvexpx():
    w = W('dvexpx', 'A positive integer power of a function is differentiable at every point where the function is ( pointwise chain rule, ~ dvcobr ).')
    A0 = '( ( F : D --> CC /\\ D C_ CC ) /\\ ( N e. NN /\\ X e. dom ( CC _D F ) ) )'
    A1 = '( %s /\\ y e. CC )' % A0
    A2 = '( %s /\\ z e. D )' % A0
    ff = w.s([], 'simpll', '( %s -> F : D --> CC )' % A0)
    dcc = w.s([], 'simplr', '( %s -> D C_ CC )' % A0)
    nn = w.s([], 'simprl', '( %s -> N e. NN )' % A0)
    xd = w.s([], 'simprr', '( %s -> X e. dom ( CC _D F ) )' % A0)
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % A1)
    nn1 = w.s([nn], 'adantr', '( %s -> N e. NN )' % A1)
    yn = w.s([yc, w.s([nn1], 'nnnn0d', '( %s -> N e. NN0 )' % A1)], 'expcld', '( %s -> ( y ^ N ) e. CC )' % A1)
    pwf = w.s([yn, w.s([], 'eqid', '%s = %s' % (PW, PW))], 'fmptd', '( %s -> %s : CC --> CC )' % (A0, PW))
    dex = w.s([nn, w.inst('dvexp')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, PW, DPW))
    rhs = w.s([w.s([nn1], 'nncnd', '( %s -> N e. CC )' % A1), w.s([yc, w.s([nn1, w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % A1)], 'expcld', '( %s -> ( y ^ ( N - 1 ) ) e. CC )' % A1)],
              'mulcld', '( %s -> ( N x. ( y ^ ( N - 1 ) ) ) e. CC )' % A1)
    dm = dvdom(w, A0, PW, 'y', 'CC', '( N x. ( y ^ ( N - 1 ) ) )', dex, rhs)
    dvbs = w.s([ccs, ff, dcc], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
    xdd = w.s([dvbs, xd], 'sseldd', '( %s -> X e. D )' % A0)
    fx = w.s([ff, xdd], 'ffvelcdmd', '( %s -> ( F ` X ) e. CC )' % A0)
    fxd = w.s([dm, fx], 'sseldd', '( %s -> ( F ` X ) e. dom ( CC _D %s ) )' % (A0, PW))
    DP = '( CC _D %s )' % PW
    fun1 = w.s([w.s([w.s([], 'dvfcn', '%s : dom %s --> CC' % (DP, DP))], 'a1i', '( %s -> %s : dom %s --> CC )' % (A0, DP, DP))], 'ffund', '( %s -> Fun %s )' % (A0, DP))
    bf = w.s([fxd, w.s([fun1, w.inst('funfvbrb')], 'syl', '( %s -> ( ( F ` X ) e. dom %s <-> ( F ` X ) %s ( %s ` ( F ` X ) ) ) )' % (A0, DP, DP, DP))], 'mpbid',
             '( %s -> ( F ` X ) %s ( %s ` ( F ` X ) ) )' % (A0, DP, DP))
    DF = '( CC _D F )'
    fun2 = w.s([w.s([w.s([], 'dvfcn', '%s : dom %s --> CC' % (DF, DF))], 'a1i', '( %s -> %s : dom %s --> CC )' % (A0, DF, DF))], 'ffund', '( %s -> Fun %s )' % (A0, DF))
    bg = w.s([xd, w.s([fun2, w.inst('funfvbrb')], 'syl', '( %s -> ( X e. dom %s <-> X %s ( %s ` X ) ) )' % (A0, DF, DF, DF))], 'mpbid',
             '( %s -> X %s ( %s ` X ) )' % (A0, DF, DF))
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    CO = '( %s o. F )' % PW
    cob = w.s([pwf, ccs, ff, dcc, ccs, ccs, bf, bg, ej], 'dvcobr', '( %s -> X ( CC _D %s ) ( ( %s ` ( F ` X ) ) x. ( %s ` X ) ) )' % (A0, CO, DP, DF))
    rel = w.s([w.s([], 'reldv', 'Rel ( CC _D %s )' % CO)], 'a1i', '( %s -> Rel ( CC _D %s ) )' % (A0, CO))
    xco = w.s([rel, cob, w.inst('releldm')], 'syl2anc', '( %s -> X e. dom ( CC _D %s ) )' % (A0, CO))
    fz = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A2), w.s([], 'simpr', '( %s -> z e. D )' % A2)], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A2)
    fm = w.s([ff], 'feqmptd', '( %s -> F = ( z e. D |-> ( F ` z ) ) )' % A0)
    pm = w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, PW, PW))
    sb = w.s([], 'oveq1', '( y = ( F ` z ) -> ( y ^ N ) = ( ( F ` z ) ^ N ) )')
    co = w.s([fz, fm, pm, sb], 'fmptco', '( %s -> %s = %s )' % (A0, CO, GN))
    w.qed([xco, w.s([w.s([co], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, CO, GN))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, CO, GN))],
          'eleqtrd', '( %s -> X e. dom ( CC _D %s ) )' % (A0, GN))
    return run8(w)


def gen_rectintmmnx():
    w = W('rectintmmnx', 'The Cauchy estimate of order zero at ` Q ` applied to the N-th power of a function continuous on an open set and differentiable off one point ` P ` ( ~ rectintce0x ).')
    C1 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s )' % (AB, INTP, INTQ, EXO)
    C2 = '( %s /\\ 0 < R )' % RBDQ
    C3 = '( M e. RR /\\ %s )' % ALF
    A1 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
    A0 = '( %s /\\ N e. NN )' % A1
    CONC = '( ( _pi x. R ) x. ( %s ^ N ) ) <_ ( ( M ^ N ) x. %s )' % (AP, PER)
    assert '( %s -> %s )' % (A0, CONC) == S['rectintmmnx']
    a1 = w.s([], 'simpl', '( %s -> %s )' % (A0, A1))
    nn = w.s([], 'simpr', '( %s -> N e. NN )' % A0)
    nn0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    c1 = w.s([a1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, C1))
    c2 = w.s([a1, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, C2))
    c3 = w.s([a1, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, C3))
    ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    pq = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INTP, INTQ))
    ex = w.s([c1, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, EXO))
    ip = w.s([pq, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
    iq = w.s([pq, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
    e1 = w.s([ex, w.inst('simpl')], 'syl', '( %s -> ( F e. ( D -cn-> CC ) /\\ D e. %s ) )' % (A0, TOP))
    e2 = w.s([ex, w.inst('simpr')], 'syl', '( %s -> ( ( D \\ { P } ) C_ dom ( CC _D F ) /\\ ( A crect B ) C_ D ) )' % A0)
    fcn = w.s([e1, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    dpd = w.s([e2, w.inst('simpl')], 'syl', '( %s -> ( D \\ { P } ) C_ dom ( CC _D F ) )' % A0)
    kd = w.s([e2, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    mr = w.s([c3, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
    alf = w.s([c3, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
    fm = w.s([ff], 'feqmptd', '( %s -> F = ( z e. D |-> ( F ` z ) ) )' % A0)
    fmp = w.s([fm, fcn], 'eqeltrrd', '( %s -> ( z e. D |-> ( F ` z ) ) e. ( D -cn-> CC ) )' % A0)
    gcn = w.s([fmp, nn0, w.inst('cncfexpb')], 'syl2anc', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, GN))
    KP = '( ( A crect B ) \\ { P } )'
    A2 = '( %s /\\ v e. %s )' % (A0, KP)
    vk = w.s([], 'simpr', '( %s -> v e. %s )' % (A2, KP))
    kpd = w.s([kd], 'ssdifd', '( %s -> %s C_ ( D \\ { P } ) )' % (A0, KP))
    vdv = w.s([w.s([w.s([kpd, dpd], 'sstrd', '( %s -> %s C_ dom ( CC _D F ) )' % (A0, KP))], 'adantr', '( %s -> %s C_ dom ( CC _D F ) )' % (A2, KP)), vk],
              'sseldd', '( %s -> v e. dom ( CC _D F ) )' % A2)
    vg = w.s([w.s([w.s([ff, dcc], 'jca', '( %s -> ( F : D --> CC /\\ D C_ CC ) )' % A0)], 'adantr', '( %s -> ( F : D --> CC /\\ D C_ CC ) )' % A2),
              w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A2), vdv], 'jca', '( %s -> ( N e. NN /\\ v e. dom ( CC _D F ) ) )' % A2), w.inst('dvexpx')],
             'syl2anc', '( %s -> v e. dom ( CC _D %s ) )' % (A2, GN))
    gdv = w.s([w.s([vg], 'ex', '( %s -> ( v e. %s -> v e. dom ( CC _D %s ) ) )' % (A0, KP, GN))], 'ssrdv', '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, KP, GN))
    exc = w.s([gcn, kd, gdv], '3jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, GN, KP, GN))
    # the frame bound of the N-th power
    frd = w.s([w.s([w.s([ab, ip, w.inst('crectfrp')], 'syl2anc', '( %s -> %s C_ %s )' % (A0, FR, KP)), w.s([w.s([], 'difss', '%s C_ ( A crect B )' % KP)], 'a1i', '( %s -> %s C_ ( A crect B ) )' % (A0, KP))],
                   'sstrd', '( %s -> %s C_ ( A crect B ) )' % (A0, FR)), kd], 'sstrd', '( %s -> %s C_ D )' % (A0, FR))
    A3 = '( %s /\\ v e. %s )' % (A0, FR)
    vf = w.s([], 'simpr', '( %s -> v e. %s )' % (A3, FR))
    vd = w.s([w.s([frd], 'adantr', '( %s -> %s C_ D )' % (A3, FR)), vf], 'sseldd', '( %s -> v e. D )' % A3)
    fv = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A3), vd], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A3)
    subv = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )')], 'oveq1d', '( z = v -> ( ( F ` z ) ^ N ) = ( ( F ` v ) ^ N ) )')
    gvv = mptval(w, A3, 'z', 'D', GN, 'v', '( ( F ` v ) ^ N )', subv, vd)
    n0a = w.s([nn0], 'adantr', '( %s -> N e. NN0 )' % A3)
    abv = w.s([fv, n0a, w.inst('absexp')], 'syl2anc', '( %s -> ( abs ` ( ( F ` v ) ^ N ) ) = ( ( abs ` ( F ` v ) ) ^ N ) )' % A3)
    subu = w.s([w.s([w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')], 'fveq2d', '( u = v -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` v ) ) )')],
               'breq1d', '( u = v -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` v ) ) <_ M ) )')
    bnd = w.s([subu, w.s([alf], 'adantr', '( %s -> %s )' % (A3, ALF)), vf], 'rspcdva', '( %s -> ( abs ` ( F ` v ) ) <_ M )' % A3)
    lex = w.s([w.s([fv], 'abscld', '( %s -> ( abs ` ( F ` v ) ) e. RR )' % A3), w.s([mr], 'adantr', '( %s -> M e. RR )' % A3), n0a,
               w.s([fv], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A3), bnd], 'leexp1ad', '( %s -> ( ( abs ` ( F ` v ) ) ^ N ) <_ ( M ^ N ) )' % A3)
    step = w.s([w.s([w.s([gvv], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` ( ( F ` v ) ^ N ) ) )' % (A3, GN)), abv], 'eqtrd',
                    '( %s -> ( abs ` ( %s ` v ) ) = ( ( abs ` ( F ` v ) ) ^ N ) )' % (A3, GN)), lex], 'eqbrtrd', '( %s -> ( abs ` ( %s ` v ) ) <_ ( M ^ N ) )' % (A3, GN))
    allv = w.s([step], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ ( M ^ N ) )' % (A0, FR, GN))
    cbv = w.s([w.s([w.s([w.s([], 'fveq2', '( v = u -> ( %s ` v ) = ( %s ` u ) )' % (GN, GN))], 'fveq2d', '( v = u -> ( abs ` ( %s ` v ) ) = ( abs ` ( %s ` u ) ) )' % (GN, GN))],
                    'breq1d', '( v = u -> ( ( abs ` ( %s ` v ) ) <_ ( M ^ N ) <-> ( abs ` ( %s ` u ) ) <_ ( M ^ N ) ) )' % (GN, GN))], 'cbvralvw',
              '( A. v e. %s ( abs ` ( %s ` v ) ) <_ ( M ^ N ) <-> A. u e. %s ( abs ` ( %s ` u ) ) <_ ( M ^ N ) )' % (FR, GN, FR, GN))
    allu = w.s([allv, cbv], 'sylib', '( %s -> A. u e. %s ( abs ` ( %s ` u ) ) <_ ( M ^ N ) )' % (A0, FR, GN))
    mn = w.s([mr, nn0], 'reexpcld', '( %s -> ( M ^ N ) e. RR )' % A0)
    CE = tsub(S['rectintce0x'], {'F': GN, 'M': '( M ^ N )'})
    cea, cec = ante_of(CE)
    ce = w.s([w.s([w.s([ab, pq, exc], '3jca', '( %s -> %s )' % (A0, ante_of(cea)[0] if False else cea.split(' /\\ ( ( R e. RR')[0][2:] if False else '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ ( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ %s C_ dom ( CC _D %s ) ) )' % (AB, INTP, INTQ, GN, KP, GN))),
                   c2, w.s([mn, allu], 'jca', '( %s -> ( ( M ^ N ) e. RR /\\ A. u e. %s ( abs ` ( %s ` u ) ) <_ ( M ^ N ) ) )' % (A0, FR, GN))], '3jca', '( %s -> %s )' % (A0, cea)),
              w.inst('rectintce0x')], 'syl', '( %s -> %s )' % (A0, cec))
    icr = w.s([ab, iq, w.inst('crectinp')], 'syl2anc', '( %s -> Q e. ( A crect B ) )' % A0)
    qd = w.s([kd, icr], 'sseldd', '( %s -> Q e. D )' % A0)
    fq = w.s([ff, qd], 'ffvelcdmd', '( %s -> ( F ` Q ) e. CC )' % A0)
    subq = w.s([w.s([], 'fveq2', '( z = Q -> ( F ` z ) = ( F ` Q ) )')], 'oveq1d', '( z = Q -> ( ( F ` z ) ^ N ) = ( ( F ` Q ) ^ N ) )')
    gvq = mptval(w, A0, 'z', 'D', GN, 'Q', '( ( F ` Q ) ^ N )', subq, qd)
    abq = w.s([fq, nn0, w.inst('absexp')], 'syl2anc', '( %s -> ( abs ` ( ( F ` Q ) ^ N ) ) = ( %s ^ N ) )' % (A0, AP))
    eqq = w.s([w.s([gvq], 'fveq2d', '( %s -> ( abs ` ( %s ` Q ) ) = ( abs ` ( ( F ` Q ) ^ N ) ) )' % (A0, GN)), abq], 'eqtrd', '( %s -> ( abs ` ( %s ` Q ) ) = ( %s ^ N ) )' % (A0, GN, AP))
    oq = w.s([w.s([eqq], 'oveq2d', '( %s -> ( ( _pi x. R ) x. ( abs ` ( %s ` Q ) ) ) = ( ( _pi x. R ) x. ( %s ^ N ) ) )' % (A0, GN, AP))], 'eqcomd',
             '( %s -> ( ( _pi x. R ) x. ( %s ^ N ) ) = ( ( _pi x. R ) x. ( abs ` ( %s ` Q ) ) ) )' % (A0, AP, GN))
    w.qed([oq, ce], 'eqbrtrd', '( %s -> %s )' % (A0, CONC))
    return run8(w)


def BODYQ(t):
    return '( ( %s <_ ( %s - %s ) /\\ %s <_ ( %s - %s ) ) /\\ ( %s <_ ( %s - %s ) /\\ %s <_ ( %s - %s ) ) )' % (
        t, RE('Q'), RA, t, RB, RE('Q'), t, IM('Q'), IA, t, IB, IM('Q'))


def gen_rectintmmx():
    w = W('rectintmmx', 'The maximum modulus principle for a rectangle, for a function continuous on an open set containing the rectangle and differentiable there except at one interior point ` P ` ( ~ rectintmm ).')
    C1 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s )' % (AB, INTP, INTQ, EXO)
    A0 = '( %s /\\ ( M e. RR /\\ %s ) )' % (C1, ALF)
    assert '( %s -> %s <_ M )' % (A0, AP) == S['rectintmmx']
    Q1 = '( %s /\\ r e. RR+ )' % A0
    Q0 = '( %s /\\ %s )' % (Q1, BODYQ('r'))
    QN = '( %s /\\ n e. NN )' % Q0
    KK = '( %s / ( _pi x. r ) )' % PER
    RQ, IQ = RE('Q'), IM('Q')
    c1 = w.s([], 'simpl', '( %s -> %s )' % (A0, C1))
    mm_ = w.s([], 'simpr', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
    ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    pq = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INTP, INTQ))
    ex = w.s([c1, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, EXO))
    iq = w.s([pq, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
    fcn = w.s([w.s([ex, w.inst('simpl')], 'syl', '( %s -> ( F e. ( D -cn-> CC ) /\\ D e. %s ) )' % (A0, TOP)), w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    rdd = w.s([w.s([ex, w.inst('simpr')], 'syl', '( %s -> ( ( D \\ { P } ) C_ dom ( CC _D F ) /\\ ( A crect B ) C_ D ) )' % A0), w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    mr = w.s([mm_, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
    alf = w.s([mm_, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    qc = w.s([iq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
    ineq = w.s([iq, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RQ, RQ, RB, IA, IQ, IQ, IB))
    lt = [w.s([ineq, w.inst(r)], 'syl', '( %s -> %s )' % (A0, f)) for r, f in
          [('simpll', '%s < %s' % (RA, RQ)), ('simplr', '%s < %s' % (RQ, RB)), ('simprl', '%s < %s' % (IA, IQ)), ('simprr', '%s < %s' % (IQ, IB))]]
    ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
    ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    qr = w.s([qc], 'recld', '( %s -> %s e. RR )' % (A0, RQ)); qi = w.s([qc], 'imcld', '( %s -> %s e. RR )' % (A0, IQ))
    ltr = w.s([ar, qr, br, lt[0], lt[1]], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))
    lti = w.s([ai, qi, bi, lt[2], lt[3]], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))
    geo = w.s([w.s([ltr], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB)), w.s([lti], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))], 'jca', '( %s -> %s )' % (A0, GEO))
    d1 = w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA))
    d2 = w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))
    p1 = w.s([ltr, w.s([ar, br], 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A0, RA, RB, RB, RA))], 'mpbid', '( %s -> 0 < ( %s - %s ) )' % (A0, RB, RA))
    p2 = w.s([lti, w.s([ai, bi], 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A0, IA, IB, IB, IA))], 'mpbid', '( %s -> 0 < ( %s - %s ) )' % (A0, IB, IA))
    perp = w.s([w.s([d1, p1], 'elrpd', '( %s -> ( %s - %s ) e. RR+ )' % (A0, RB, RA)), w.s([d2, p2], 'elrpd', '( %s -> ( %s - %s ) e. RR+ )' % (A0, IB, IA))],
               'rpaddcld', '( %s -> %s e. RR+ )' % (A0, PER))
    fra = w.s([ab, geo, w.inst('crectfra')], 'syl2anc', '( %s -> A e. %s )' % (A0, FR))
    fru = w.s([ab, geo, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( A crect B ) )' % (A0, FR))
    adm = w.s([w.s([fru, rdd], 'sstrd', '( %s -> %s C_ D )' % (A0, FR)), fra], 'sseldd', '( %s -> A e. D )' % A0)
    faC = w.s([ff, adm], 'ffvelcdmd', '( %s -> ( F ` A ) e. CC )' % A0)
    suba = w.s([w.s([w.s([], 'fveq2', '( u = A -> ( F ` u ) = ( F ` A ) )')], 'fveq2d', '( u = A -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` A ) ) )')],
               'breq1d', '( u = A -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` A ) ) <_ M ) )')
    bnda = w.s([suba, alf, fra], 'rspcdva', '( %s -> ( abs ` ( F ` A ) ) <_ M )' % A0)
    m0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.s([faC], 'abscld', '( %s -> ( abs ` ( F ` A ) ) e. RR )' % A0), mr,
              w.s([faC], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` A ) ) )' % A0), bnda], 'letrd', '( %s -> 0 <_ M )' % A0)
    qd = w.s([rdd, w.s([ab, iq, w.inst('crectinp')], 'syl2anc', '( %s -> Q e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> Q e. D )' % A0)
    fq = w.s([ff, qd], 'ffvelcdmd', '( %s -> ( F ` Q ) e. CC )' % A0)
    apr = w.s([fq], 'abscld', '( %s -> %s e. RR )' % (A0, AP))
    ap0 = w.s([fq], 'absge0d', '( %s -> 0 <_ %s )' % (A0, AP))
    rrp = w.s([w.s([], 'simpr', '( %s -> r e. RR+ )' % Q1)], 'adantr', '( %s -> r e. RR+ )' % Q0)
    body = w.s([], 'simpr', '( %s -> %s )' % (Q0, BODYQ('r')))
    rre = w.s([rrp], 'rpred', '( %s -> r e. RR )' % Q0)
    rpos = w.s([rrp], 'rpgt0d', '( %s -> 0 < r )' % Q0)
    RBr = '( r e. RR /\\ %s )' % BODYQ('r')
    assert RBr == RBD('Q', 'r')
    rbd = w.s([rre, body], 'jca', '( %s -> %s )' % (Q0, RBr))
    pird = w.s([w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % Q0), rrp], 'rpmulcld', '( %s -> ( _pi x. r ) e. RR+ )' % Q0)

    def lift0(st, form):
        return w.s([w.s([st], 'adantr', '( %s -> %s )' % (Q1, form))], 'adantr', '( %s -> %s )' % (Q0, form))
    c1q = lift0(c1, C1); mrq = lift0(mr, 'M e. RR'); alfq = lift0(alf, ALF)
    perq = lift0(perp, '%s e. RR+' % PER); aprq = lift0(apr, '%s e. RR' % AP); ap0q = lift0(ap0, '0 <_ %s' % AP)
    m0q = lift0(m0, '0 <_ M')
    kkrp = w.s([perq, pird], 'rpdivcld', '( %s -> %s e. RR+ )' % (Q0, KK))
    nn = w.s([], 'simpr', '( %s -> n e. NN )' % QN)
    nn0 = w.s([nn], 'nnnn0d', '( %s -> n e. NN0 )' % QN)
    ad = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (QN, f))
    c1n = ad(c1q, C1); mrn = ad(mrq, 'M e. RR'); alfn = ad(alfq, ALF); rbdn = ad(rbd, RBr); rposn = ad(rpos, '0 < r')
    pirdn = ad(pird, '( _pi x. r ) e. RR+'); perrn = w.s([ad(perq, '%s e. RR+' % PER)], 'rpred', '( %s -> %s e. RR )' % (QN, PER)); aprn = ad(aprq, '%s e. RR' % AP)
    MMN = tsub(S['rectintmmnx'], {'R': 'r', 'N': 'n'})
    mma, mmc = ante_of(MMN)
    mmn = w.s([w.s([w.s([c1n, w.s([rbdn, rposn], 'jca', '( %s -> ( %s /\\ 0 < r ) )' % (QN, RBr)), w.s([mrn, alfn], 'jca', '( %s -> ( M e. RR /\\ %s ) )' % (QN, ALF))],
                         '3jca', '( %s -> %s )' % (QN, mma[2:-len(' /\\ n e. NN )') + 1] if False else mma.rsplit(' /\\ n e. NN', 1)[0][2:])), nn], 'jca', '( %s -> %s )' % (QN, mma)),
               w.inst('rectintmmnx')], 'syl', '( %s -> %s )' % (QN, mmc))
    apn = w.s([aprn, nn0], 'reexpcld', '( %s -> ( %s ^ n ) e. RR )' % (QN, AP))
    mn = w.s([mrn, nn0], 'reexpcld', '( %s -> ( M ^ n ) e. RR )' % QN)
    mpr = w.s([mn, perrn], 'remulcld', '( %s -> ( ( M ^ n ) x. %s ) e. RR )' % (QN, PER))
    piC = w.s([pirdn], 'rpred', '( %s -> ( _pi x. r ) e. RR )' % QN)
    piP = w.s([pirdn], 'rpgt0d', '( %s -> 0 < ( _pi x. r ) )' % QN)
    div1 = w.s([mmn, w.s([apn, mpr, w.s([piC, piP], 'jca', '( %s -> ( ( _pi x. r ) e. RR /\\ 0 < ( _pi x. r ) ) )' % QN), w.inst('lemuldiv2')], 'syl3anc',
                         '( %s -> ( ( ( _pi x. r ) x. ( %s ^ n ) ) <_ ( ( M ^ n ) x. %s ) <-> ( %s ^ n ) <_ ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) ) )' % (QN, AP, PER, AP, PER))],
                'mpbid', '( %s -> ( %s ^ n ) <_ ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) )' % (QN, AP, PER))
    mnc = w.s([mn], 'recnd', '( %s -> ( M ^ n ) e. CC )' % QN)
    perc = w.s([perrn], 'recnd', '( %s -> %s e. CC )' % (QN, PER))
    pic = w.s([piC], 'recnd', '( %s -> ( _pi x. r ) e. CC )' % QN)
    pine = w.s([pirdn], 'rpne0d', '( %s -> ( _pi x. r ) =/= 0 )' % QN)
    eq1 = w.s([w.s([mnc, perc], 'mulcomd', '( %s -> ( ( M ^ n ) x. %s ) = ( %s x. ( M ^ n ) ) )' % (QN, PER, PER))], 'oveq1d',
              '( %s -> ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) = ( ( %s x. ( M ^ n ) ) / ( _pi x. r ) ) )' % (QN, PER, PER))
    eq2 = w.s([perc, mnc, pic, pine], 'div23d', '( %s -> ( ( %s x. ( M ^ n ) ) / ( _pi x. r ) ) = ( %s x. ( M ^ n ) ) )' % (QN, PER, KK))
    stepn = w.s([div1, w.s([eq1, eq2], 'eqtrd', '( %s -> ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) = ( %s x. ( M ^ n ) ) )' % (QN, PER, KK))],
                'breqtrd', '( %s -> ( %s ^ n ) <_ ( %s x. ( M ^ n ) ) )' % (QN, AP, KK))
    alln = w.s([stepn], 'ralrimiva', '( %s -> A. n e. NN ( %s ^ n ) <_ ( %s x. ( M ^ n ) ) )' % (Q0, AP, KK))
    edl = w.s([w.s([aprq, ap0q], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (Q0, AP, AP)),
               w.s([mrq, m0q], 'jca', '( %s -> ( M e. RR /\\ 0 <_ M ) )' % Q0),
               w.s([w.s([w.s([kkrp], 'rpred', '( %s -> %s e. RR )' % (Q0, KK)), w.s([kkrp], 'rpgt0d', '( %s -> 0 < %s )' % (Q0, KK))], 'jca',
                        '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (Q0, KK, KK)), alln], 'jca',
                   '( %s -> ( ( %s e. RR /\\ 0 < %s ) /\\ A. n e. NN ( %s ^ n ) <_ ( %s x. ( M ^ n ) ) ) )' % (Q0, KK, KK, AP, KK)),
               w.inst('expdomle')], 'syl3anc', '( %s -> %s <_ M )' % (Q0, AP))
    exq = w.s([edl], 'ex', '( %s -> ( %s -> %s <_ M ) )' % (Q1, BODYQ('r'), AP))
    rex = w.s([ab, iq, w.inst('crectrbd')], 'syl2anc', '( %s -> E. r e. RR+ %s )' % (A0, BODYQ('r')))
    w.qed([w.s([exq], 'rexlimdva', '( %s -> ( E. r e. RR+ %s -> %s <_ M ) )' % (A0, BODYQ('r'), AP)), rex], 'mpd', '( %s -> %s <_ M )' % (A0, AP))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_rectintce0x, gen_dvexpx, gen_rectintmmnx, gen_rectintmmx]:
        g()
