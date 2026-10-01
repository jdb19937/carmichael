"""Sortie C8, section 3: the sharp Schwarz lemma (rectintschx) and the sharp
Borel-Caratheodory inequality (rectintbcx) on a rectangle."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
from cl import lift
from c8_freeze import S, INTQ, ALF

RBDP = RBD('P', 'R')
C0 = '( ( CC _D F ) ` P )'


def XQ(T, G='F'):
    return '( ( ( %s ` %s ) - ( %s ` P ) ) / ( %s - P ) )' % (G, T, G, T)


def DSM(G='F'):
    return '( z e. D |-> if ( z = P , ( ( CC _D %s ) ` P ) , %s ) )' % (G, XQ('z', G))


def dsval(w, ante, T, tne, G='F'):
    """( ante -> ( DS ` T ) = XQ(T) ) from tne : ( ante -> T =/= P ) and ante -> T e. D given as tne2"""
    raise NotImplementedError


def dsvalue(w, ante, T, tne, td, G='F'):
    """( ante -> ( DSM ` T ) = XQ(T) ) from tne : ( ante -> T =/= P ), td : ( ante -> T e. D )"""
    A1 = '( %s /\\ z = %s )' % (ante, T)
    zt = w.s([], 'simpr', '( %s -> z = %s )' % (A1, T))
    tn1 = w.s([tne], 'adantr', '( %s -> %s =/= P )' % (A1, T))
    zn = w.s([tn1, w.s([zt], 'neeq1d', '( %s -> ( z =/= P <-> %s =/= P ) )' % (A1, T))], 'mpbird', '( %s -> z =/= P )' % A1)
    ifz = w.s([w.s([zn], 'neneqd', '( %s -> -. z = P )' % A1)], 'iffalsed', '( %s -> if ( z = P , ( ( CC _D %s ) ` P ) , %s ) = %s )' % (A1, G, XQ('z', G), XQ('z', G)))
    xz = w.s([w.s([w.s([zt], 'fveq2d', '( %s -> ( %s ` z ) = ( %s ` %s ) )' % (A1, G, G, T))], 'oveq1d', '( %s -> ( ( %s ` z ) - ( %s ` P ) ) = ( ( %s ` %s ) - ( %s ` P ) ) )' % (A1, G, G, G, T, G)),
              w.s([zt], 'oveq1d', '( %s -> ( z - P ) = ( %s - P ) )' % (A1, T))], 'oveq12d', '( %s -> %s = %s )' % (A1, XQ('z', G), XQ(T, G)))
    body = w.s([ifz, xz], 'eqtrd', '( %s -> if ( z = P , ( ( CC _D %s ) ` P ) , %s ) = %s )' % (A1, G, XQ('z', G), XQ(T, G)))
    return w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, DSM(G), DSM(G))), body, td, ovexd(w, ante, XQ(T, G))], 'fvmptd',
               '( %s -> ( %s ` %s ) = %s )' % (ante, DSM(G), T, XQ(T, G)))


def gen_rectintschx():
    w = W('rectintschx', 'The sharp Schwarz lemma on a rectangle: a holomorphic function vanishing at an interior point ` P ` is bounded at ` Q ` by its frame bound times ` abs ( Q - P ) / R ` , where ` R ` is below the four coordinate gaps of ` P ` ( ~ rectintmmx on the difference quotient).')
    C1 = '( %s /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( A crect B ) C_ D ) )' % (AB, INTP, INTQ, HOL)
    C2 = '( ( %s /\\ 0 < R ) /\\ ( ( M e. RR /\\ %s ) /\\ ( F ` P ) = 0 ) )' % (RBDP, ALF)
    A0 = '( %s /\\ %s )' % (C1, C2)
    AQ = '( abs ` ( F ` Q ) )'
    DQ = '( abs ` ( Q - P ) )'
    CONC = '( %s x. R ) <_ ( M x. %s )' % (AQ, DQ)
    assert '( %s -> %s )' % (A0, CONC) == S['rectintschx']
    c1 = w.s([], 'simpl', '( %s -> %s )' % (A0, C1))
    c2 = w.s([], 'simpr', '( %s -> %s )' % (A0, C2))
    ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    ipq = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, INTP, INTQ))
    hd = w.s([c1, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ ( A crect B ) C_ D ) )' % (A0, HOL))
    ip = w.s([ipq, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, INTP))
    iq = w.s([ipq, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, INTQ))
    hol = w.s([hd, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    kd = w.s([hd, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    fcn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    dd = w.s([hol, w.inst('simpr')], 'syl', '( %s -> D C_ dom ( CC _D F ) )' % A0)
    rb0 = w.s([c2, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
    rbd = w.s([rb0, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP))
    rpos = w.s([rb0, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
    rr = w.s([rbd, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
    rrp = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
    ma = w.s([c2, w.inst('simpr')], 'syl', '( %s -> ( ( M e. RR /\\ %s ) /\\ ( F ` P ) = 0 ) )' % (A0, ALF))
    mal = w.s([ma, w.inst('simpl')], 'syl', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
    fp0 = w.s([ma, w.inst('simpr')], 'syl', '( %s -> ( F ` P ) = 0 )' % A0)
    mr = w.s([mal, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
    alf = w.s([mal, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    pc = w.s([ip, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    qc = w.s([iq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
    pd = w.s([kd, w.s([ab, ip, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> P e. D )' % A0)
    qd = w.s([kd, w.s([ab, iq, w.inst('crectinp')], 'syl2anc', '( %s -> Q e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> Q e. D )' % A0)
    fq = w.s([ff, qd], 'ffvelcdmd', '( %s -> ( F ` Q ) e. CC )' % A0)
    # ---- case P = Q
    AE = '( %s /\\ P = Q )' % A0
    pe = w.s([], 'simpr', '( %s -> P = Q )' % AE)
    fq0 = w.s([w.s([pe], 'fveq2d', '( %s -> ( F ` P ) = ( F ` Q ) )' % AE), lift(w, fp0, AE)], 'eqtr3d', '( %s -> ( F ` Q ) = 0 )' % AE)
    aq0 = w.s([w.s([fq0], 'fveq2d', '( %s -> %s = ( abs ` 0 ) )' % (AE, AQ)), closed(w, AE, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( %s -> %s = 0 )' % (AE, AQ))
    rce = w.s([lift(w, rr, AE)], 'recnd', '( %s -> R e. CC )' % AE)
    l0 = w.s([w.s([aq0], 'oveq1d', '( %s -> ( %s x. R ) = ( 0 x. R ) )' % (AE, AQ)), w.s([rce], 'mul02d', '( %s -> ( 0 x. R ) = 0 )' % AE)], 'eqtrd',
             '( %s -> ( %s x. R ) = 0 )' % (AE, AQ))
    qp0 = w.s([w.s([w.s([pe], 'eqcomd', '( %s -> Q = P )' % AE)], 'oveq1d', '( %s -> ( Q - P ) = ( P - P ) )' % AE), w.s([lift(w, pc, AE)], 'subidd', '( %s -> ( P - P ) = 0 )' % AE)],
              'eqtrd', '( %s -> ( Q - P ) = 0 )' % AE)
    dq0 = w.s([w.s([qp0], 'fveq2d', '( %s -> %s = ( abs ` 0 ) )' % (AE, DQ)), closed(w, AE, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( %s -> %s = 0 )' % (AE, DQ))
    r0 = w.s([w.s([dq0], 'oveq2d', '( %s -> ( M x. %s ) = ( M x. 0 ) )' % (AE, DQ)), w.s([w.s([lift(w, mr, AE)], 'recnd', '( %s -> M e. CC )' % AE)], 'mul01d', '( %s -> ( M x. 0 ) = 0 )' % AE)],
             'eqtrd', '( %s -> ( M x. %s ) = 0 )' % (AE, DQ))
    le0 = w.s([closed(w, AE, '0le0', '0 <_ 0'), r0], 'breqtrrd', '( %s -> 0 <_ ( M x. %s ) )' % (AE, DQ))
    case1 = w.s([l0, le0], 'eqbrtrd', '( %s -> %s )' % (AE, CONC))
    # ---- case P =/= Q
    AN = '( %s /\\ P =/= Q )' % A0
    L = lambda st: lift(w, st, AN)
    pnq = w.s([], 'simpr', '( %s -> P =/= Q )' % AN)
    DS = DSM()
    pdm = w.s([L(dd), L(pd)], 'sseldd', '( %s -> P e. dom ( CC _D F ) )' % AN)
    dcn = w.s([L(fcn), pdm, w.s([], 'eqidd', '( %s -> %s = %s )' % (AN, C0, C0)), w.inst('dscn')], 'syl3anc', '( %s -> %s e. ( D -cn-> CC ) )' % (AN, DS))
    dvf = w.s([L(hol), w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : D --> CC )' % AN)
    c0c = w.s([dvf, L(pd)], 'ffvelcdmd', '( %s -> %s e. CC )' % (AN, C0))
    dsd = w.s([L(fcn), L(pd), c0c, w.inst('dsdv')], 'syl3anc', '( %s -> ( dom ( CC _D F ) \\ { P } ) C_ dom ( CC _D %s ) )' % (AN, DS))
    dpd = w.s([w.s([L(dd)], 'ssdifd', '( %s -> ( D \\ { P } ) C_ ( dom ( CC _D F ) \\ { P } ) )' % AN), dsd], 'sstrd', '( %s -> ( D \\ { P } ) C_ dom ( CC _D %s ) )' % (AN, DS))
    dop = w.s([L(hol), w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (AN, TOP))
    EXOD = '( ( %s e. ( D -cn-> CC ) /\\ D e. %s ) /\\ ( ( D \\ { P } ) C_ dom ( CC _D %s ) /\\ ( A crect B ) C_ D ) )' % (DS, TOP, DS)
    exo = w.s([w.s([dcn, dop], 'jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ D e. %s ) )' % (AN, DS, TOP)),
               w.s([dpd, L(kd)], 'jca', '( %s -> ( ( D \\ { P } ) C_ dom ( CC _D %s ) /\\ ( A crect B ) C_ D ) )' % (AN, DS))], 'jca', '( %s -> %s )' % (AN, EXOD))
    # frame bound M / R
    MR = '( M / R )'
    A3 = '( %s /\\ v e. %s )' % (AN, FR)
    uf = w.s([], 'simpr', '( %s -> v e. %s )' % (A3, FR))
    KP = '( ( A crect B ) \\ { P } )'
    fru = w.s([ab, ip, w.inst('crectfrp')], 'syl2anc', '( %s -> %s C_ %s )' % (A0, FR, KP))
    ukp = w.s([lift(w, fru, A3), uf], 'sseldd', '( %s -> v e. %s )' % (A3, KP))
    uel = w.s([ukp, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. ( A crect B ) /\\ v =/= P ) )' % A3)
    uk = w.s([uel, w.inst('simpl')], 'syl', '( %s -> v e. ( A crect B ) )' % A3)
    une = w.s([uel, w.inst('simpr')], 'syl', '( %s -> v =/= P )' % A3)
    ud = w.s([lift(w, kd, A3), uk], 'sseldd', '( %s -> v e. D )' % A3)
    uc = w.s([w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0) and lift(w, w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0), A3), uk], 'sseldd', '( %s -> v e. CC )' % A3)
    dsu = dsvalue(w, A3, 'v', une, ud)
    fu = w.s([lift(w, ff, A3), ud], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A3)
    up = w.s([uc, lift(w, pc, A3)], 'subcld', '( %s -> ( v - P ) e. CC )' % A3)
    upn = w.s([uc, lift(w, pc, A3), une], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % A3)
    fu0 = w.s([w.s([lift(w, fp0, A3)], 'oveq2d', '( %s -> ( ( F ` v ) - ( F ` P ) ) = ( ( F ` v ) - 0 ) )' % A3), w.s([fu], 'subid1d', '( %s -> ( ( F ` v ) - 0 ) = ( F ` v ) )' % A3)],
              'eqtrd', '( %s -> ( ( F ` v ) - ( F ` P ) ) = ( F ` v ) )' % A3)
    xu = w.s([fu0], 'oveq1d', '( %s -> %s = ( ( F ` v ) / ( v - P ) ) )' % (A3, XQ('v')))
    absu = w.s([w.s([w.s([dsu, xu], 'eqtrd', '( %s -> ( %s ` v ) = ( ( F ` v ) / ( v - P ) ) )' % (A3, DS))], 'fveq2d',
                    '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` ( ( F ` v ) / ( v - P ) ) ) )' % (A3, DS)),
                w.s([fu, up, upn], 'absdivd', '( %s -> ( abs ` ( ( F ` v ) / ( v - P ) ) ) = ( ( abs ` ( F ` v ) ) / ( abs ` ( v - P ) ) ) )' % A3)], 'eqtrd',
               '( %s -> ( abs ` ( %s ` v ) ) = ( ( abs ` ( F ` v ) ) / ( abs ` ( v - P ) ) ) )' % (A3, DS))
    fub = w.s([w.s([w.s([w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')], 'fveq2d', '( u = v -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` v ) ) )')], 'breq1d', '( u = v -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` v ) ) <_ M ) )'), lift(w, alf, A3), uf], 'rspcdva', '( %s -> ( abs ` ( F ` v ) ) <_ M )' % A3)
    DIS = 'A. u e. %s R <_ ( abs ` ( u - P ) )' % FR
    dis = w.s([ab, ip, rbd, w.inst('crectdis')], 'syl3anc', '( %s -> %s )' % (A0, DIS))
    rub = w.s([w.s([w.s([w.s([], 'oveq1', '( u = v -> ( u - P ) = ( v - P ) )')], 'fveq2d', '( u = v -> ( abs ` ( u - P ) ) = ( abs ` ( v - P ) ) )')], 'breq2d', '( u = v -> ( R <_ ( abs ` ( u - P ) ) <-> R <_ ( abs ` ( v - P ) ) ) )'), lift(w, dis, A3), uf], 'rspcdva', '( %s -> R <_ ( abs ` ( v - P ) ) )' % A3)
    ldv = w.s([w.s([fu], 'abscld', '( %s -> ( abs ` ( F ` v ) ) e. RR )' % A3), lift(w, mr, A3), lift(w, rrp, A3), w.s([up], 'abscld', '( %s -> ( abs ` ( v - P ) ) e. RR )' % A3),
               w.s([fu], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A3), fub, rub], 'lediv12ad',
              '( %s -> ( ( abs ` ( F ` v ) ) / ( abs ` ( v - P ) ) ) <_ %s )' % (A3, MR))
    bu = w.s([absu, ldv], 'eqbrtrd', '( %s -> ( abs ` ( %s ` v ) ) <_ %s )' % (A3, DS, MR))
    ALFD = 'A. u e. %s ( abs ` ( %s ` u ) ) <_ %s' % (FR, DS, MR)
    ALFV = 'A. v e. %s ( abs ` ( %s ` v ) ) <_ %s' % (FR, DS, MR)
    allv = w.s([bu], 'ralrimiva', '( %s -> %s )' % (AN, ALFV))
    cbv = w.s([w.s([w.s([w.s([], 'fveq2', '( v = u -> ( %s ` v ) = ( %s ` u ) )' % (DS, DS))], 'fveq2d', '( v = u -> ( abs ` ( %s ` v ) ) = ( abs ` ( %s ` u ) ) )' % (DS, DS))],
                    'breq1d', '( v = u -> ( ( abs ` ( %s ` v ) ) <_ %s <-> ( abs ` ( %s ` u ) ) <_ %s ) )' % (DS, MR, DS, MR))], 'cbvralvw', '( %s <-> %s )' % (ALFV, ALFD))
    allu = w.s([allv, cbv], 'sylib', '( %s -> %s )' % (AN, ALFD))
    mrr = w.s([L(mr), L(rrp)], 'rerpdivcld', '( %s -> %s e. RR )' % (AN, MR))
    MMX = tsub(S['rectintmmx'], {'F': DS, 'M': MR})
    mxa, mxc = ante_of(MMX)
    MXA1 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s )' % (AB, INTP, INTQ, EXOD)
    assert mxa == '( %s /\\ ( %s e. RR /\\ %s ) )' % (MXA1, MR, ALFD)
    mx = w.s([w.s([w.s([L(ab), w.s([L(ip), L(iq), pnq], '3jca', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (AN, INTP, INTQ)), exo], '3jca', '( %s -> %s )' % (AN, MXA1)),
                   w.s([mrr, allu], 'jca', '( %s -> ( %s e. RR /\\ %s ) )' % (AN, MR, ALFD))], 'jca', '( %s -> %s )' % (AN, mxa)), w.inst('rectintmmx')], 'syl', '( %s -> %s )' % (AN, mxc))
    # value at Q
    qne = w.s([pnq], 'necomd', '( %s -> Q =/= P )' % AN)
    dsq = dsvalue(w, AN, 'Q', qne, L(qd))
    fq0 = w.s([w.s([L(fp0)], 'oveq2d', '( %s -> ( ( F ` Q ) - ( F ` P ) ) = ( ( F ` Q ) - 0 ) )' % AN), w.s([L(fq)], 'subid1d', '( %s -> ( ( F ` Q ) - 0 ) = ( F ` Q ) )' % AN)],
              'eqtrd', '( %s -> ( ( F ` Q ) - ( F ` P ) ) = ( F ` Q ) )' % AN)
    qp = w.s([L(qc), L(pc)], 'subcld', '( %s -> ( Q - P ) e. CC )' % AN)
    qpn = w.s([L(qc), L(pc), qne], 'subne0d', '( %s -> ( Q - P ) =/= 0 )' % AN)
    absq = w.s([w.s([w.s([dsq, w.s([fq0], 'oveq1d', '( %s -> %s = ( ( F ` Q ) / ( Q - P ) ) )' % (AN, XQ('Q')))], 'eqtrd', '( %s -> ( %s ` Q ) = ( ( F ` Q ) / ( Q - P ) ) )' % (AN, DS))],
                    'fveq2d', '( %s -> ( abs ` ( %s ` Q ) ) = ( abs ` ( ( F ` Q ) / ( Q - P ) ) ) )' % (AN, DS)),
                w.s([L(fq), qp, qpn], 'absdivd', '( %s -> ( abs ` ( ( F ` Q ) / ( Q - P ) ) ) = ( %s / %s ) )' % (AN, AQ, DQ))], 'eqtrd',
               '( %s -> ( abs ` ( %s ` Q ) ) = ( %s / %s ) )' % (AN, DS, AQ, DQ))
    AD = '( %s / %s )' % (AQ, DQ)
    b1 = w.s([absq, mx], 'eqbrtrrd', '( %s -> %s <_ %s )' % (AN, AD, MR))
    dqp = w.s([qp, qpn], 'absrpcld', '( %s -> %s e. RR+ )' % (AN, DQ))
    aqr = w.s([L(fq)], 'abscld', '( %s -> %s e. RR )' % (AN, AQ))
    adr = w.s([aqr, dqp], 'rerpdivcld', '( %s -> %s e. RR )' % (AN, AD))
    b2 = w.s([adr, mrr, L(rr), w.s([L(rrp)], 'rpge0d', '( %s -> 0 <_ R )' % AN), b1], 'lemul1ad', '( %s -> ( %s x. R ) <_ ( %s x. R ) )' % (AN, AD, MR))
    rc = w.s([L(rr)], 'recnd', '( %s -> R e. CC )' % AN)
    mc = w.s([L(mr)], 'recnd', '( %s -> M e. CC )' % AN)
    e1 = w.s([mc, rc, w.s([L(rrp)], 'rpne0d', '( %s -> R =/= 0 )' % AN)], 'divcan1d', '( %s -> ( %s x. R ) = M )' % (AN, MR))
    b3 = w.s([b2, e1], 'breqtrd', '( %s -> ( %s x. R ) <_ M )' % (AN, AD))
    dqr = w.s([dqp], 'rpred', '( %s -> %s e. RR )' % (AN, DQ))
    b4 = w.s([w.s([adr, L(rr)], 'remulcld', '( %s -> ( %s x. R ) e. RR )' % (AN, AD)), L(mr), dqr, w.s([dqp], 'rpge0d', '( %s -> 0 <_ %s )' % (AN, DQ)), b3], 'lemul1ad',
             '( %s -> ( ( %s x. R ) x. %s ) <_ ( M x. %s ) )' % (AN, AD, DQ, DQ))
    adc = w.s([adr], 'recnd', '( %s -> %s e. CC )' % (AN, AD))
    dqc = w.s([dqr], 'recnd', '( %s -> %s e. CC )' % (AN, DQ))
    e2 = w.s([adc, rc, dqc], 'mul32d', '( %s -> ( ( %s x. R ) x. %s ) = ( ( %s x. %s ) x. R ) )' % (AN, AD, DQ, AD, DQ))
    e3 = w.s([w.s([w.s([aqr], 'recnd', '( %s -> %s e. CC )' % (AN, AQ)), dqc, w.s([dqp], 'rpne0d', '( %s -> %s =/= 0 )' % (AN, DQ))], 'divcan1d', '( %s -> ( %s x. %s ) = %s )' % (AN, AD, DQ, AQ))],
             'oveq1d', '( %s -> ( ( %s x. %s ) x. R ) = ( %s x. R ) )' % (AN, AD, DQ, AQ))
    e4 = w.s([e2, e3], 'eqtrd', '( %s -> ( ( %s x. R ) x. %s ) = ( %s x. R ) )' % (AN, AD, DQ, AQ))
    case2 = w.s([e4, b4], 'eqbrtrrd', '( %s -> %s )' % (AN, CONC))
    w.qed([case1, case2], 'pm2.61dane', '( %s -> %s )' % (A0, CONC))
    return run8(w)


def bc_body():
    """C2's rectintbc generator, lines 257-402: the Moebius transform GM is
    holomorphic on D, bounded by 1 on the frame, and vanishes at P"""
    L = open(os.path.join(os.path.dirname(__file__), 'c2_bc.py')).read().split('\n')
    body = '\n'.join(L[256:402])
    assert body.startswith('# the denominator is nonzero on D') and 'gp0 = ' in body and 'rectintsch' not in body
    return body


def gen_rectintbcx():
    w = W('rectintbcx', 'The sharp Borel-Caratheodory inequality on a rectangle: a function holomorphic on an open set containing the rectangle, vanishing at an interior point ` P ` , with real part at most ` M ` , is bounded at ` Q ` by ` 2 M abs ( Q - P ) / ( R - abs ( Q - P ) ) ` ( Lean ` borelCaratheodory_zero ` ; ~ rectintschx on the Moebius transform).')
    REH = 'A. y e. D ( Re ` ( F ` y ) ) <_ M'
    DQ = '( abs ` ( Q - P ) )'
    C1 = '( %s /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( A crect B ) C_ D ) )' % (AB, INTP, INTQ, HOL)
    C2 = '( ( M e. RR /\\ 0 < M /\\ %s ) /\\ ( F ` P ) = 0 )' % REH
    C3 = '( ( %s /\\ 0 < R ) /\\ %s < R )' % (RBDP, DQ)
    A0 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
    BND = '( ( ( 2 x. M ) x. %s ) / ( R - %s ) )' % (DQ, DQ)
    assert '( %s -> ( abs ` ( F ` Q ) ) <_ %s )' % (A0, BND) == S['rectintbcx']
    c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1))
    c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2))
    c3 = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
    ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    ipq = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, INTP, INTQ))
    hd = w.s([c1, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ ( A crect B ) C_ D ) )' % (A0, HOL))
    it = w.s([ipq, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, INTP))
    iq = w.s([ipq, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, INTQ))
    hl = w.s([hd, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    rdd = w.s([hd, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    mm0 = w.s([c2, w.inst('simpl')], 'syl', '( %s -> ( M e. RR /\\ 0 < M /\\ %s ) )' % (A0, REH))
    fp0 = w.s([c2, w.inst('simpr')], 'syl', '( %s -> ( F ` P ) = 0 )' % A0)
    mr = w.s([mm0, w.inst('simp1')], 'syl', '( %s -> M e. RR )' % A0)
    mp_ = w.s([mm0, w.inst('simp2')], 'syl', '( %s -> 0 < M )' % A0)
    reh = w.s([mm0, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, REH))
    rb0 = w.s([c3, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
    dqlt = w.s([c3, w.inst('simpr')], 'syl', '( %s -> %s < R )' % (A0, DQ))
    rr = w.s([w.s([rb0, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP)), w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
    rpos = w.s([rb0, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
    rrp = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
    fcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    dop = w.s([hl, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
    dvfd = w.s([hl, w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : D --> CC )' % A0)
    mrc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
    t2c = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
    m2c = w.s([t2c, mrc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0)
    m0 = w.s([mp_], 'ltled', '( %s -> 0 <_ M )' % A0)
    ns = dict(globals()); ns.update(locals())
    ns.update(dict(DZ='( ( 2 x. M ) - ( F ` z ) )', AZ='( %s /\\ z e. D )' % A0, C0S='( CC \\ { 0 } )'))
    ns['GM'] = MP('z', 'D', '( ( F ` z ) / %s )' % ns['DZ'])
    ns['DU'] = lambda X: '( ( 2 x. M ) - ( F ` %s ) )' % X
    ns['GMV'] = lambda X: '( ( F ` %s ) / %s )' % (X, ns['DU'](X))
    exec(bc_body(), ns)
    GM, GMV, hgm, allu, gp0, qd, fqc, pc, qc = [ns[k] for k in ('GM', 'GMV', 'hgm', 'allu', 'gp0', 'qd', 'fqc', 'pc', 'qc')]
    gmval = ns['gmval']
    # sharp Schwarz on the Moebius transform, frame bound 1
    SCH = tsub(S['rectintschx'], {'F': GM, 'M': '1'})
    sa, sc = ante_of(SCH)
    S1 = '( %s /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( A crect B ) C_ D ) )' % (AB, INTP, INTQ, HOLG(GM))
    AL1 = 'A. u e. %s ( abs ` ( %s ` u ) ) <_ 1' % (FR, GM)
    S2 = '( ( %s /\\ 0 < R ) /\\ ( ( 1 e. RR /\\ %s ) /\\ ( %s ` P ) = 0 ) )' % (RBDP, AL1, GM)
    assert sa == '( %s /\\ %s )' % (S1, S2)
    sch = w.s([w.s([w.s([ab, ipq, w.s([hgm, rdd], 'jca', '( %s -> ( %s /\\ ( A crect B ) C_ D ) )' % (A0, HOLG(GM)))], '3jca', '( %s -> %s )' % (A0, S1)),
                    w.s([rb0, w.s([w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), allu], 'jca', '( %s -> ( 1 e. RR /\\ %s ) )' % (A0, AL1)), gp0], 'jca',
                                  '( %s -> ( ( 1 e. RR /\\ %s ) /\\ ( %s ` P ) = 0 ) )' % (A0, AL1, GM))], 'jca', '( %s -> %s )' % (A0, S2))], 'jca', '( %s -> %s )' % (A0, sa)),
               w.inst('rectintschx')], 'syl', '( %s -> %s )' % (A0, sc))
    AQG = '( abs ` ( %s ` Q ) )' % GM
    ddr = w.s([w.s([qc, pc], 'subcld', '( %s -> ( Q - P ) e. CC )' % A0)], 'abscld', '( %s -> %s e. RR )' % (A0, DQ))
    ddc = w.s([ddr], 'recnd', '( %s -> %s e. CC )' % (A0, DQ))
    sch1 = w.s([sch, w.s([ddc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, DQ, DQ))], 'breqtrd', '( %s -> ( %s x. R ) <_ %s )' % (A0, AQG, DQ))
    gf = w.s([w.s([hgm, w.inst('simpl')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, GM)), w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (A0, GM))
    aqr = w.s([w.s([gf, qd], 'ffvelcdmd', '( %s -> ( %s ` Q ) e. CC )' % (A0, GM))], 'abscld', '( %s -> %s e. RR )' % (A0, AQG))
    T = '( %s / R )' % DQ
    tle = w.s([sch1, w.s([aqr, ddr, w.s([rr, rpos], 'jca', '( %s -> ( R e. RR /\\ 0 < R ) )' % A0), w.inst('lemuldiv')], 'syl3anc',
                         '( %s -> ( ( %s x. R ) <_ %s <-> %s <_ %s ) )' % (A0, AQG, DQ, AQG, T))], 'mpbid', '( %s -> %s <_ %s )' % (A0, AQG, T))
    gvq = gmval(A0, 'Q', qd)
    gle = w.s([w.s([w.s([gvq], 'eqcomd', '( %s -> %s = ( %s ` Q ) )' % (A0, GMV('Q'), GM))], 'fveq2d', '( %s -> ( abs ` %s ) = %s )' % (A0, GMV('Q'), AQG)), tle],
              'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, GMV('Q'), T))
    tr = w.s([ddr, rrp], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, T))
    rc = w.s([rr], 'recnd', '( %s -> R e. CC )' % A0)
    rne = w.s([rrp], 'rpne0d', '( %s -> R =/= 0 )' % A0)
    t1 = w.s([w.s([dqlt, w.s([ddr, rr, rrp], 'ltdiv1d', '( %s -> ( %s < R <-> %s < ( R / R ) ) )' % (A0, DQ, T))], 'mpbid', '( %s -> %s < ( R / R ) )' % (A0, T)),
              w.s([rc, rne], 'dividd', '( %s -> ( R / R ) = 1 )' % A0)], 'breqtrd', '( %s -> %s < 1 )' % (A0, T))
    subq = w.s([w.s([w.s([], 'fveq2', '( y = Q -> ( F ` y ) = ( F ` Q ) )')], 'fveq2d', '( y = Q -> ( Re ` ( F ` y ) ) = ( Re ` ( F ` Q ) ) )')], 'breq1d',
               '( y = Q -> ( ( Re ` ( F ` y ) ) <_ M <-> ( Re ` ( F ` Q ) ) <_ M ) )')
    req = w.s([subq, reh, qd], 'rspcdva', '( %s -> ( Re ` ( F ` Q ) ) <_ M )' % A0)
    X0 = '( ( ( 2 x. M ) x. %s ) / ( 1 - %s ) )' % (T, T)
    bci = w.s([w.s([fqc, mr], 'jca', '( %s -> ( ( F ` Q ) e. CC /\\ M e. RR ) )' % A0), w.s([mp_, req], 'jca', '( %s -> ( 0 < M /\\ ( Re ` ( F ` Q ) ) <_ M ) )' % A0),
               w.s([tr, t1, gle], '3jca', '( %s -> ( %s e. RR /\\ %s < 1 /\\ ( abs ` %s ) <_ %s ) )' % (A0, T, T, GMV('Q'), T)), w.inst('bcinv')], 'syl3anc',
              '( %s -> ( abs ` ( F ` Q ) ) <_ %s )' % (A0, X0))
    # X0 = BND
    tc = w.s([tr], 'recnd', '( %s -> %s e. CC )' % (A0, T))
    omt = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), tc], 'subcld', '( %s -> ( 1 - %s ) e. CC )' % (A0, T))
    omt0 = w.s([tr, w.s([], '1red', '( %s -> 1 e. RR )' % A0)], 'posdifd', '( %s -> ( %s < 1 <-> 0 < ( 1 - %s ) ) )' % (A0, T, T))
    omp = w.s([t1, omt0], 'mpbid', '( %s -> 0 < ( 1 - %s ) )' % (A0, T))
    omn = w.s([omp], 'gt0ne0d', '( %s -> ( 1 - %s ) =/= 0 )' % (A0, T))
    NUM = '( ( 2 x. M ) x. %s )' % T
    numc = w.s([m2c, tc], 'mulcld', '( %s -> %s e. CC )' % (A0, NUM))
    e1 = w.s([numc, omt, rc, omn, rne], 'divcan5rd', '( %s -> ( ( %s x. R ) / ( ( 1 - %s ) x. R ) ) = %s )' % (A0, NUM, T, X0))
    en = w.s([w.s([m2c, tc, rc], 'mulassd', '( %s -> ( %s x. R ) = ( ( 2 x. M ) x. ( %s x. R ) ) )' % (A0, NUM, T)),
              w.s([w.s([ddc, rc, rne], 'divcan1d', '( %s -> ( %s x. R ) = %s )' % (A0, T, DQ))], 'oveq2d', '( %s -> ( ( 2 x. M ) x. ( %s x. R ) ) = ( ( 2 x. M ) x. %s ) )' % (A0, T, DQ))],
             'eqtrd', '( %s -> ( %s x. R ) = ( ( 2 x. M ) x. %s ) )' % (A0, NUM, DQ))
    ed = w.s([w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), tc, rc], 'subdird', '( %s -> ( ( 1 - %s ) x. R ) = ( ( 1 x. R ) - ( %s x. R ) ) )' % (A0, T, T)),
              w.s([w.s([rc], 'mullidd', '( %s -> ( 1 x. R ) = R )' % A0), w.s([ddc, rc, rne], 'divcan1d', '( %s -> ( %s x. R ) = %s )' % (A0, T, DQ))], 'oveq12d',
                  '( %s -> ( ( 1 x. R ) - ( %s x. R ) ) = ( R - %s ) )' % (A0, T, DQ))], 'eqtrd', '( %s -> ( ( 1 - %s ) x. R ) = ( R - %s ) )' % (A0, T, DQ))
    e2 = w.s([en, ed], 'oveq12d', '( %s -> ( ( %s x. R ) / ( ( 1 - %s ) x. R ) ) = %s )' % (A0, NUM, T, BND))
    xeq = w.s([e1, e2], 'eqtr3d', '( %s -> %s = %s )' % (A0, X0, BND))
    w.qed([bci, xeq], 'breqtrd', '( %s -> ( abs ` ( F ` Q ) ) <_ %s )' % (A0, BND))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_rectintschx, gen_rectintbcx]:
        g()
