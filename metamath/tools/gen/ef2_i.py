"""Sortie EF2: one partial-fraction term of the strip integrand (ef2kph: y^z / ( z ( z - Q ) ) holomorphic off 0, Q;
ef2stk: its boundary integral over a rectangle, times a constant M, on any carrier E containing the frame)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
from z4blib import fvmd
import ef2_h
from ef2_h import CN0
import lin
lin.FASTPATH = True

DQ = '( %s \\ { Q } )' % CN0
KPO = KP('Q', DQ)
P10 = '( ( Re ` B ) + ( _i x. ( Im ` A ) ) )'
P01 = '( ( Re ` A ) + ( _i x. ( Im ` B ) ) )'
FRAB = '( ( ( A cseg %s ) u. ( %s cseg B ) ) u. ( ( B cseg %s ) u. ( %s cseg A ) ) )' % (P10, P10, P01, P01)
TMB = '( d e. E |-> ( M x. ( ( %s ` d ) / ( d - Q ) ) ) )' % PKF()
S['ef2kph'] = '( ( Y e. RR+ /\\ Q e. CC ) -> %s )' % HOLF(KPO, DQ)
INSQ = INS('Q', 'A', 'B')
S['ef2stk'] = ('( ( ( Y e. RR+ /\\ ( A e. CC /\\ B e. CC ) /\\ ( 0 < ( Re ` A ) /\\ ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) ) /\\ '
               '( ( M e. CC /\\ Q e. CC ) /\\ ( E C_ %s /\\ %s C_ E ) /\\ ( Q e. ( A crect B ) -> %s ) ) ) -> '
               '( %s rectint <. A , B >. ) = if ( %s , ( %s x. ( M x. ( ( Y ^c Q ) / Q ) ) ) , 0 ) )') % (DQ, FRAB, INSQ, TMB, INSQ, TPI)


def gen_kph():
    w = W('ef2kph', 'The mapping ` z |-> ( y ^ z / z ) / ( z - Q ) ` is holomorphic on ` CC ` minus ` 0 ` and ` Q ` .')
    A0, GC = ante_of(S['ef2kph'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yr = s([], 'simpl', 'Y e. RR+'); pc = s([], 'simpr', 'Q e. CC')
    K = '( TopOpen ` CCfld )'
    k_ = w.s([], 'eqid', '%s = %s' % (K, K))
    haus = s([w.s([k_], 'cnfldhaus', '%s e. Haus' % K)], 'a1i', '%s e. Haus' % K)
    scl = s([haus, pc, w.s([w.s([], 'unicntop', 'CC = U. %s' % K)], 'sncld', '( ( %s e. Haus /\\ Q e. CC ) -> { Q } e. ( Clsd ` %s ) )' % (K, K))], 'syl2anc', '{ Q } e. ( Clsd ` %s )' % K)
    dop = s([s([w.s([], 'cnn0opn', '%s e. %s' % (CN0, K))], 'a1i', '%s e. %s' % (CN0, K)), scl,
             w.s([w.s([], 'unicntop', 'CC = U. %s' % K)], 'difopn', '( ( %s e. %s /\\ { Q } e. ( Clsd ` %s ) ) -> %s e. %s )' % (CN0, K, K, DQ, K))], 'syl2anc', '%s e. %s' % (DQ, K))
    dss = s([w.s([], 'difss', '%s C_ %s' % (DQ, CN0))], 'a1i', '%s C_ %s' % (DQ, CN0))
    ph = s([yr, w.s([], 'pkfhol', '( Y e. RR+ -> %s )' % HOLF(PKF(), CN0))], 'syl', HOLF(PKF(), CN0))
    F1 = '( b e. %s |-> ( %s ` b ) )' % (DQ, PKF())
    G1 = '( b e. %s |-> ( b - Q ) )' % DQ
    f1 = s([s([ph, s([dop, dss], 'jca', '( %s e. %s /\\ %s C_ %s )' % (DQ, K, DQ, CN0))], 'jca', '( %s /\\ ( %s e. %s /\\ %s C_ %s ) )' % (HOLF(PKF(), CN0), DQ, K, DQ, CN0)),
            w.inst('zl2hres')], 'syl', HOLF(F1, DQ))
    g1 = s([s([pc, dop], 'jca', '( Q e. CC /\\ %s e. %s )' % (DQ, K)), w.s([], 'ef2hsub', '( ( Q e. CC /\\ %s e. %s ) -> %s )' % (DQ, K, HOLF(G1, DQ)))], 'syl', HOLF(G1, DQ))
    Av = '( %s /\\ v e. %s )' % (A0, DQ)
    sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    vd = sv([], 'simpr', 'v e. %s' % DQ)
    ev = sv([vd, w.s([], 'eldifsn', '( v e. %s <-> ( v e. %s /\\ v =/= Q ) )' % (DQ, CN0))], 'sylib', '( v e. %s /\\ v =/= Q )' % CN0)
    vcn = sv([ev, w.inst('simpl')], 'syl', 'v e. %s' % CN0)
    vc = sv([sv([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0), vcn], 'sseldd', 'v e. CC')
    vne = sv([ev, w.inst('simpr')], 'syl', 'v =/= Q')
    gv = fvmd(w, Av, 'b', DQ, '( b - Q )', 'v', vd, w.s([], 'ovexd', '( %s -> ( v - Q ) e. _V )' % Av))
    nz = sv([gv, sv([vc, up(w, pc, Av), vne], 'subne0d', '( v - Q ) =/= 0')], 'eqnetrd', '( %s ` v ) =/= 0' % G1)
    nza = w.s([nz], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) =/= 0 )' % (A0, DQ, G1))
    M1 = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (DQ, F1, G1)
    hd = s([f1, g1, nza, w.inst('holdiv')], 'syl3anc', HOLF(M1, DQ))
    Az = '( %s /\\ z e. %s )' % (A0, DQ)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zd = sz([], 'simpr', 'z e. %s' % DQ)
    fv1 = fvmd(w, Az, 'b', DQ, '( %s ` b )' % PKF(), 'z', zd, sz([w.s([], 'fvex', '( %s ` z ) e. _V' % PKF())], 'a1i', '( %s ` z ) e. _V' % PKF()))
    gv1 = fvmd(w, Az, 'b', DQ, '( b - Q )', 'z', zd, sz([], 'ovexd', '( z - Q ) e. _V'))
    eq = sz([fv1, gv1], 'oveq12d', '( ( %s ` z ) / ( %s ` z ) ) = ( ( %s ` z ) / ( z - Q ) )' % (F1, G1, PKF()))
    meq = s([eq], 'mpteq2dva', '%s = %s' % (M1, KPO))
    cs, _ = w.wcongr(HOLF(M1, DQ), {}, A0, {}, rules={M1: (KPO, meq)})
    w.qed([hd, cs], 'mpbid', S['ef2kph'])
    return run8(w)


def mlin(w, C, M, g, mc, gc):
    """( C -> ( ( ( M - 1 ) x. g ) + g ) = ( M x. g ) )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    one = s([], '1cnd', '1 e. CC')
    m1 = s([mc, one], 'subcld', '( %s - 1 ) e. CC' % M)
    a = s([s([s([gc], 'mullidd', '( 1 x. %s ) = %s' % (g, g))], 'eqcomd', '%s = ( 1 x. %s )' % (g, g))], 'oveq2d', '( ( ( %s - 1 ) x. %s ) + %s ) = ( ( ( %s - 1 ) x. %s ) + ( 1 x. %s ) )' % (M, g, g, M, g, g))
    b = s([s([m1, one, gc], 'adddird', '( ( ( %s - 1 ) + 1 ) x. %s ) = ( ( ( %s - 1 ) x. %s ) + ( 1 x. %s ) )' % (M, g, M, g, g))], 'eqcomd',
          '( ( ( %s - 1 ) x. %s ) + ( 1 x. %s ) ) = ( ( ( %s - 1 ) + 1 ) x. %s )' % (M, g, g, M, g))
    c = s([s([mc, one, w.inst('npcan')], 'syl2anc', '( ( %s - 1 ) + 1 ) = %s' % (M, M))], 'oveq1d', '( ( ( %s - 1 ) + 1 ) x. %s ) = ( %s x. %s )' % (M, g, M, g))
    return s([s([a, b], 'eqtrd', '( ( ( %s - 1 ) x. %s ) + %s ) = ( ( ( %s - 1 ) + 1 ) x. %s )' % (M, g, g, M, g)), c], 'eqtrd', '( ( ( %s - 1 ) x. %s ) + %s ) = ( %s x. %s )' % (M, g, g, M, g))


def gen_stk():
    w = W('ef2stk', 'One partial-fraction term of the strip integrand: the boundary integral of ` M y ^ s / ( s ( s - Q ) ) ` over a rectangle in the right half-plane is ` 2 pi i M y ^ Q / Q ` when ` Q ` is strictly inside and ` 0 ` when ` Q ` is outside ( ~ ef2pole , ~ ef2nopole ; any carrier ` E ` containing the frame).')
    A0, GC = ante_of(S['ef2stk'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2 = top_and(A0)
    x1 = s([], 'simpl', X1); x2 = s([], 'simpr', X2)
    P1, P2, P3 = top_and(X1)
    yr = s([x1, w.inst('simp1')], 'syl', P1); ab = s([x1, w.inst('simp2')], 'syl', P2); geo = s([x1, w.inst('simp3')], 'syl', P3)
    a0 = s([geo, w.inst('simp1')], 'syl', '0 < ( Re ` A )')
    Q1, Q2, Q3 = top_and(X2)
    q1 = s([x2, w.inst('simp1')], 'syl', Q1); q2 = s([x2, w.inst('simp2')], 'syl', Q2); q3 = s([x2, w.inst('simp3')], 'syl', Q3)
    mc = s([q1, w.inst('simpl')], 'syl', 'M e. CC'); qc = s([q1, w.inst('simpr')], 'syl', 'Q e. CC')
    edq = s([q2, w.inst('simpl')], 'syl', 'E C_ %s' % DQ); fre = s([q2, w.inst('simpr')], 'syl', '%s C_ E' % FRAB)
    hk = s([yr, qc, w.inst('ef2kph')], 'syl2anc', HOLF(KPO, DQ))
    kcn = s([hk, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (KPO, DQ))
    G = '( %s |` E )' % KPO
    gcn = s([edq, kcn, w.inst('rescncf')], 'sylc', '%s e. ( E -cn-> CC )' % G)
    pkh = s([yr, w.s([], 'pkfhol', '( Y e. RR+ -> %s )' % HOLF(PKF(), CN0))], 'syl', HOLF(PKF(), CN0))
    pkf = s([s([pkh, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (PKF(), CN0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (PKF(), CN0))
    cn0x = w.s([w.s([], 'cnex', 'CC e. _V')], 'difexi', '%s e. _V' % CN0)
    dqx = w.s([cn0x], 'difexi', '%s e. _V' % DQ)
    kex = s([w.s([dqx], 'mptex', '%s e. _V' % KPO)], 'a1i', '%s e. _V' % KPO)
    ecc = s([edq, s([s([w.s([], 'difss', '%s C_ %s' % (DQ, CN0))], 'a1i', '%s C_ %s' % (DQ, CN0)), s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)], 'sstrd', '%s C_ CC' % DQ)],
            'sstrd', 'E C_ CC')
    eex = s([s([w.s([], 'cnex', 'CC e. _V')], 'a1i', 'CC e. _V'), ecc], 'ssexd', 'E e. _V')
    tex = s([eex, w.inst('mptexg')], 'syl', '%s e. _V' % TMB)
    gex = s([kex, w.inst('resexg')], 'syl', '%s e. _V' % G)
    # pointwise
    Au = '( %s /\\ u e. E )' % A0
    su = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Au, f))
    ue = su([], 'simpr', 'u e. E')
    ud = su([up(w, edq, Au), ue], 'sseldd', 'u e. %s' % DQ)
    ev = su([ud, w.s([], 'eldifsn', '( u e. %s <-> ( u e. %s /\\ u =/= Q ) )' % (DQ, CN0))], 'sylib', '( u e. %s /\\ u =/= Q )' % CN0)
    ucn = su([ev, w.inst('simpl')], 'syl', 'u e. %s' % CN0)
    uc = su([su([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0), ucn], 'sseldd', 'u e. CC')
    une = su([ev, w.inst('simpr')], 'syl', 'u =/= Q')
    PU = '( %s ` u )' % PKF()
    gu = '( %s / ( u - Q ) )' % PU
    pkc = su([up(w, pkf, Au), ucn], 'ffvelcdmd', '%s e. CC' % PU)
    guc = su([pkc, su([uc, up(w, qc, Au)], 'subcld', '( u - Q ) e. CC'), su([uc, up(w, qc, Au), une], 'subne0d', '( u - Q ) =/= 0')], 'divcld', '%s e. CC' % gu)
    tv = fvmd(w, Au, 'd', 'E', '( M x. ( ( %s ` d ) / ( d - Q ) ) )' % PKF(), 'u', ue, w.s([], 'ovexd', '( %s -> ( M x. %s ) e. _V )' % (Au, gu)))
    gres = su([ue, w.inst('fvres')], 'syl', '( %s ` u ) = ( %s ` u )' % (G, KPO))
    kv = fvmd(w, Au, 'z', DQ, '( ( %s ` z ) / ( z - Q ) )' % PKF(), 'u', ud, w.s([], 'ovexd', '( %s -> %s e. _V )' % (Au, gu)))
    gv = su([gres, kv], 'eqtrd', '( %s ` u ) = %s' % (G, gu))
    ml = mlin(w, Au, 'M', gu, up(w, mc, Au), guc)
    rhs = su([su([su([gv], 'oveq2d', '( ( M - 1 ) x. ( %s ` u ) ) = ( ( M - 1 ) x. %s )' % (G, gu)), gv], 'oveq12d',
                 '( ( ( M - 1 ) x. ( %s ` u ) ) + ( %s ` u ) ) = ( ( ( M - 1 ) x. %s ) + %s )' % (G, G, gu, gu)), ml], 'eqtrd', '( ( ( M - 1 ) x. ( %s ` u ) ) + ( %s ` u ) ) = ( M x. %s )' % (G, G, gu))
    pt = su([tv, rhs], 'eqtr4d', '( %s ` u ) = ( ( ( M - 1 ) x. ( %s ` u ) ) + ( %s ` u ) )' % (TMB, G, G))
    allp = w.s([pt], 'ralrimiva', '( %s -> A. u e. E ( %s ` u ) = ( ( ( M - 1 ) x. ( %s ` u ) ) + ( %s ` u ) ) )' % (A0, TMB, G, G))
    LC = tsub(stmt('rectintlce'), {'F': TMB, 'C': '( M - 1 )', 'G': G, 'H': G, 'D': 'E', 'V': '_V'})
    la, lc = ante_of(LC)
    m1c = s([mc, s([], '1cnd', '1 e. CC')], 'subcld', '( M - 1 ) e. CC')
    have = {'( A e. CC /\\ B e. CC )': ab, '%s C_ E' % FRAB: fre, '%s e. _V' % TMB: tex,
            '( M - 1 ) e. CC': m1c, '%s e. ( E -cn-> CC )' % G: gcn, 'E C_ E': s([w.s([], 'ssid', 'E C_ E')], 'a1i', 'E C_ E'), body_of(w, allp): allp}
    lce = s([conj(w, A0, la, have), w.inst('rectintlce')], 'syl', lc)
    IG = '( %s rectint <. A , B >. )' % G
    IK = '( %s rectint <. A , B >. )' % KPO
    EQ = tsub(stmt('rectinteqe'), {'F': G, 'G': KPO, 'V': '_V'})
    ea, ec = ante_of(EQ)
    gk = w.s([gres], 'ralrimiva', '( %s -> A. u e. E ( %s ` u ) = ( %s ` u ) )' % (A0, G, KPO))
    have2 = {'( A e. CC /\\ B e. CC )': ab, '%s C_ E' % FRAB: fre, '%s e. _V' % G: gex, '%s e. _V' % KPO: kex, body_of(w, gk): gk}
    igk = s([conj(w, A0, ea, have2), w.inst('rectinteqe')], 'syl', ec)
    # ( M - 1 ) I + I = M I
    Ci = '( %s /\\ %s )' % (A0, INSQ)
    Cn = '( %s /\\ -. %s )' % (A0, INSQ)
    outs = []
    for C, case in ((Ci, 1), (Cn, 0)):
        sc = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
        if case:
            RB = '( ( A crect B ) \\ { Q } )'
            KR = KP('Q', RB)
            PO = tsub(S['ef2pole'], {'P': 'Q'})
            pa, pc_ = ante_of(PO)
            ins = sc([], 'simpr', INSQ)
            hv = {'Y e. RR+': up(w, yr, C), '( A e. CC /\\ B e. CC )': up(w, ab, C), '0 < ( Re ` A )': up(w, a0, C), 'Q e. CC': up(w, qc, C), INSQ: ins}
            pole = sc([conj(w, C, pa, hv), w.inst('ef2pole')], 'syl', pc_)
            # KPO and KR agree off Q on the rectangle
            Cv = '( %s /\\ u e. %s )' % (C, RB)
            sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Cv, f))
            urb = sv([], 'simpr', 'u e. %s' % RB)
            e2 = sv([urb, w.s([], 'eldifsn', '( u e. %s <-> ( u e. ( A crect B ) /\\ u =/= Q ) )' % RB)], 'sylib', '( u e. ( A crect B ) /\\ u =/= Q )')
            rh = sv([sv([up(w, ab, Cv), up(w, a0, Cv)], 'jca', '( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) )'), w.inst('ef2rhp')], 'syl', '( ( A crect B ) C_ %s /\\ ( A crect B ) C_ %s )' % (HP0, CN0))
            ucn2 = sv([sv([rh, w.inst('simpr')], 'syl', '( A crect B ) C_ %s' % CN0), sv([e2, w.inst('simpl')], 'syl', 'u e. ( A crect B )')], 'sseldd', 'u e. %s' % CN0)
            udq = sv([sv([ucn2, sv([e2, w.inst('simpr')], 'syl', 'u =/= Q')], 'jca', '( u e. %s /\\ u =/= Q )' % CN0), w.s([], 'eldifsn', '( u e. %s <-> ( u e. %s /\\ u =/= Q ) )' % (DQ, CN0))], 'sylibr', 'u e. %s' % DQ)
            v1 = fvmd(w, Cv, 'z', DQ, '( ( %s ` z ) / ( z - Q ) )' % PKF(), 'u', udq, w.s([], 'ovexd', '( %s -> %s e. _V )' % (Cv, gu)))
            v2 = fvmd(w, Cv, 'z', RB, '( ( %s ` z ) / ( z - Q ) )' % PKF(), 'u', urb, w.s([], 'ovexd', '( %s -> %s e. _V )' % (Cv, gu)))
            kk = w.s([sv([v1, v2], 'eqtr4d', '( %s ` u ) = ( %s ` u )' % (KPO, KR))], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (C, RB, KPO, KR))
            EP = tsub(stmt('rectinteqp'), {'F': KPO, 'G': KR, 'P': 'Q', 'V': '_V'})
            epa, epc = ante_of(EP)
            hv2 = dict(hv); hv2['%s e. _V' % KPO] = up(w, kex, C); hv2['%s e. _V' % KR] = sc([w.s([w.s([w.s([], 'ovex', '( A crect B ) e. _V')], 'difexi', '%s e. _V' % RB)], 'mptex', '%s e. _V' % KR)], 'a1i', '%s e. _V' % KR); hv2[body_of(w, kk)] = kk
            ikr = sc([conj(w, C, epa, hv2), w.inst('rectinteqp')], 'syl', epc)
            ival = sc([ikr, pole], 'eqtrd', '%s = ( %s x. ( ( Y ^c Q ) / Q ) )' % (IK, TPI))
            V = '( %s x. ( ( Y ^c Q ) / Q ) )' % TPI
            RES = '( %s x. ( M x. ( ( Y ^c Q ) / Q ) ) )' % TPI
        else:
            npi = sc([up(w, q3, C), sc([], 'simpr', '-. %s' % INSQ)], 'mtod', '-. Q e. ( A crect B )')
            NP = tsub(S['ef2nopole'], {'P': 'Q'})
            na, nc = ante_of(NP)
            hv = {'Y e. RR+': up(w, yr, C), '( A e. CC /\\ B e. CC )': up(w, ab, C), body_of(w, geo): up(w, geo, C), 'Q e. CC': up(w, qc, C), '-. Q e. ( A crect B )': npi}
            ival = sc([conj(w, C, na, hv), w.inst('ef2nopole')], 'syl', nc)
            V = '0'
            RES = '0'
        # assemble: TMB integral = ( M - 1 ) IG + IG, IG = IK = V
        igv = sc([up(w, igk, C), ival], 'eqtrd', '%s = %s' % (IG, V))
        ITM = '( %s rectint <. A , B >. )' % TMB
        l1 = sc([up(w, lce, C), sc([sc([igv], 'oveq2d', '( ( M - 1 ) x. %s ) = ( ( M - 1 ) x. %s )' % (IG, V)), igv], 'oveq12d',
                                  '( ( ( M - 1 ) x. %s ) + %s ) = ( ( ( M - 1 ) x. %s ) + %s )' % (IG, IG, V, V))], 'eqtrd', '%s = ( ( ( M - 1 ) x. %s ) + %s )' % (ITM, V, V))
        if case:
            qin = sc([up(w, ab, C), sc([up(w, qc, C), ins], 'jca', '( Q e. CC /\\ %s )' % INSQ), w.inst('crectinp')], 'syl2anc', 'Q e. ( A crect B )')
            rh = sc([sc([up(w, ab, C), up(w, a0, C)], 'jca', '( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) )'), w.inst('ef2rhp')], 'syl', '( ( A crect B ) C_ %s /\\ ( A crect B ) C_ %s )' % (HP0, CN0))
            qcn = sc([sc([rh, w.inst('simpr')], 'syl', '( A crect B ) C_ %s' % CN0), qin], 'sseldd', 'Q e. %s' % CN0)
            qn0 = sc([sc([qcn, w.s([], 'eldifsn', '( Q e. %s <-> ( Q e. CC /\\ Q =/= 0 ) )' % CN0)], 'sylib', '( Q e. CC /\\ Q =/= 0 )'), w.inst('simpr')], 'syl', 'Q =/= 0')
            yq = sc([sc([sc([up(w, yr, C)], 'rpcnd', 'Y e. CC'), up(w, qc, C)], 'cxpcld', '( Y ^c Q ) e. CC'), up(w, qc, C), qn0], 'divcld', '( ( Y ^c Q ) / Q ) e. CC')
            tc = sc([sc([], '2cnd', '2 e. CC'), sc([sc([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), sc([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')],
                    'mulcld', '%s e. CC' % TPI)
            vcc = sc([tc, yq], 'mulcld', '%s e. CC' % V)
            l2 = sc([l1, mlin(w, C, 'M', V, up(w, mc, C), vcc)], 'eqtrd', '%s = ( M x. %s )' % (ITM, V))
            l3 = sc([l2, sc([up(w, mc, C), tc, yq], 'mul12d', '( M x. %s ) = %s' % (V, RES))], 'eqtrd', '%s = %s' % (ITM, RES))
            outs.append(sc([l3, sc([ins], 'iftrued', 'if ( %s , %s , 0 ) = %s' % (INSQ, RES, RES))], 'eqtr4d', GC))
        else:
            z1 = sc([sc([up(w, m1c, C)], 'mul01d', '( ( M - 1 ) x. 0 ) = 0')], 'oveq1d', '( ( ( M - 1 ) x. 0 ) + 0 ) = ( 0 + 0 )')
            z2 = sc([z1, sc([w.s([], '00id', '( 0 + 0 ) = 0')], 'a1i', '( 0 + 0 ) = 0')], 'eqtrd', '( ( ( M - 1 ) x. 0 ) + 0 ) = 0')
            l3 = sc([l1, z2], 'eqtrd', '%s = 0' % ITM)
            outs.append(sc([l3, sc([sc([], 'simpr', '-. %s' % INSQ)], 'iffalsed', 'if ( %s , %s , 0 ) = 0' % (INSQ, '( %s x. ( M x. ( ( Y ^c Q ) / Q ) ) )' % TPI))], 'eqtr4d', GC))
    w.qed(outs, 'pm2.61dan', S['ef2stk'])
    return run8(w)


S['ef2tmc'] = '( ( Y e. RR+ /\\ ( M e. CC /\\ Q e. CC ) /\\ E C_ %s ) -> %s e. ( E -cn-> CC ) )' % (DQ, TMB)


def gen_tmc():
    w = W('ef2tmc', 'The term ` M y ^ z / ( z ( z - Q ) ) ` is continuous on every set avoiding ` 0 ` and ` Q ` .')
    A0, GC = ante_of(S['ef2tmc'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yr = s([], 'simp1', 'Y e. RR+'); mq = s([], 'simp2', '( M e. CC /\\ Q e. CC )'); edq = s([], 'simp3', 'E C_ %s' % DQ)
    mc = s([mq, w.inst('simpl')], 'syl', 'M e. CC'); qc = s([mq, w.inst('simpr')], 'syl', 'Q e. CC')
    kcn = s([s([yr, qc, w.inst('ef2kph')], 'syl2anc', HOLF(KPO, DQ)), w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (KPO, DQ))
    rc = s([edq, kcn, w.inst('rescncf')], 'sylc', '( %s |` E ) e. ( E -cn-> CC )' % KPO)
    BZ = '( ( %s ` z ) / ( z - Q ) )' % PKF()
    BD = '( ( %s ` d ) / ( d - Q ) )' % PKF()
    rm = s([edq, w.inst('resmpt')], 'syl', '( %s |` E ) = ( z e. E |-> %s )' % (KPO, BZ))
    idd = w.s([], 'id', '( z = d -> z = d )')
    cz, _ = w.congr(BZ, {'z': 'd'}, 'z = d', {'z': idd})
    cb = s([w.s([cz], 'cbvmptv', '( z e. E |-> %s ) = ( d e. E |-> %s )' % (BZ, BD))], 'a1i', '( z e. E |-> %s ) = ( d e. E |-> %s )' % (BZ, BD))
    kd = s([s([rm, cb], 'eqtrd', '( %s |` E ) = ( d e. E |-> %s )' % (KPO, BD)), rc], 'eqeltrrd', '( d e. E |-> %s ) e. ( E -cn-> CC )' % BD)
    ecc = s([edq, s([s([w.s([], 'difss', '%s C_ %s' % (DQ, CN0))], 'a1i', '%s C_ %s' % (DQ, CN0)), s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)], 'sstrd', '%s C_ CC' % DQ)],
            'sstrd', 'E C_ CC')
    mcn = s([mc, ecc, s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( d e. E |-> M ) e. ( E -cn-> CC )')
    w.qed([mcn, kd], 'mulcncf', S['ef2tmc'])
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2kph', 'ef2stk', 'ef2tmc']:
        {'ef2kph': gen_kph, 'ef2stk': gen_stk, 'ef2tmc': gen_tmc}[g]()
