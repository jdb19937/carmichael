"""Sortie TP: the kernel ( 1 / z ) ^ Y on rectangles in the right half-plane (tpfh holomorphy; tppole, tpnopole,
tpkph, tpstk, tptmc: EF2's ef2pole ... ef2tmc with the kernel ( 1 / z ) ^ Y in place of y ^ z / z)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin
import ef2lib as E
from z4blib import fvmd

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


HOLF = E.HOLF
INS = E.INS
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt
TPI = '( 2 x. ( _i x. _pi ) )'
CN0 = '( CC \\ { 0 } )'
HP0 = E.HP0
FY = '( o e. %s |-> ( ( 1 / o ) ^ Y ) )' % CN0


def KP(P, D):
    return '( z e. %s |-> ( ( %s ` z ) / ( z - %s ) ) )' % (D, FY, P)


S['tpfh'] = '( Y e. NN -> %s )' % HOLF(FY, CN0)


def gen_fh():
    w = W('tpfh', 'The kernel ` z |-> ( 1 / z ) ^ Y ` is holomorphic on ` CC \\ { 0 } ` .')
    A0 = 'Y e. NN'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yn = w.s([], 'id', '( Y e. NN -> Y e. NN )')
    H = '( x e. %s |-> ( 1 / x ) )' % CN0
    dr = s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('dvrec')], 'ax-mp', '( CC _D %s ) = ( x e. %s |-> -u ( 1 / ( x ^ 2 ) ) )' % (H, CN0))], 'a1i',
           '( CC _D %s ) = ( x e. %s |-> -u ( 1 / ( x ^ 2 ) ) )' % (H, CN0))
    Ax = '( %s /\\ x e. %s )' % (A0, CN0)
    sx = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ax, f))
    xd = sx([], 'simpr', 'x e. %s' % CN0)
    ex = sx([xd, w.s([], 'eldifsn', '( x e. %s <-> ( x e. CC /\\ x =/= 0 ) )' % CN0)], 'sylib', '( x e. CC /\\ x =/= 0 )')
    xc = sx([ex, w.inst('simpl')], 'syl', 'x e. CC'); xn = sx([ex, w.inst('simpr')], 'syl', 'x =/= 0')
    cx = Closure(w, Ax, {'x': ('CC', xc)}); cx.have('x', 'ne0', xn)
    cx.have('( x ^ 2 )', 'ne0', ap(w, Ax, 'expne0d', '( x ^ 2 ) =/= 0', cx, facts=[sx([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')]))
    dv = cx.mem('-u ( 1 / ( x ^ 2 ) )', 'CC')
    dm0 = s([w.s([dv], 'ralrimiva', '( %s -> A. x e. %s -u ( 1 / ( x ^ 2 ) ) e. CC )' % (A0, CN0)), w.inst('dmmptg')], 'syl',
            'dom ( x e. %s |-> -u ( 1 / ( x ^ 2 ) ) ) = %s' % (CN0, CN0))
    dm = s([s([dr], 'dmeqd', 'dom ( CC _D %s ) = dom ( x e. %s |-> -u ( 1 / ( x ^ 2 ) ) )' % (H, CN0)), dm0], 'eqtrd', 'dom ( CC _D %s ) = %s' % (H, CN0))
    hf = s([cx.mem('( 1 / x )', 'CC')], 'fmptd', '%s : %s --> CC' % (H, CN0))
    ss = s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC')
    cs = s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)
    hcn = s([s([ss, hf, cs], '3jca', '( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC )' % (H, CN0, CN0)), dm, w.inst('dvcn')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (H, CN0))
    dms = s([s([dm], 'eqcomd', '%s = dom ( CC _D %s )' % (CN0, H))], 'eqimssd', '%s C_ dom ( CC _D %s )' % (CN0, H))
    hh = s([hcn, dms], 'jca', HOLF(H, CN0))
    M1 = '( z e. %s |-> ( ( %s ` z ) ^ Y ) )' % (CN0, H)
    he = s([hh, yn, w.inst('holexp')], 'syl2anc', HOLF(M1, CN0))
    Az = '( %s /\\ z e. %s )' % (A0, CN0)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zd = sz([], 'simpr', 'z e. %s' % CN0)
    ez = sz([zd, w.s([], 'eldifsn', '( z e. %s <-> ( z e. CC /\\ z =/= 0 ) )' % CN0)], 'sylib', '( z e. CC /\\ z =/= 0 )')
    cz = Closure(w, Az, {'z': ('CC', sz([ez, w.inst('simpl')], 'syl', 'z e. CC'))}); cz.have('z', 'ne0', sz([ez, w.inst('simpr')], 'syl', 'z =/= 0'))
    hv = fvmd(w, Az, 'x', CN0, '( 1 / x )', 'z', zd, cz.mem('( 1 / z )', 'CC'))
    eq = sz([hv], 'oveq1d', '( ( %s ` z ) ^ Y ) = ( ( 1 / z ) ^ Y )' % H)
    M2 = '( z e. %s |-> ( ( 1 / z ) ^ Y ) )' % CN0
    m12 = s([eq], 'mpteq2dva', '%s = %s' % (M1, M2))
    idz = w.s([], 'id', '( z = o -> z = o )')
    czo, _ = w.congr('( ( 1 / z ) ^ Y )', {'z': 'o'}, 'z = o', {'z': idz})
    m2y = s([w.s([czo], 'cbvmptv', '%s = %s' % (M2, FY))], 'a1i', '%s = %s' % (M2, FY))
    mm = s([m12, m2y], 'eqtrd', '%s = %s' % (M1, FY))
    csw, _ = w.wcongr(HOLF(M1, CN0), {}, A0, {}, rules={M1: (FY, mm)})
    w.qed([he, csw], 'mpbid', S['tpfh'])
    return run(w)


# ---- EF2's single-term residue calculus with the kernel ( 1 / z ) ^ Y (code transcribed from tools/gen/ef2_h.py, ef2_i.py)
from ef2lib import crect_bounds
up = E.up
DQ = '( %s \\ { Q } )' % CN0
KPO = KP('Q', DQ)
P10 = '( ( Re ` B ) + ( _i x. ( Im ` A ) ) )'
P01 = '( ( Re ` A ) + ( _i x. ( Im ` B ) ) )'
FRAB = '( ( ( A cseg %s ) u. ( %s cseg B ) ) u. ( ( B cseg %s ) u. ( %s cseg A ) ) )' % (P10, P10, P01, P01)
TMB = '( d e. E |-> ( M x. ( ( %s ` d ) / ( d - Q ) ) ) )' % FY
INSQ = INS('Q', 'A', 'B')
S['tppole'] = '( ( Y e. NN /\\ ( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) ) /\\ ( P e. CC /\\ ( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) ) ) ) -> ( ( z e. ( ( A crect B ) \\ { P } ) |-> ( ( ( o e. ( CC \\ { 0 } ) |-> ( ( 1 / o ) ^ Y ) ) ` z ) / ( z - P ) ) ) rectint <. A , B >. ) = ( ( 2 x. ( _i x. _pi ) ) x. ( ( 1 / P ) ^ Y ) ) )'
S['tpnopole'] = '( ( Y e. NN /\\ ( ( A e. CC /\\ B e. CC ) /\\ ( 0 < ( Re ` A ) /\\ ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) ) /\\ ( P e. CC /\\ -. P e. ( A crect B ) ) ) -> ( ( z e. ( ( CC \\ { 0 } ) \\ { P } ) |-> ( ( ( o e. ( CC \\ { 0 } ) |-> ( ( 1 / o ) ^ Y ) ) ` z ) / ( z - P ) ) ) rectint <. A , B >. ) = 0 )'
S['tpkph'] = '( ( Y e. NN /\\ Q e. CC ) -> ( ( z e. ( ( CC \\ { 0 } ) \\ { Q } ) |-> ( ( ( o e. ( CC \\ { 0 } ) |-> ( ( 1 / o ) ^ Y ) ) ` z ) / ( z - Q ) ) ) e. ( ( ( CC \\ { 0 } ) \\ { Q } ) -cn-> CC ) /\\ ( ( CC \\ { 0 } ) \\ { Q } ) C_ dom ( CC _D ( z e. ( ( CC \\ { 0 } ) \\ { Q } ) |-> ( ( ( o e. ( CC \\ { 0 } ) |-> ( ( 1 / o ) ^ Y ) ) ` z ) / ( z - Q ) ) ) ) ) )'
S['tpstk'] = '( ( ( Y e. NN /\\ ( A e. CC /\\ B e. CC ) /\\ ( 0 < ( Re ` A ) /\\ ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) ) /\\ ( ( M e. CC /\\ Q e. CC ) /\\ ( E C_ ( ( CC \\ { 0 } ) \\ { Q } ) /\\ ( ( ( A cseg ( ( Re ` B ) + ( _i x. ( Im ` A ) ) ) ) u. ( ( ( Re ` B ) + ( _i x. ( Im ` A ) ) ) cseg B ) ) u. ( ( B cseg ( ( Re ` A ) + ( _i x. ( Im ` B ) ) ) ) u. ( ( ( Re ` A ) + ( _i x. ( Im ` B ) ) ) cseg A ) ) ) C_ E ) /\\ ( Q e. ( A crect B ) -> ( ( ( Re ` A ) < ( Re ` Q ) /\\ ( Re ` Q ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` Q ) /\\ ( Im ` Q ) < ( Im ` B ) ) ) ) ) ) -> ( ( d e. E |-> ( M x. ( ( ( o e. ( CC \\ { 0 } ) |-> ( ( 1 / o ) ^ Y ) ) ` d ) / ( d - Q ) ) ) ) rectint <. A , B >. ) = if ( ( ( ( Re ` A ) < ( Re ` Q ) /\\ ( Re ` Q ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` Q ) /\\ ( Im ` Q ) < ( Im ` B ) ) ) , ( ( 2 x. ( _i x. _pi ) ) x. ( M x. ( ( 1 / Q ) ^ Y ) ) ) , 0 ) )'
S['tptmc'] = '( ( Y e. NN /\\ ( M e. CC /\\ Q e. CC ) /\\ E C_ ( ( CC \\ { 0 } ) \\ { Q } ) ) -> ( d e. E |-> ( M x. ( ( ( o e. ( CC \\ { 0 } ) |-> ( ( 1 / o ) ^ Y ) ) ` d ) / ( d - Q ) ) ) ) e. ( E -cn-> CC ) )'


def gen_pole():
    w = W('tppole', 'For ` P ` strictly inside a rectangle in the right half-plane, the boundary integral of ` ( 1 / z ) ^ Y / ( z - P ) ` is ` 2 pi i ( 1 / P ) ^ Y ` (C0c ~ rectintcau at ~ tpfh ; EF2 ~ ef2pole with this kernel).')
    A0, GC = ante_of(S['tppole'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yr = s([], 'simp1', 'Y e. NN')
    X2 = '( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) )'
    x2 = s([], 'simp2', X2)
    X3 = '( P e. CC /\\ %s )' % INS('P', 'A', 'B')
    x3 = s([], 'simp3', X3)
    ab = s([x2, w.inst('simpl')], 'syl', '( A e. CC /\\ B e. CC )')
    rh = s([x2, w.inst('ef2rhp')], 'syl', '( ( A crect B ) C_ %s /\\ ( A crect B ) C_ %s )' % (HP0, CN0))
    rcn = s([rh, w.inst('simpr')], 'syl', '( A crect B ) C_ %s' % CN0)
    ph = s([yr, w.s([], 'tpfh', '( Y e. NN -> %s )' % HOLF(FY, CN0))], 'syl', HOLF(FY, CN0))
    hc = s([s([ph, rcn], 'jca', '( %s /\\ ( A crect B ) C_ %s )' % (HOLF(FY, CN0), CN0)), w.inst('holcrect')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) )' % (FY, CN0, FY))
    RC = tsub(stmt('rectintcau'), {'F': FY, 'D': CN0})
    ra, rc = ante_of(RC)
    cau = s([conj(w, A0, ra, {'( A e. CC /\\ B e. CC )': ab, X3: x3, body_of(w, hc): hc}), w.inst('rectintcau')], 'syl', rc)
    pin = s([ab, x3, w.inst('crectinp')], 'syl2anc', 'P e. ( A crect B )')
    pn = s([rcn, pin], 'sseldd', 'P e. %s' % CN0)
    pv = fvmd(w, A0, 'o', CN0, '( ( 1 / o ) ^ Y )', 'P', pn, w.s([], 'ovexd', '( %s -> ( ( 1 / P ) ^ Y ) e. _V )' % A0))
    w.qed([cau, s([pv], 'oveq2d', '( %s x. ( %s ` P ) ) = ( %s x. ( ( 1 / P ) ^ Y ) )' % (TPI, FY, TPI))], 'eqtrd', S['tppole'])
    return run(w)


def gen_nopole():
    w = W('tpnopole', 'For ` P ` outside a closed rectangle in the right half-plane, the boundary integral of ` ( 1 / z ) ^ Y / ( z - P ) ` vanishes (C0b ~ rectintgour ; EF2 ~ ef2nopole with this kernel).')
    A0, GC = ante_of(S['tpnopole'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2, X3 = top_and(A0)
    yr = s([], 'simp1', X1); x2 = s([], 'simp2', X2); x3 = s([], 'simp3', X3)
    ab = s([x2, w.inst('simpl')], 'syl', '( A e. CC /\\ B e. CC )')
    G3 = s([x2, w.inst('simpr')], 'syl', top_and(X2)[1])
    a0 = s([G3, w.inst('simp1')], 'syl', '0 < ( Re ` A )')
    pc = s([x3, w.inst('simpl')], 'syl', 'P e. CC'); pn = s([x3, w.inst('simpr')], 'syl', '-. P e. ( A crect B )')
    DP = '( %s \\ { P } )' % CN0
    K = '( TopOpen ` CCfld )'
    k_ = w.s([], 'eqid', '%s = %s' % (K, K))
    haus = s([w.s([k_], 'cnfldhaus', '%s e. Haus' % K)], 'a1i', '%s e. Haus' % K)
    scl = s([haus, pc, w.s([w.s([], 'unicntop', 'CC = U. %s' % K)], 'sncld', '( ( %s e. Haus /\\ P e. CC ) -> { P } e. ( Clsd ` %s ) )' % (K, K))], 'syl2anc', '{ P } e. ( Clsd ` %s )' % K)
    dop = s([s([w.s([], 'cnn0opn', '%s e. %s' % (CN0, K))], 'a1i', '%s e. %s' % (CN0, K)), scl, w.s([w.s([], 'unicntop', 'CC = U. %s' % K)], 'difopn', '( ( %s e. %s /\\ { P } e. ( Clsd ` %s ) ) -> %s e. %s )' % (CN0, K, K, DP, K))], 'syl2anc', '%s e. %s' % (DP, K))
    dss = s([w.s([], 'difss', '%s C_ %s' % (DP, CN0))], 'a1i', '%s C_ %s' % (DP, CN0))
    ph = s([yr, w.s([], 'tpfh', '( Y e. NN -> %s )' % HOLF(FY, CN0))], 'syl', HOLF(FY, CN0))
    F1 = '( b e. %s |-> ( %s ` b ) )' % (DP, FY)
    G1 = '( b e. %s |-> ( b - P ) )' % DP
    f1 = s([s([ph, s([dop, dss], 'jca', '( %s e. %s /\\ %s C_ %s )' % (DP, K, DP, CN0))], 'jca', '( %s /\\ ( %s e. %s /\\ %s C_ %s ) )' % (HOLF(FY, CN0), DP, K, DP, CN0)), w.inst('zl2hres')],
           'syl', HOLF(F1, DP))
    g1 = s([s([pc, dop], 'jca', '( P e. CC /\\ %s e. %s )' % (DP, K)), w.inst('ef2hsub')], 'syl', HOLF(G1, DP))
    Av = '( %s /\\ v e. %s )' % (A0, DP)
    sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    vd = sv([], 'simpr', 'v e. %s' % DP)
    ev = sv([vd, w.s([], 'eldifsn', '( v e. %s <-> ( v e. %s /\\ v =/= P ) )' % (DP, CN0))], 'sylib', '( v e. %s /\\ v =/= P )' % CN0)
    vcn = sv([ev, w.inst('simpl')], 'syl', 'v e. %s' % CN0)
    vc = sv([sv([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0), vcn], 'sseldd', 'v e. CC')
    vne = sv([ev, w.inst('simpr')], 'syl', 'v =/= P')
    gv = fvmd(w, Av, 'b', DP, '( b - P )', 'v', vd, w.s([], 'ovexd', '( %s -> ( v - P ) e. _V )' % Av))
    nz = sv([gv, sv([vc, up(w, pc, Av), vne], 'subne0d', '( v - P ) =/= 0')], 'eqnetrd', '( %s ` v ) =/= 0' % G1)
    nza = w.s([nz], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) =/= 0 )' % (A0, DP, G1))
    M1 = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (DP, F1, G1)
    hd = s([f1, g1, nza, w.inst('holdiv')], 'syl3anc', HOLF(M1, DP))
    KPD = KP('P', DP)
    Az = '( %s /\\ z e. %s )' % (A0, DP)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zd = sz([], 'simpr', 'z e. %s' % DP)
    fv1 = fvmd(w, Az, 'b', DP, '( %s ` b )' % FY, 'z', zd, sz([w.s([], 'fvex', '( %s ` z ) e. _V' % FY)], 'a1i', '( %s ` z ) e. _V' % FY))
    gv1 = fvmd(w, Az, 'b', DP, '( b - P )', 'z', zd, sz([], 'ovexd', '( z - P ) e. _V'))
    eq = sz([fv1, gv1], 'oveq12d', '( ( %s ` z ) / ( %s ` z ) ) = ( ( %s ` z ) / ( z - P ) )' % (F1, G1, FY))
    meq = s([eq], 'mpteq2dva', '%s = %s' % (M1, KPD))
    cs, _ = w.wcongr(HOLF(M1, DP), {}, A0, {}, rules={M1: (KPD, meq)})
    hk = s([hd, cs], 'mpbid', HOLF(KPD, DP))
    rh = s([s([ab, a0], 'jca', '( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) )'), w.inst('ef2rhp')], 'syl', '( ( A crect B ) C_ %s /\\ ( A crect B ) C_ %s )' % (HP0, CN0))
    rcn = s([rh, w.inst('simpr')], 'syl', '( A crect B ) C_ %s' % CN0)
    rdp = s([s([rcn, pn], 'jca', '( ( A crect B ) C_ %s /\\ -. P e. ( A crect B ) )' % CN0), w.s([], 'ssdifsn', '( ( A crect B ) C_ %s <-> ( ( A crect B ) C_ %s /\\ -. P e. ( A crect B ) ) )' % (DP, CN0))],
            'sylibr', '( A crect B ) C_ %s' % DP)
    hc = s([s([hk, rdp], 'jca', '( %s /\\ ( A crect B ) C_ %s )' % (HOLF(KPD, DP), DP)), w.inst('holcrect')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) )' % (KPD, DP, KPD))
    RG = tsub(stmt('rectintgour'), {'F': KPD, 'D': DP})
    ra, rc = ante_of(RG)
    geo = s([G3, w.inst('simp2')], 'syl', '( Re ` A ) <_ ( Re ` B )'), s([G3, w.inst('simp3')], 'syl', '( Im ` A ) <_ ( Im ` B )')
    have = {'( A e. CC /\\ B e. CC )': ab, '( Re ` A ) <_ ( Re ` B )': geo[0], '( Im ` A ) <_ ( Im ` B )': geo[1], body_of(w, hc): hc}
    w.qed([conj(w, A0, ra, have), w.inst('rectintgour')], 'syl', S['tpnopole'])
    return run(w)


def gen_kph():
    w = W('tpkph', 'The mapping ` z |-> ( 1 / z ) ^ Y / ( z - Q ) ` is holomorphic on ` CC ` minus ` 0 ` and ` Q ` .')
    A0, GC = ante_of(S['tpkph'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yr = s([], 'simpl', 'Y e. NN'); pc = s([], 'simpr', 'Q e. CC')
    K = '( TopOpen ` CCfld )'
    k_ = w.s([], 'eqid', '%s = %s' % (K, K))
    haus = s([w.s([k_], 'cnfldhaus', '%s e. Haus' % K)], 'a1i', '%s e. Haus' % K)
    scl = s([haus, pc, w.s([w.s([], 'unicntop', 'CC = U. %s' % K)], 'sncld', '( ( %s e. Haus /\\ Q e. CC ) -> { Q } e. ( Clsd ` %s ) )' % (K, K))], 'syl2anc', '{ Q } e. ( Clsd ` %s )' % K)
    dop = s([s([w.s([], 'cnn0opn', '%s e. %s' % (CN0, K))], 'a1i', '%s e. %s' % (CN0, K)), scl,
             w.s([w.s([], 'unicntop', 'CC = U. %s' % K)], 'difopn', '( ( %s e. %s /\\ { Q } e. ( Clsd ` %s ) ) -> %s e. %s )' % (CN0, K, K, DQ, K))], 'syl2anc', '%s e. %s' % (DQ, K))
    dss = s([w.s([], 'difss', '%s C_ %s' % (DQ, CN0))], 'a1i', '%s C_ %s' % (DQ, CN0))
    ph = s([yr, w.s([], 'tpfh', '( Y e. NN -> %s )' % HOLF(FY, CN0))], 'syl', HOLF(FY, CN0))
    F1 = '( b e. %s |-> ( %s ` b ) )' % (DQ, FY)
    G1 = '( b e. %s |-> ( b - Q ) )' % DQ
    f1 = s([s([ph, s([dop, dss], 'jca', '( %s e. %s /\\ %s C_ %s )' % (DQ, K, DQ, CN0))], 'jca', '( %s /\\ ( %s e. %s /\\ %s C_ %s ) )' % (HOLF(FY, CN0), DQ, K, DQ, CN0)),
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
    fv1 = fvmd(w, Az, 'b', DQ, '( %s ` b )' % FY, 'z', zd, sz([w.s([], 'fvex', '( %s ` z ) e. _V' % FY)], 'a1i', '( %s ` z ) e. _V' % FY))
    gv1 = fvmd(w, Az, 'b', DQ, '( b - Q )', 'z', zd, sz([], 'ovexd', '( z - Q ) e. _V'))
    eq = sz([fv1, gv1], 'oveq12d', '( ( %s ` z ) / ( %s ` z ) ) = ( ( %s ` z ) / ( z - Q ) )' % (F1, G1, FY))
    meq = s([eq], 'mpteq2dva', '%s = %s' % (M1, KPO))
    cs, _ = w.wcongr(HOLF(M1, DQ), {}, A0, {}, rules={M1: (KPO, meq)})
    w.qed([hd, cs], 'mpbid', S['tpkph'])
    return run(w)


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
    w = W('tpstk', 'One Newton term: the boundary integral of ` M ( 1 / s ) ^ Y / ( s - Q ) ` over a rectangle in the right half-plane is ` 2 pi i M ( 1 / Q ) ^ Y ` when ` Q ` is strictly inside and ` 0 ` when ` Q ` is outside ( ~ tppole , ~ tpnopole ; any carrier ` E ` containing the frame; EF2 ~ ef2stk with this kernel).')
    A0, GC = ante_of(S['tpstk'])
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
    hk = s([yr, qc, w.inst('tpkph')], 'syl2anc', HOLF(KPO, DQ))
    kcn = s([hk, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (KPO, DQ))
    G = '( %s |` E )' % KPO
    gcn = s([edq, kcn, w.inst('rescncf')], 'sylc', '%s e. ( E -cn-> CC )' % G)
    pkh = s([yr, w.s([], 'tpfh', '( Y e. NN -> %s )' % HOLF(FY, CN0))], 'syl', HOLF(FY, CN0))
    pkf = s([s([pkh, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (FY, CN0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (FY, CN0))
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
    PU = '( %s ` u )' % FY
    gu = '( %s / ( u - Q ) )' % PU
    pkc = su([up(w, pkf, Au), ucn], 'ffvelcdmd', '%s e. CC' % PU)
    guc = su([pkc, su([uc, up(w, qc, Au)], 'subcld', '( u - Q ) e. CC'), su([uc, up(w, qc, Au), une], 'subne0d', '( u - Q ) =/= 0')], 'divcld', '%s e. CC' % gu)
    tv = fvmd(w, Au, 'd', 'E', '( M x. ( ( %s ` d ) / ( d - Q ) ) )' % FY, 'u', ue, w.s([], 'ovexd', '( %s -> ( M x. %s ) e. _V )' % (Au, gu)))
    gres = su([ue, w.inst('fvres')], 'syl', '( %s ` u ) = ( %s ` u )' % (G, KPO))
    kv = fvmd(w, Au, 'z', DQ, '( ( %s ` z ) / ( z - Q ) )' % FY, 'u', ud, w.s([], 'ovexd', '( %s -> %s e. _V )' % (Au, gu)))
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
            PO = tsub(S['tppole'], {'P': 'Q'})
            pa, pc_ = ante_of(PO)
            ins = sc([], 'simpr', INSQ)
            hv = {'Y e. NN': up(w, yr, C), '( A e. CC /\\ B e. CC )': up(w, ab, C), '0 < ( Re ` A )': up(w, a0, C), 'Q e. CC': up(w, qc, C), INSQ: ins}
            pole = sc([conj(w, C, pa, hv), w.inst('tppole')], 'syl', pc_)
            # KPO and KR agree off Q on the rectangle
            Cv = '( %s /\\ u e. %s )' % (C, RB)
            sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Cv, f))
            urb = sv([], 'simpr', 'u e. %s' % RB)
            e2 = sv([urb, w.s([], 'eldifsn', '( u e. %s <-> ( u e. ( A crect B ) /\\ u =/= Q ) )' % RB)], 'sylib', '( u e. ( A crect B ) /\\ u =/= Q )')
            rh = sv([sv([up(w, ab, Cv), up(w, a0, Cv)], 'jca', '( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) )'), w.inst('ef2rhp')], 'syl', '( ( A crect B ) C_ %s /\\ ( A crect B ) C_ %s )' % (HP0, CN0))
            ucn2 = sv([sv([rh, w.inst('simpr')], 'syl', '( A crect B ) C_ %s' % CN0), sv([e2, w.inst('simpl')], 'syl', 'u e. ( A crect B )')], 'sseldd', 'u e. %s' % CN0)
            udq = sv([sv([ucn2, sv([e2, w.inst('simpr')], 'syl', 'u =/= Q')], 'jca', '( u e. %s /\\ u =/= Q )' % CN0), w.s([], 'eldifsn', '( u e. %s <-> ( u e. %s /\\ u =/= Q ) )' % (DQ, CN0))], 'sylibr', 'u e. %s' % DQ)
            v1 = fvmd(w, Cv, 'z', DQ, '( ( %s ` z ) / ( z - Q ) )' % FY, 'u', udq, w.s([], 'ovexd', '( %s -> %s e. _V )' % (Cv, gu)))
            v2 = fvmd(w, Cv, 'z', RB, '( ( %s ` z ) / ( z - Q ) )' % FY, 'u', urb, w.s([], 'ovexd', '( %s -> %s e. _V )' % (Cv, gu)))
            kk = w.s([sv([v1, v2], 'eqtr4d', '( %s ` u ) = ( %s ` u )' % (KPO, KR))], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (C, RB, KPO, KR))
            EP = tsub(stmt('rectinteqp'), {'F': KPO, 'G': KR, 'P': 'Q', 'V': '_V'})
            epa, epc = ante_of(EP)
            hv2 = dict(hv); hv2['%s e. _V' % KPO] = up(w, kex, C); hv2['%s e. _V' % KR] = sc([w.s([w.s([w.s([], 'ovex', '( A crect B ) e. _V')], 'difexi', '%s e. _V' % RB)], 'mptex', '%s e. _V' % KR)], 'a1i', '%s e. _V' % KR); hv2[body_of(w, kk)] = kk
            ikr = sc([conj(w, C, epa, hv2), w.inst('rectinteqp')], 'syl', epc)
            ival = sc([ikr, pole], 'eqtrd', '%s = ( %s x. ( ( 1 / Q ) ^ Y ) )' % (IK, TPI))
            V = '( %s x. ( ( 1 / Q ) ^ Y ) )' % TPI
            RES = '( %s x. ( M x. ( ( 1 / Q ) ^ Y ) ) )' % TPI
        else:
            npi = sc([up(w, q3, C), sc([], 'simpr', '-. %s' % INSQ)], 'mtod', '-. Q e. ( A crect B )')
            NP = tsub(S['tpnopole'], {'P': 'Q'})
            na, nc = ante_of(NP)
            hv = {'Y e. NN': up(w, yr, C), '( A e. CC /\\ B e. CC )': up(w, ab, C), body_of(w, geo): up(w, geo, C), 'Q e. CC': up(w, qc, C), '-. Q e. ( A crect B )': npi}
            ival = sc([conj(w, C, na, hv), w.inst('tpnopole')], 'syl', nc)
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
            yq = sc([sc([up(w, qc, C), qn0], 'reccld', '( 1 / Q ) e. CC'), sc([up(w, yr, C)], 'nnnn0d', 'Y e. NN0')], 'expcld', '( ( 1 / Q ) ^ Y ) e. CC')
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
            outs.append(sc([l3, sc([sc([], 'simpr', '-. %s' % INSQ)], 'iffalsed', 'if ( %s , %s , 0 ) = 0' % (INSQ, '( %s x. ( M x. ( ( 1 / Q ) ^ Y ) ) )' % TPI))], 'eqtr4d', GC))
    w.qed(outs, 'pm2.61dan', S['tpstk'])
    return run(w)


def gen_tmc():
    w = W('tptmc', 'The term ` M ( 1 / z ) ^ Y / ( z - Q ) ` is continuous on every set avoiding ` 0 ` and ` Q ` .')
    A0, GC = ante_of(S['tptmc'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yr = s([], 'simp1', 'Y e. NN'); mq = s([], 'simp2', '( M e. CC /\\ Q e. CC )'); edq = s([], 'simp3', 'E C_ %s' % DQ)
    mc = s([mq, w.inst('simpl')], 'syl', 'M e. CC'); qc = s([mq, w.inst('simpr')], 'syl', 'Q e. CC')
    kcn = s([s([yr, qc, w.inst('tpkph')], 'syl2anc', HOLF(KPO, DQ)), w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (KPO, DQ))
    rc = s([edq, kcn, w.inst('rescncf')], 'sylc', '( %s |` E ) e. ( E -cn-> CC )' % KPO)
    BZ = '( ( %s ` z ) / ( z - Q ) )' % FY
    BD = '( ( %s ` d ) / ( d - Q ) )' % FY
    rm = s([edq, w.inst('resmpt')], 'syl', '( %s |` E ) = ( z e. E |-> %s )' % (KPO, BZ))
    idd = w.s([], 'id', '( z = d -> z = d )')
    cz, _ = w.congr(BZ, {'z': 'd'}, 'z = d', {'z': idd})
    cb = s([w.s([cz], 'cbvmptv', '( z e. E |-> %s ) = ( d e. E |-> %s )' % (BZ, BD))], 'a1i', '( z e. E |-> %s ) = ( d e. E |-> %s )' % (BZ, BD))
    kd = s([s([rm, cb], 'eqtrd', '( %s |` E ) = ( d e. E |-> %s )' % (KPO, BD)), rc], 'eqeltrrd', '( d e. E |-> %s ) e. ( E -cn-> CC )' % BD)
    ecc = s([edq, s([s([w.s([], 'difss', '%s C_ %s' % (DQ, CN0))], 'a1i', '%s C_ %s' % (DQ, CN0)), s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)], 'sstrd', '%s C_ CC' % DQ)],
            'sstrd', 'E C_ CC')
    mcn = s([mc, ecc, s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( d e. E |-> M ) e. ( E -cn-> CC )')
    w.qed([mcn, kd], 'mulcncf', S['tptmc'])
    return run(w)



if __name__ == '__main__':
    gen_fh()
    gen_pole()
    gen_nopole()
    gen_kph()
    gen_stk()
    gen_tmc()

