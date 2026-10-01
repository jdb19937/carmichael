"""Sortie EF2: rectangle residues of y ^ s / ( s ( s - p ) ) (ef2rhp, ef2pole, ef2nopole)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
from z4blib import fvmd
import lin
lin.FASTPATH = True

CN0 = '( CC \\ { 0 } )'
S['ef2rhp'] = '( ( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) ) -> ( ( A crect B ) C_ %s /\\ ( A crect B ) C_ %s ) )' % (HP0, CN0)


def gen_rhp():
    w = W('ef2rhp', 'A closed rectangle with ` 0 < Re A ` lies in the right half-plane and misses ` 0 ` .')
    A0, GC = ante_of(S['ef2rhp'])
    Au = '( %s /\\ u e. ( A crect B ) )' % A0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Au, f))
    ab = s([], 'simpll', '( A e. CC /\\ B e. CC )')
    ac = s([ab, w.inst('simpl')], 'syl', 'A e. CC'); bc = s([ab, w.inst('simpr')], 'syl', 'B e. CC')
    a0 = s([], 'simplr', '0 < ( Re ` A )')
    bd = crect_bounds(w, Au, ac, bc, s([], 'simpr', 'u e. ( A crect B )'), 'A', 'B', 'u')
    ru = lin8(w, Au, [a0, bd['le'][0]], '0 < ( Re ` u )', bd['cl'])
    hp = s([s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( u e. %s <-> ( u e. CC /\\ 0 < ( Re ` u ) ) )' % HP0),
            s([bd['cc'], ru], 'jca', '( u e. CC /\\ 0 < ( Re ` u ) )')], 'mpbird', 'u e. %s' % HP0)
    e1 = s([w.s([w.s([], 'fveq2', '( u = 0 -> ( Re ` u ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( u = 0 -> ( Re ` u ) = 0 )')], 'a1i', '( u = 0 -> ( Re ` u ) = 0 )')
    un = s([s([ru], 'gt0ne0d', '( Re ` u ) =/= 0'), s([e1], 'necon3d', '( ( Re ` u ) =/= 0 -> u =/= 0 )')], 'mpd', 'u =/= 0')
    cn = s([s([bd['cc'], un], 'jca', '( u e. CC /\\ u =/= 0 )'), w.s([], 'eldifsn', '( u e. %s <-> ( u e. CC /\\ u =/= 0 ) )' % CN0)], 'sylibr', 'u e. %s' % CN0)
    s1 = w.s([w.s([hp], 'ex', '( %s -> ( u e. ( A crect B ) -> u e. %s ) )' % (A0, HP0))], 'ssrdv', '( %s -> ( A crect B ) C_ %s )' % (A0, HP0))
    s2 = w.s([w.s([cn], 'ex', '( %s -> ( u e. ( A crect B ) -> u e. %s ) )' % (A0, CN0))], 'ssrdv', '( %s -> ( A crect B ) C_ %s )' % (A0, CN0))
    w.qed([s1, s2], 'jca', S['ef2rhp'])
    return run8(w)


def gen_pole():
    w = W('ef2pole', 'Lean ` rectInt_ys_pole ` : for ` p ` strictly inside a rectangle in the right half-plane, the boundary integral of ` y ^ s / ( s ( s - p ) ) ` is ` 2 pi i y ^ p / p ` ( C0c ~ rectintcau at C4 ~ pkfhol ).')
    A0, GC = ante_of(S['ef2pole'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    yr = s([], 'simp1', 'Y e. RR+')
    X2 = '( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) )'
    x2 = s([], 'simp2', X2)
    X3 = '( P e. CC /\\ %s )' % INS('P', 'A', 'B')
    x3 = s([], 'simp3', X3)
    ab = s([x2, w.inst('simpl')], 'syl', '( A e. CC /\\ B e. CC )')
    rh = s([x2, w.inst('ef2rhp')], 'syl', '( ( A crect B ) C_ %s /\\ ( A crect B ) C_ %s )' % (HP0, CN0))
    rcn = s([rh, w.inst('simpr')], 'syl', '( A crect B ) C_ %s' % CN0)
    ph = s([yr, w.s([], 'pkfhol', '( Y e. RR+ -> %s )' % HOLF(PKF(), CN0))], 'syl', HOLF(PKF(), CN0))
    hc = s([s([ph, rcn], 'jca', '( %s /\\ ( A crect B ) C_ %s )' % (HOLF(PKF(), CN0), CN0)), w.inst('holcrect')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) )' % (PKF(), CN0, PKF()))
    RC = tsub(stmt('rectintcau'), {'F': PKF(), 'D': CN0})
    ra, rc = ante_of(RC)
    cau = s([conj(w, A0, ra, {'( A e. CC /\\ B e. CC )': ab, X3: x3, body_of(w, hc): hc}), w.inst('rectintcau')], 'syl', rc)
    pin = s([ab, x3, w.inst('crectinp')], 'syl2anc', 'P e. ( A crect B )')
    pn = s([rcn, pin], 'sseldd', 'P e. %s' % CN0)
    pv = fvmd(w, A0, 'o', CN0, '( ( Y ^c o ) / o )', 'P', pn, w.s([], 'ovexd', '( %s -> ( ( Y ^c P ) / P ) e. _V )' % A0))
    w.qed([cau, s([pv], 'oveq2d', '( %s x. ( %s ` P ) ) = ( %s x. ( ( Y ^c P ) / P ) )' % (TPI, PKF(), TPI))], 'eqtrd', S['ef2pole'])
    return run8(w)


S['ef2hsub'] = '( ( P e. CC /\\ D e. ( TopOpen ` CCfld ) ) -> %s )' % HOLF('( z e. D |-> ( z - P ) )', 'D')


def gen_hsub():
    w = W('ef2hsub', 'The mapping ` z |-> z - P ` is holomorphic on every open set (as ZC1 ~ hsub1 ).')
    A0, GC = ante_of(S['ef2hsub'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pc = s([], 'simpl', 'P e. CC'); do = s([], 'simpr', 'D e. ( TopOpen ` CCfld )')
    Az = '( %s /\\ z e. CC )' % A0
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    cc = s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', 'CC e. { RR , CC }')
    d2 = s([cc], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    d1 = s([cc, pc], 'dvmptc', '( CC _D ( z e. CC |-> P ) ) = ( z e. CC |-> 0 )')
    zc = sz([], 'simpr', 'z e. CC'); one = sz([], '1cnd', '1 e. CC'); zero = sz([], '0cnd', '0 e. CC'); pz = up(w, pc, Az)
    dA = s([cc, zc, one, d2, pz, zero, d1], 'dvmptsub', '( CC _D ( z e. CC |-> ( z - P ) ) ) = ( z e. CC |-> ( 1 - 0 ) )')
    dm = s([s([sz([one, zero], 'subcld', '( 1 - 0 ) e. CC')], 'ralrimiva', 'A. z e. CC ( 1 - 0 ) e. CC'), w.inst('dmmptg')], 'syl', 'dom ( z e. CC |-> ( 1 - 0 ) ) = CC')
    dmG = s([s([dA], 'dmeqd', 'dom ( CC _D ( z e. CC |-> ( z - P ) ) ) = dom ( z e. CC |-> ( 1 - 0 ) )'), dm], 'eqtrd', 'dom ( CC _D ( z e. CC |-> ( z - P ) ) ) = CC')
    gf = s([sz([zc, pz], 'subcld', '( z - P ) e. CC')], 'fmptd', '( z e. CC |-> ( z - P ) ) : CC --> CC')
    ss = s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC')
    cn = s([s([ss, gf, ss], '3jca', '( CC C_ CC /\\ ( z e. CC |-> ( z - P ) ) : CC --> CC /\\ CC C_ CC )'), dmG, w.inst('dvcn')], 'syl2anc', '( z e. CC |-> ( z - P ) ) e. ( CC -cn-> CC )')
    dms = s([s([dmG], 'eqcomd', 'CC = dom ( CC _D ( z e. CC |-> ( z - P ) ) )')], 'eqimssd', 'CC C_ dom ( CC _D ( z e. CC |-> ( z - P ) ) )')
    hc = s([cn, dms], 'jca', HOLF('( z e. CC |-> ( z - P ) )', 'CC'))
    w.qed([s([hc, do], 'jca', ante_of(tsub(stmt('zl2hent'), {'A': '( z - P )'}))[0]), w.inst('zl2hent')], 'syl', S['ef2hsub'])
    return run8(w)


def gen_nopole():
    w = W('ef2nopole', 'Lean ` rectInt_ys_nopole ` : for ` p ` outside a closed rectangle in the right half-plane, the boundary integral of ` y ^ s / ( s ( s - p ) ) ` vanishes (C0b ~ rectintgour ).')
    A0, GC = ante_of(S['ef2nopole'])
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
    ph = s([yr, w.s([], 'pkfhol', '( Y e. RR+ -> %s )' % HOLF(PKF(), CN0))], 'syl', HOLF(PKF(), CN0))
    F1 = '( b e. %s |-> ( %s ` b ) )' % (DP, PKF())
    G1 = '( b e. %s |-> ( b - P ) )' % DP
    f1 = s([s([ph, s([dop, dss], 'jca', '( %s e. %s /\\ %s C_ %s )' % (DP, K, DP, CN0))], 'jca', '( %s /\\ ( %s e. %s /\\ %s C_ %s ) )' % (HOLF(PKF(), CN0), DP, K, DP, CN0)), w.inst('zl2hres')],
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
    fv1 = fvmd(w, Az, 'b', DP, '( %s ` b )' % PKF(), 'z', zd, sz([w.s([], 'fvex', '( %s ` z ) e. _V' % PKF())], 'a1i', '( %s ` z ) e. _V' % PKF()))
    gv1 = fvmd(w, Az, 'b', DP, '( b - P )', 'z', zd, sz([], 'ovexd', '( z - P ) e. _V'))
    eq = sz([fv1, gv1], 'oveq12d', '( ( %s ` z ) / ( %s ` z ) ) = ( ( %s ` z ) / ( z - P ) )' % (F1, G1, PKF()))
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
    w.qed([conj(w, A0, ra, have), w.inst('rectintgour')], 'syl', S['ef2nopole'])
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2rhp', 'ef2pole', 'ef2hsub', 'ef2nopole']:
        {'ef2rhp': gen_rhp, 'ef2pole': gen_pole, 'ef2hsub': gen_hsub, 'ef2nopole': gen_nopole}[g]()
