"""Sortie ZC1: ( s - 1 ) eta ( s ) = ( 1 - 2 ^ ( 1 - s ) ) E1 ( s ) on the right half-plane (etarel)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
import zc1_c, zc1_f, zc1_j, zc1_n, zc1_q
from zc1_c import u1base, cx1val, U1, CX1
from zc1_j import Z1
from zc1_q import hp_cc
import lin
lin.FASTPATH = True

S['etarel'] = '( S e. %s -> ( ( S - 1 ) x. ( %s ` S ) ) = ( ( %s ` S ) x. ( %s ` S ) ) )' % (HP0, ETA, GF, E1)
EB = 'sum_ k e. NN ( ( k mod 2 ) x. ( ( k ^c -u %s ) - ( ( k + 1 ) ^c -u %s ) ) )'
ETAa = '( a e. %s |-> %s )' % (HP0, EB % ('a', 'a'))
GFa = '( a e. %s |-> ( 1 - ( 2 ^c ( 1 - a ) ) ) )' % HP0
Z1a = '( a e. %s |-> ( a - 1 ) )' % HP0


def renamed_hol(w, A0, holst, M, Ma, cbv_hyp):
    """( A0 -> HOL(Ma) ) and ( A0 -> M = Ma ) from holst : ( A0 -> HOL(M) ), cbv_hyp the ( z = a -> body = body' ) step"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    eq = s([w.s([cbv_hyp], 'cbvmptv', '%s = %s' % (M, Ma))], 'a1i', '%s = %s' % (M, Ma))
    cn = s([eq, s([holst, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (M, HP0))], 'eqeltrd' if False else 'eqeltrd', '%s e. ( %s -cn-> CC )' % (Ma, HP0)) if False else \
        s([s([eq], 'eqcomd', '%s = %s' % (Ma, M)), s([holst, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (M, HP0))], 'eqeltrd', '%s e. ( %s -cn-> CC )' % (Ma, HP0))
    dm = s([s([holst, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D %s )' % (HP0, M)), s([s([eq], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (M, Ma))], 'dmeqd', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (M, Ma))],
           'sseqtrd', '%s C_ dom ( CC _D %s )' % (HP0, Ma))
    return s([cn, dm], 'jca', HOLF(Ma, HP0)), eq


def gen_etarel():
    w = W('etarel', 'On the right half-plane ` ( s - 1 ) eta ( s ) = ( 1 - 2 ^ ( 1 - s ) ) E1 ( s ) ` , ` E1 = ( s - 1 ) zeta ( s ) ` (Lean ` etaFun_eqOn ` ; ~ etazser , ~ zl1dser , ~ hp0id ).')
    A0 = 'S e. %s' % HP0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    sh = s([], 'id', A0)
    ub = u1base(w, A0)
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), ub], 'jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    e1hol = s([nx1, w.inst('zl1ehol')], 'syl', HOLF(E1, HP0))
    etah = s([s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0')], 'jca', '( 0 e. RR /\\ 0 <_ 0 )'), w.inst('etahol')], 'syl', HOLF(ETA, HP0))
    gfh = s([w.s([], 'gfhol', S['gfhol'])], 'a1i', S['gfhol'])
    z1h = s([w.s([], 'hsub1', S['hsub1'])], 'a1i', S['hsub1'])
    ce = w.s([w.s([w.s([w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( k ^c -u z ) = ( k ^c -u a ) )'),
                          w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( ( k + 1 ) ^c -u z ) = ( ( k + 1 ) ^c -u a ) )')], 'oveq12d',
                         '( z = a -> ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) = ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) )')], 'oveq2d',
                    '( z = a -> ( ( k mod 2 ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) ) = ( ( k mod 2 ) x. ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) ) )')], 'sumeq2sdv',
              '( z = a -> %s = %s )' % (EB % ('z', 'z'), EB % ('a', 'a')))
    etaa, eeq = renamed_hol(w, A0, etah, ETA, ETAa, ce)
    cg = w.s([w.s([w.s([], 'oveq2', '( z = a -> ( 1 - z ) = ( 1 - a ) )')], 'oveq2d', '( z = a -> ( 2 ^c ( 1 - z ) ) = ( 2 ^c ( 1 - a ) ) )')], 'oveq2d',
             '( z = a -> ( 1 - ( 2 ^c ( 1 - z ) ) ) = ( 1 - ( 2 ^c ( 1 - a ) ) ) )')
    gfa, geq = renamed_hol(w, A0, gfh, GF, GFa, cg)
    cz = w.s([], 'oveq1', '( z = a -> ( z - 1 ) = ( a - 1 ) )')
    z1a, zeq = renamed_hol(w, A0, z1h, Z1, Z1a, cz)
    F1 = '( b e. %s |-> ( ( %s ` b ) x. ( %s ` b ) ) )' % (HP0, Z1a, ETAa)
    G1 = '( b e. %s |-> ( ( %s ` b ) x. ( %s ` b ) ) )' % (HP0, GFa, E1)
    f1h = s([s([z1a, etaa], 'jca', '( %s /\\ %s )' % (HOLF(Z1a, HP0), HOLF(ETAa, HP0))), w.inst('holmul')], 'syl', HOLF(F1, HP0))
    g1h = s([s([gfa, e1hol], 'jca', '( %s /\\ %s )' % (HOLF(GFa, HP0), HOLF(E1, HP0))), w.inst('holmul')], 'syl', HOLF(G1, HP0))
    def vals(ante, x, xh):
        """values of F1, G1 at x: ( ante -> ( F1 ` x ) = ( ( x - 1 ) x. EB(x) ) ), ( ante -> ( G1 ` x ) = ( ( 1 - 2 ^c ( 1 - x ) ) x. ( E1 ` x ) ) )"""
        sa = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        mv = lambda M, x_, body, val, exs: _cg.mptval(w, ante, 'a', HP0, body, x_, xh, exs=sa([w.s([], exs, '%s e. _V' % val)], 'a1i', '%s e. _V' % val), gen=w.g)[0]
        zv = mv(Z1a, x, '( a - 1 )', '( %s - 1 )' % x, 'ovex')
        ev = mv(ETAa, x, EB % ('a', 'a'), EB % (x, x), 'sumex')
        gv = mv(GFa, x, '( 1 - ( 2 ^c ( 1 - a ) ) )', '( 1 - ( 2 ^c ( 1 - %s ) ) )' % x, 'ovex')
        f1v = _cg.mptval(w, ante, 'b', HP0, '( ( %s ` b ) x. ( %s ` b ) )' % (Z1a, ETAa), x, xh,
                         exs=sa([w.s([], 'ovex', '( ( %s ` %s ) x. ( %s ` %s ) ) e. _V' % (Z1a, x, ETAa, x))], 'a1i', '( ( %s ` %s ) x. ( %s ` %s ) ) e. _V' % (Z1a, x, ETAa, x)), gen=w.g)[0]
        g1v = _cg.mptval(w, ante, 'b', HP0, '( ( %s ` b ) x. ( %s ` b ) )' % (GFa, E1), x, xh,
                         exs=sa([w.s([], 'ovex', '( ( %s ` %s ) x. ( %s ` %s ) ) e. _V' % (GFa, x, E1, x))], 'a1i', '( ( %s ` %s ) x. ( %s ` %s ) ) e. _V' % (GFa, x, E1, x)), gen=w.g)[0]
        F1v = sa([f1v, sa([zv, ev], 'oveq12d', '( ( %s ` %s ) x. ( %s ` %s ) ) = ( ( %s - 1 ) x. %s )' % (Z1a, x, ETAa, x, x, EB % (x, x)))], 'eqtrd', '( %s ` %s ) = ( ( %s - 1 ) x. %s )' % (F1, x, x, EB % (x, x)))
        G1v = sa([g1v, sa([gv], 'oveq1d', '( ( %s ` %s ) x. ( %s ` %s ) ) = ( ( 1 - ( 2 ^c ( 1 - %s ) ) ) x. ( %s ` %s ) )' % (GFa, x, E1, x, x, E1, x))], 'eqtrd',
                 '( %s ` %s ) = ( ( 1 - ( 2 ^c ( 1 - %s ) ) ) x. ( %s ` %s ) )' % (G1, x, x, E1, x))
        return F1v, G1v, ev, gv
    Av = '( ( %s /\\ v e. %s ) /\\ 1 < ( Re ` v ) )' % (A0, HP0)
    sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    vh = sv([], 'simplr', 'v e. %s' % HP0); v1 = sv([], 'simpr', '1 < ( Re ` v )')
    vc, _ = hp_cc(w, Av, vh, 'v')
    zv = sv([vc, v1], 'jca', '( v e. CC /\\ 1 < ( Re ` v ) )')
    F1v, G1v, _, _ = vals(Av, 'v', vh)
    ez = sv([zv, w.inst('etazser')], 'syl', '%s = ( ( 1 - ( 2 ^c ( 1 - v ) ) ) x. sum_ k e. NN ( k ^c -u v ) )' % (EB % ('v', 'v')))
    DS = ante_of(tsub(stmt('zl1dser'), {'N': '1', 'X': U1}))[1]
    body = DS[len('A. s e. %s ' % HP0):]
    inst = tsub(body, {'s': 'v'})
    eqs = w.wcongr(body, {'s': 'v'}, 's = v', {'s': w.s([], 'id', '( s = v -> s = v )')})[0]
    e1d = sv([v1, sv([eqs, sv([lift(w, nx1, Av), w.inst('zl1dser')], 'syl', DS), vh], 'rspcdva', inst)], 'mpd', inst.split(' -> ', 1)[1][:-2])
    Avk = '( %s /\\ k e. NN )' % Av
    c1k, _ = cx1val(w, Av, lift(w, ub, Av))
    kv = w.s([w.s([w.s([], 'simpr', '( %s -> k e. NN )' % Avk)], 'nncnd', '( %s -> k e. CC )' % Avk), w.s([lift(w, vc, Avk)], 'negcld', '( %s -> -u v e. CC )' % Avk)], 'cxpcld', '( %s -> ( k ^c -u v ) e. CC )' % Avk)
    t2 = w.s([w.s([c1k], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u v ) ) = ( 1 x. ( k ^c -u v ) ) )' % (Avk, CX1)), w.s([kv], 'mullidd', '( %s -> ( 1 x. ( k ^c -u v ) ) = ( k ^c -u v ) )' % Avk)],
             'eqtrd', '( %s -> ( ( %s ` k ) x. ( k ^c -u v ) ) = ( k ^c -u v ) )' % (Avk, CX1))
    ZV = 'sum_ k e. NN ( k ^c -u v )'
    DSX1 = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) )' % CX1
    sc1 = sv([t2], 'sumeq2dv', '%s = %s' % (DSX1, ZV))
    e1v = sv([e1d, sv([sc1], 'oveq2d', '( ( v - 1 ) x. %s ) = ( ( v - 1 ) x. %s )' % (DSX1, ZV))], 'eqtrd', '( %s ` v ) = ( ( v - 1 ) x. %s )' % (E1, ZV))
    CH = tsub(stmt('zl2chs'), {'N': '1', 'X': U1, 'Z': 'v'})
    chs = sv([sv([lift(w, nx1, Av), zv], 'jca', ante_of(CH)[0]), w.inst('zl2chs')], 'syl', ante_of(CH)[1])
    zvc = sv([sc1, sv([chs, w.inst('simpl')], 'syl', '%s e. CC' % DSX1)], 'eqeltrrd', '%s e. CC' % ZV)
    G_ = '( 1 - ( 2 ^c ( 1 - v ) ) )'
    gc = sv([sv([], '1cnd', '1 e. CC'), sv([sv([], '2cnd', '2 e. CC'), sv([sv([], '1cnd', '1 e. CC'), vc], 'subcld', '( 1 - v ) e. CC')], 'cxpcld', '( 2 ^c ( 1 - v ) ) e. CC')], 'subcld', '%s e. CC' % G_)
    v1c = sv([vc, sv([], '1cnd', '1 e. CC')], 'subcld', '( v - 1 ) e. CC')
    lhs = sv([F1v, sv([ez], 'oveq2d', '( ( v - 1 ) x. %s ) = ( ( v - 1 ) x. ( %s x. %s ) )' % (EB % ('v', 'v'), G_, ZV))], 'eqtrd', '( %s ` v ) = ( ( v - 1 ) x. ( %s x. %s ) )' % (F1, G_, ZV))
    rhs = sv([G1v, sv([e1v], 'oveq2d', '( %s x. ( %s ` v ) ) = ( %s x. ( ( v - 1 ) x. %s ) )' % (G_, E1, G_, ZV))], 'eqtrd', '( %s ` v ) = ( %s x. ( ( v - 1 ) x. %s ) )' % (G1, G_, ZV))
    m12 = sv([v1c, gc, zvc], 'mul12d', '( ( v - 1 ) x. ( %s x. %s ) ) = ( %s x. ( ( v - 1 ) x. %s ) )' % (G_, ZV, G_, ZV))
    fg = sv([sv([lhs, m12], 'eqtrd', '( %s ` v ) = ( %s x. ( ( v - 1 ) x. %s ) )' % (F1, G_, ZV)), sv([rhs], 'eqcomd', '( %s x. ( ( v - 1 ) x. %s ) ) = ( %s ` v )' % (G_, ZV, G1))], 'eqtrd',
            '( %s ` v ) = ( %s ` v )' % (F1, G1))
    Av0 = '( %s /\\ v e. %s )' % (A0, HP0)
    agr = s([w.s([fg], 'ex', '( %s -> ( 1 < ( Re ` v ) -> ( %s ` v ) = ( %s ` v ) ) )' % (Av0, F1, G1))], 'ralrimiva', 'A. v e. %s ( 1 < ( Re ` v ) -> ( %s ` v ) = ( %s ` v ) )' % (HP0, F1, G1))
    HI = tsub(S['hp0id'], {'F': F1, 'G': G1})
    hia, hic = ante_of(HI)
    hi = s([s([f1h, g1h, agr], '3jca', hia), w.inst('hp0id')], 'syl', hic)
    eqz = w.s([w.s([], 'fveq2', '( z = S -> ( %s ` z ) = ( %s ` S ) )' % (F1, F1)), w.s([], 'fveq2', '( z = S -> ( %s ` z ) = ( %s ` S ) )' % (G1, G1))], 'eqeq12d',
              '( z = S -> ( ( %s ` z ) = ( %s ` z ) <-> ( %s ` S ) = ( %s ` S ) ) )' % (F1, G1, F1, G1))
    fgS = s([eqz, hi, sh], 'rspcdva', '( %s ` S ) = ( %s ` S )' % (F1, G1))
    F1S, G1S, evS, gvS = vals(A0, 'S', sh)
    # back to ETA and GF
    ea = s([s([eeq], 'fveq1d', '( %s ` S ) = ( %s ` S )' % (ETA, ETAa)), evS], 'eqtrd', '( %s ` S ) = %s' % (ETA, EB % ('S', 'S')))
    ga = s([s([geq], 'fveq1d', '( %s ` S ) = ( %s ` S )' % (GF, GFa)), gvS], 'eqtrd', '( %s ` S ) = ( 1 - ( 2 ^c ( 1 - S ) ) )' % GF)
    l = s([s([s([F1S], 'eqcomd', '( ( S - 1 ) x. %s ) = ( %s ` S )' % (EB % ('S', 'S'), F1)), fgS], 'eqtrd', '( ( S - 1 ) x. %s ) = ( %s ` S )' % (EB % ('S', 'S'), G1)), G1S], 'eqtrd',
          '( ( S - 1 ) x. %s ) = ( ( 1 - ( 2 ^c ( 1 - S ) ) ) x. ( %s ` S ) )' % (EB % ('S', 'S'), E1))
    fin = s([s([s([ea], 'oveq2d', '( ( S - 1 ) x. ( %s ` S ) ) = ( ( S - 1 ) x. %s )' % (ETA, EB % ('S', 'S'))), l], 'eqtrd',
               '( ( S - 1 ) x. ( %s ` S ) ) = ( ( 1 - ( 2 ^c ( 1 - S ) ) ) x. ( %s ` S ) )' % (ETA, E1)), s([s([ga], 'oveq1d', '( ( %s ` S ) x. ( %s ` S ) ) = ( ( 1 - ( 2 ^c ( 1 - S ) ) ) x. ( %s ` S ) )' % (GF, E1, E1))], 'eqcomd',
               '( ( 1 - ( 2 ^c ( 1 - S ) ) ) x. ( %s ` S ) ) = ( ( %s ` S ) x. ( %s ` S ) )' % (E1, GF, E1))], 'eqtrd', S['etarel'].split(' -> ', 1)[1][:-2])
    w.lines.append('qed:%s:idi |- %s' % (fin, S['etarel']))
    return run8(w)


if __name__ == '__main__':
    gen_etarel()
