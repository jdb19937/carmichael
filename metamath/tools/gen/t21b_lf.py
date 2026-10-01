"""Sortie T21b: t21lfp (LFunction_eq_primitive_mul_prod, every character)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *
import congr as _cg
from c8lib import tsub, ante_of
from zc1lib import HOLF
zstmt = lambda l: thm(l)[3:]

M_ = COND
EP = '( %s DChrLF %s )' % (COND, PRIM)
CX = '( a e. NN |-> ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` a ) ) )'


def gen_lfp():
    w = W('t21lfp', 'For every character ` X ` mod ` N ` , ` E_X = PF_X . E_X* ` on the right half-plane: the Euler factor at the primitive character times the ` E ` of the primitive character (Lean ` LFunction_eq_primitive_mul_prod ` ; ~ zl1dser , ~ zl2dsp , ~ zl2dpf , ~ hp0id , as ~ zc1prin ).')
    A0 = '( %s /\\ S e. %s )' % (NX, HP0)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', NX); sh = s([], 'simpr', 'S e. %s' % HP0)
    mx = s([s([nx, w.inst('dchrcondnn')], 'syl', '%s e. NN' % M_), s([nx, w.inst('dchrprimcl')], 'syl', '%s e. ( Base ` ( DChr ` %s ) )' % (PRIM, M_))], 'jca',
           '( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) )' % (M_, PRIM, M_))
    ehol = s([nx, w.inst('zl1ehol')], 'syl', HOLF(EN, HP0))
    ephol = s([mx, w.inst('zl1ehol')], 'syl', HOLF(EP, HP0))
    PFW = '( w e. CC |-> %s )' % PFX('w')
    dph = s([nx, w.inst('zl2dph')], 'syl', HOLF(PFW, 'CC'))
    PFM = '( j e. %s |-> %s )' % (HP0, PFX('j'))
    op = s([w.s([], 'hpopn', '%s e. ( TopOpen ` CCfld )' % HP0)], 'a1i', '%s e. ( TopOpen ` CCfld )' % HP0)
    PFJ = '( j e. CC |-> %s )' % PFX('j')
    ng = w.s([], 'negeq', '( w = j -> -u w = -u j )')
    cj1 = w.s([ng], 'oveq2d', '( w = j -> ( d ^c -u w ) = ( d ^c -u j ) )')
    cj2 = w.s([cj1], 'oveq2d', '( w = j -> ( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u w ) ) = ( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u j ) ) )' % (CY, CY))
    cj3 = w.s([cj2], 'sumeq2sdv', '( w = j -> %s = %s )' % (PFX('w'), PFX('j')))
    cvj = s([w.s([cj3], 'cbvmptv', '%s = %s' % (PFW, PFJ))], 'a1i', '%s = %s' % (PFW, PFJ))
    cn1 = s([s([cvj], 'eqcomd', '%s = %s' % (PFJ, PFW)), s([dph, w.inst('simpl')], 'syl', '%s e. ( CC -cn-> CC )' % PFW)], 'eqeltrd', '%s e. ( CC -cn-> CC )' % PFJ)
    dm1 = s([s([dph, w.inst('simpr')], 'syl', 'CC C_ dom ( CC _D %s )' % PFW),
             s([s([cvj], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (PFW, PFJ))], 'dmeqd', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (PFW, PFJ))], 'sseqtrd', 'CC C_ dom ( CC _D %s )' % PFJ)
    hj = s([cn1, dm1], 'jca', HOLF(PFJ, 'CC'))
    ZH = tsub(zstmt('zl2hent'), {'z': 'j', 'A': PFX('j'), 'D': HP0})
    pfm = s([s([hj, op], 'jca', ante_of(ZH)[0]), w.inst('zl2hent')], 'syl', HOLF(PFM, HP0))
    GG = '( b e. %s |-> ( ( %s ` b ) x. ( %s ` b ) ) )' % (HP0, PFM, EP)
    HM = tsub(zstmt('holmul'), {'F': PFM, 'G': EP, 'D': HP0, 'z': 'b'})
    gg = s([s([pfm, ephol], 'jca', ante_of(HM)[0]), w.inst('holmul')], 'syl', HOLF(GG, HP0))
    # agreement on 1 < Re v
    Av = '( ( %s /\\ v e. %s ) /\\ 1 < ( Re ` v ) )' % (A0, HP0)
    sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    Lv = lambda st: lift(w, st, Av)
    vh = sv([], 'simplr', 'v e. %s' % HP0); v1 = sv([], 'simpr', '1 < ( Re ` v )')
    vc = sv([sv([vh, sv([sv([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( v e. %s <-> ( v e. CC /\\ 0 < ( Re ` v ) ) )' % HP0)], 'mpbid', '( v e. CC /\\ 0 < ( Re ` v ) )'), w.inst('simpl')],
            'syl', 'v e. CC')
    zv = sv([vc, v1], 'jca', '( v e. CC /\\ 1 < ( Re ` v ) )')

    def dser(nxst, Ee):
        DS = ante_of(tsub(zstmt('zl1dser'), {'N': Ee[0], 'X': Ee[1]}))[1]
        body = DS[len('A. s e. %s ' % HP0):]
        inst = tsub(body, {'s': 'v'})
        eq = w.wcongr(body, {'s': 'v'}, 's = v', {'s': w.s([], 'id', '( s = v -> s = v )')})[0]
        al = sv([Lv(nxst), w.inst('zl1dser')], 'syl', DS)
        imp = sv([eq, al, vh], 'rspcdva', inst)
        return sv([v1, imp], 'mpd', inst.split(' -> ', 1)[1][:-2])
    ev = dser(nx, ('N', 'X'))
    epv = dser(mx, (M_, PRIM))
    DSX = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) )' % CX
    SAF = tsub(ante_of(zstmt('zl2dsp'))[1].split(' = ', 1)[1], {'Z': 'v'})
    dsp = sv([sv([Lv(nx), zv], 'jca', '( %s /\\ ( v e. CC /\\ 1 < ( Re ` v ) ) )' % NX), w.inst('zl2dsp')], 'syl', '%s = %s' % (DSX, SAF))
    SCY = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) )' % CY
    AFS = SAF[2:].split(' x. %s' % SCY, 1)[0]
    assert SAF == '( %s x. %s )' % (AFS, SCY), SAF
    dpf = sv([sv([Lv(nx), vc], 'jca', '( %s /\\ v e. CC )' % NX), w.inst('zl2dpf')], 'syl', '%s = %s' % (AFS, PFX('v')))
    V1 = '( v - 1 )'
    ev2 = sv([ev, sv([sv([dsp, sv([dpf], 'oveq1d', '%s = ( %s x. %s )' % (SAF, PFX('v'), SCY))], 'eqtrd', '%s = ( %s x. %s )' % (DSX, PFX('v'), SCY))], 'oveq2d',
                     '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (V1, DSX, V1, PFX('v'), SCY))], 'eqtrd', '( %s ` v ) = ( %s x. ( %s x. %s ) )' % (EN, V1, PFX('v'), SCY))
    gv, _ = _cg.mptval(w, Av, 'b', HP0, '( ( %s ` b ) x. ( %s ` b ) )' % (PFM, EP), 'v', vh, exs=sv([w.s([], 'ovex', '( ( %s ` v ) x. ( %s ` v ) ) e. _V' % (PFM, EP))], 'a1i',
                                                                                                        '( ( %s ` v ) x. ( %s ` v ) ) e. _V' % (PFM, EP)), gen=w.g)
    pv, _ = _cg.mptval(w, Av, 'j', HP0, PFX('j'), 'v', vh, exs=sv([w.s([], 'sumex', '%s e. _V' % PFX('v'))], 'a1i', '%s e. _V' % PFX('v')), gen=w.g)
    gv2 = sv([gv, sv([pv, epv], 'oveq12d', '( ( %s ` v ) x. ( %s ` v ) ) = ( %s x. ( %s x. %s ) )' % (PFM, EP, PFX('v'), V1, SCY))], 'eqtrd',
             '( %s ` v ) = ( %s x. ( %s x. %s ) )' % (GG, PFX('v'), V1, SCY))
    v1c = sv([vc, sv([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % V1)
    pfvc = sv([pv, sv([sv([Lv(s([pfm, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (PFM, HP0))), w.inst('cncff')], 'syl', '%s : %s --> CC' % (PFM, HP0)), vh], 'ffvelcdmd', '( %s ` v ) e. CC' % PFM)],
              'eqeltrrd', '%s e. CC' % PFX('v'))
    CH = tsub(zstmt('zl2chs'), {'N': M_, 'X': PRIM, 'Z': 'v'})
    chs = sv([sv([Lv(mx), zv], 'jca', ante_of(CH)[0]), w.inst('zl2chs')], 'syl', ante_of(CH)[1])
    zvc = sv([chs, w.inst('simpl')], 'syl', '%s e. CC' % SCY)
    m12 = sv([v1c, pfvc, zvc], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (V1, PFX('v'), SCY, PFX('v'), V1, SCY))
    egv = sv([sv([ev2, m12], 'eqtrd', '( %s ` v ) = ( %s x. ( %s x. %s ) )' % (EN, PFX('v'), V1, SCY)), sv([gv2], 'eqcomd', '( %s x. ( %s x. %s ) ) = ( %s ` v )' % (PFX('v'), V1, SCY, GG))],
             'eqtrd', '( %s ` v ) = ( %s ` v )' % (EN, GG))
    Av0 = '( %s /\\ v e. %s )' % (A0, HP0)
    agr = s([w.s([egv], 'ex', '( %s -> ( 1 < ( Re ` v ) -> ( %s ` v ) = ( %s ` v ) ) )' % (Av0, EN, GG))], 'ralrimiva', 'A. v e. %s ( 1 < ( Re ` v ) -> ( %s ` v ) = ( %s ` v ) )' % (HP0, EN, GG))
    HI = tsub(zstmt('hp0id'), {'F': EN, 'G': GG})
    hia, hic = ante_of(HI)
    hi = s([s([ehol, gg, agr], '3jca', hia), w.inst('hp0id')], 'syl', hic)
    BZ = '( %s ` z ) = ( %s ` z )' % (EN, GG)
    eqz = w.s([w.s([], 'fveq2', '( z = S -> ( %s ` z ) = ( %s ` S ) )' % (EN, EN)), w.s([], 'fveq2', '( z = S -> ( %s ` z ) = ( %s ` S ) )' % (GG, GG))], 'eqeq12d',
              '( z = S -> ( %s <-> ( %s ` S ) = ( %s ` S ) ) )' % (BZ, EN, GG))
    es = s([eqz, hi, sh], 'rspcdva', '( %s ` S ) = ( %s ` S )' % (EN, GG))
    gs, _ = _cg.mptval(w, A0, 'b', HP0, '( ( %s ` b ) x. ( %s ` b ) )' % (PFM, EP), 'S', sh, exs=s([w.s([], 'ovex', '( ( %s ` S ) x. ( %s ` S ) ) e. _V' % (PFM, EP))], 'a1i',
                                                                                                      '( ( %s ` S ) x. ( %s ` S ) ) e. _V' % (PFM, EP)), gen=w.g)
    ps, _ = _cg.mptval(w, A0, 'j', HP0, PFX('j'), 'S', sh, exs=s([w.s([], 'sumex', '%s e. _V' % PFX('S'))], 'a1i', '%s e. _V' % PFX('S')), gen=w.g)
    fin = s([s([es, gs], 'eqtrd', '( %s ` S ) = ( ( %s ` S ) x. ( %s ` S ) )' % (EN, PFM, EP)), s([ps], 'oveq1d', '( ( %s ` S ) x. ( %s ` S ) ) = ( %s x. ( %s ` S ) )' % (PFM, EP, PFX('S'), EP))],
            'eqtrd', SB['t21lfp'].split(' -> ', 1)[1][:-2])
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21lfp']))
    return go(w)


if __name__ == '__main__':
    gen_lfp()
