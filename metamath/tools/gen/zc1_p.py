"""Sortie ZC1: the principal character: its primitive character is 1 (prmcy1); E = EUF . E1 on the right half-plane (zc1prin)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
import zc1_c, zc1_n, zc1_o
from zc1_c import u1base, cx1val, U1, L1, CX1
from zc1_o import EUF, PFP, DN
import lin
lin.FASTPATH = True

U0 = '( 0g ` ( DChr ` N ) )'
PR = '( %s /\\ X = %s )' % (NX, U0)
COND = '( N DChrCond X )'
PRIM = '( N DChrPrim X )'
CY = '( a e. NN |-> ( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` a ) ) )' % (PRIM, COND)
CX = '( a e. NN |-> ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` a ) ) )'
S['prmcy1'] = '( ( %s /\\ K e. NN ) -> ( %s ` K ) = 1 )' % (PR, CY)
S['zc1prin'] = '( ( %s /\\ S e. %s ) -> ( %s ` S ) = ( %s x. ( %s ` S ) ) )' % (PR, HP0, E, EUF('N', 'S'), E1)


def PFX(z):
    return 'sum_ d e. %s ( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u %s ) )' % (DN, CY, z)


def gen_prmcy1():
    w = W('prmcy1', 'The primitive character of the principal character mod ` N ` is the character mod ` 1 ` : its values on ` NN ` are ` 1 ` ( ~ dchrcondeq1 , ~ dchrprimcl , ~ zc1x1 ).')
    A0 = '( %s /\\ K e. NN )' % PR
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pr = s([], 'simpl', PR); kn = s([], 'simpr', 'K e. NN')
    nx = s([pr, w.inst('simpl')], 'syl', NX); xu = s([pr, w.inst('simpr')], 'syl', 'X = %s' % U0)
    c1 = s([xu, s([nx, w.inst('dchrcondeq1')], 'syl', '( X = %s <-> %s = 1 )' % (U0, COND))], 'mpbid', '%s = 1' % COND)
    pc = s([nx, w.inst('dchrprimcl')], 'syl', '%s e. ( Base ` ( DChr ` %s ) )' % (PRIM, COND))
    pc1 = s([pc, s([s([s([c1], 'fveq2d', '( DChr ` %s ) = ( DChr ` 1 )' % COND)], 'fveq2d', '( Base ` ( DChr ` %s ) ) = ( Base ` ( DChr ` 1 ) )' % COND)], 'x', 'x') if False else
             s([s([c1], 'fveq2d', '( DChr ` %s ) = ( DChr ` 1 )' % COND)], 'fveq2d', '( Base ` ( DChr ` %s ) ) = ( Base ` ( DChr ` 1 ) )' % COND)], 'eleqtrd', '%s e. ( Base ` ( DChr ` 1 ) )' % PRIM)
    VAL = '( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` K ) )' % (PRIM, COND)
    vx = s([w.s([], 'fvex', '%s e. _V' % VAL)], 'a1i', '%s e. _V' % VAL)
    fv, _ = _cg.mptval(w, A0, 'a', 'NN', '( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` a ) )' % (PRIM, COND), 'K', kn, exs=vx, gen=w.g)
    zr = s([s([s([c1], 'fveq2d', '( Z/nZ ` %s ) = ( Z/nZ ` 1 )' % COND)], 'fveq2d', '( ZRHom ` ( Z/nZ ` %s ) ) = ( ZRHom ` ( Z/nZ ` 1 ) )' % COND)], 'fveq1d',
           '( ( ZRHom ` ( Z/nZ ` %s ) ) ` K ) = ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` K )' % COND)
    v2 = s([zr], 'fveq2d', '%s = ( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` K ) )' % (VAL, PRIM))
    x1 = s([s([pc1, s([kn], 'nnzd', 'K e. ZZ')], 'jca', '( %s e. ( Base ` ( DChr ` 1 ) ) /\\ K e. ZZ )' % PRIM), w.inst('zc1x1')], 'syl', '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` K ) ) = 1' % PRIM)
    w.qed([s([fv, v2], 'eqtrd', '( %s ` K ) = ( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` K ) )' % (CY, PRIM)), x1], 'eqtrd', S['prmcy1'])
    return run8(w)


def pfx_is_pfp(w, ante, pr_st, zc_st, z):
    """( ante -> PFX(z) = PFP(N, z) ) from pr_st : ( ante -> PR ), zc_st : ( ante -> z e. CC )"""
    Ad = '( %s /\\ d e. %s )' % (ante, DN)
    sd = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ad, f))
    dn = sd([sd([], 'simpr', 'd e. %s' % DN), w.inst('elrabi')], 'syl', 'd e. NN')
    cy = sd([sd([lift(w, pr_st, Ad), dn], 'jca', '( %s /\\ d e. NN )' % PR), w.inst('prmcy1')], 'syl', '( %s ` d ) = 1' % CY)
    mz = sd([sd([dn, w.inst('mucl')], 'syl', '( mmu ` d ) e. ZZ')], 'zcnd', '( mmu ` d ) e. CC')
    e = sd([sd([cy], 'oveq2d', '( ( mmu ` d ) x. ( %s ` d ) ) = ( ( mmu ` d ) x. 1 )' % CY), sd([mz], 'mulridd', '( ( mmu ` d ) x. 1 ) = ( mmu ` d )')], 'eqtrd', '( ( mmu ` d ) x. ( %s ` d ) ) = ( mmu ` d )' % CY)
    e2 = sd([e], 'oveq1d', '( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u %s ) ) = ( ( mmu ` d ) x. ( d ^c -u %s ) )' % (CY, z, z))
    return w.s([e2], 'sumeq2dv', '( %s -> %s = %s )' % (ante, PFX(z), PFP('N', z)))


def gen_zc1prin():
    w = W('zc1prin', 'For the principal character mod ` N ` , ` E = ( s - 1 ) L ( s , chi_0 ) ` is the Euler factor ` prod_ ( p || N ) ( 1 - p ^ -s ) ` times ` E1 = ( s - 1 ) zeta ( s ) ` on the right half-plane (Lean ` LFunctionTrivChar_eq_mul_riemannZeta ` ; ~ zl2dsp , ~ zl1dser , ~ hp0id , ~ euf1 ).')
    A0 = ante_of(S['zc1prin'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pr = s([], 'simpl', PR); sh = s([], 'simpr', 'S e. %s' % HP0)
    nx = s([pr, w.inst('simpl')], 'syl', NX)
    ub = u1base(w, A0)
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), ub], 'jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    ehol = s([nx, w.inst('zl1ehol')], 'syl', HOLF(E, HP0))
    e1hol = s([nx1, w.inst('zl1ehol')], 'syl', HOLF(E1, HP0))
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
    hj = s([cvj, dph], 'x', 'x') if False else None
    # HOL of PFJ on CC by rewriting PFW = PFJ
    cn1 = s([s([cvj], 'eqcomd', '%s = %s' % (PFJ, PFW)), s([dph, w.inst('simpl')], 'syl', '%s e. ( CC -cn-> CC )' % PFW)], 'eqeltrd', '%s e. ( CC -cn-> CC )' % PFJ)
    dm1 = s([s([dph, w.inst('simpr')], 'syl', 'CC C_ dom ( CC _D %s )' % PFW), s([s([s([cvj], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (PFW, PFJ))], 'dmeqd', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (PFW, PFJ))], 'x', 'x') if False else
            s([s([cvj], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (PFW, PFJ))], 'dmeqd', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (PFW, PFJ))], 'sseqtrd', 'CC C_ dom ( CC _D %s )' % PFJ)
    hj = s([cn1, dm1], 'jca', HOLF(PFJ, 'CC'))
    ZH = tsub(stmt('zl2hent'), {'z': 'j', 'A': PFX('j'), 'D': HP0})
    pfm = s([s([hj, op], 'jca', ante_of(ZH)[0]), w.inst('zl2hent')], 'syl', HOLF(PFM, HP0))
    GG = '( b e. %s |-> ( ( %s ` b ) x. ( %s ` b ) ) )' % (HP0, PFM, E1)
    HM = tsub(stmt('holmul'), {'F': PFM, 'G': E1, 'D': HP0, 'z': 'b'})
    gg = s([s([pfm, e1hol], 'jca', ante_of(HM)[0]), w.inst('holmul')], 'syl', HOLF(GG, HP0))
    # agreement on 1 < Re v
    Av = '( ( %s /\\ v e. %s ) /\\ 1 < ( Re ` v ) )' % (A0, HP0)
    sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    Lv = lambda st: lift(w, st, Av)
    vh = sv([], 'simplr', 'v e. %s' % HP0); v1 = sv([], 'simpr', '1 < ( Re ` v )')
    vc = sv([sv([vh, sv([sv([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( v e. %s <-> ( v e. CC /\\ 0 < ( Re ` v ) ) )' % HP0)], 'mpbid', '( v e. CC /\\ 0 < ( Re ` v ) )'), w.inst('simpl')],
            'syl', 'v e. CC')
    zv = sv([vc, v1], 'jca', '( v e. CC /\\ 1 < ( Re ` v ) )')
    def dser(nxst, Ee, CXe):
        DS = ante_of(tsub(stmt('zl1dser'), {'N': Ee[0], 'X': Ee[1]}))[1]
        body = DS[len('A. s e. %s ' % HP0):]
        inst = tsub(body, {'s': 'v'})
        eq = w.wcongr(body, {'s': 'v'}, 's = v', {'s': w.s([], 'id', '( s = v -> s = v )')})[0]
        al = sv([Lv(nxst), w.inst('zl1dser')], 'syl', DS)
        imp = sv([eq, al, vh], 'rspcdva', inst)
        return sv([v1, imp], 'mpd', inst.split(' -> ', 1)[1][:-2])
    ev = dser(nx, ('N', 'X'), CX)
    e1v = dser(nx1, ('1', U1), CX1)
    DSX = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) )' % CX
    SAF = tsub(ante_of(stmt('zl2dsp'))[1].split(' = ', 1)[1], {'Z': 'v'})
    dsp = sv([sv([Lv(nx), zv], 'jca', '( %s /\\ ( v e. CC /\\ 1 < ( Re ` v ) ) )' % NX), w.inst('zl2dsp')], 'syl', '%s = %s' % (DSX, SAF))
    AFS = SAF[2:].split(' x. sum_ k e. NN ( ( %s' % CY, 1)[0]
    SCY = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) )' % CY
    assert SAF == '( %s x. %s )' % (AFS, SCY), SAF
    dpf = sv([sv([Lv(nx), vc], 'jca', '( %s /\\ v e. CC )' % NX), w.inst('zl2dpf')], 'syl', '%s = %s' % (AFS, PFX('v')))
    # SCY = sum k ^c -u v ; DSX1 = sum k ^c -u v
    Avk = '( %s /\\ k e. NN )' % Av
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Avk)
    cyk = w.s([w.s([lift(w, lift(w, pr, Av), Avk), kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Avk, PR)), w.inst('prmcy1')], 'syl', '( %s -> ( %s ` k ) = 1 )' % (Avk, CY))
    kv = w.s([w.s([kn], 'nncnd', '( %s -> k e. CC )' % Avk), w.s([lift(w, vc, Avk)], 'negcld', '( %s -> -u v e. CC )' % Avk)], 'cxpcld', '( %s -> ( k ^c -u v ) e. CC )' % Avk)
    t1 = w.s([w.s([cyk], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u v ) ) = ( 1 x. ( k ^c -u v ) ) )' % (Avk, CY)), w.s([kv], 'mullidd', '( %s -> ( 1 x. ( k ^c -u v ) ) = ( k ^c -u v ) )' % Avk)],
             'eqtrd', '( %s -> ( ( %s ` k ) x. ( k ^c -u v ) ) = ( k ^c -u v ) )' % (Avk, CY))
    ZV = 'sum_ k e. NN ( k ^c -u v )'
    scy = sv([t1], 'sumeq2dv', '%s = %s' % (SCY, ZV))
    c1k, _ = cx1val(w, Av, Lv(ub))
    t2 = w.s([w.s([c1k], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u v ) ) = ( 1 x. ( k ^c -u v ) ) )' % (Avk, CX1)), w.s([kv], 'mullidd', '( %s -> ( 1 x. ( k ^c -u v ) ) = ( k ^c -u v ) )' % Avk)],
             'eqtrd', '( %s -> ( ( %s ` k ) x. ( k ^c -u v ) ) = ( k ^c -u v ) )' % (Avk, CX1))
    DSX1 = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u v ) )' % CX1
    sc1 = sv([t2], 'sumeq2dv', '%s = %s' % (DSX1, ZV))
    # E v = ( v - 1 ) ( PFX ( v ) ZV ) ; GG v = PFX ( v ) ( ( v - 1 ) ZV )
    V1 = '( v - 1 )'
    ev2 = sv([ev, sv([sv([dsp, sv([dpf, scy], 'oveq12d', '%s = ( %s x. %s )' % (SAF, PFX('v'), ZV))], 'eqtrd', '%s = ( %s x. %s )' % (DSX, PFX('v'), ZV))], 'oveq2d',
                     '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (V1, DSX, V1, PFX('v'), ZV))], 'eqtrd', '( %s ` v ) = ( %s x. ( %s x. %s ) )' % (E, V1, PFX('v'), ZV))
    e1v2 = sv([e1v, sv([sc1], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (V1, DSX1, V1, ZV))], 'eqtrd', '( %s ` v ) = ( %s x. %s )' % (E1, V1, ZV))
    gv, _ = _cg.mptval(w, Av, 'b', HP0, '( ( %s ` b ) x. ( %s ` b ) )' % (PFM, E1), 'v', vh, exs=sv([w.s([], 'ovex', '( ( %s ` v ) x. ( %s ` v ) ) e. _V' % (PFM, E1))], 'a1i',
                                                                                                        '( ( %s ` v ) x. ( %s ` v ) ) e. _V' % (PFM, E1)), gen=w.g)
    pv, _ = _cg.mptval(w, Av, 'j', HP0, PFX('j'), 'v', vh, exs=sv([w.s([], 'sumex', '%s e. _V' % PFX('v'))], 'a1i', '%s e. _V' % PFX('v')), gen=w.g)
    gv2 = sv([gv, sv([pv, e1v2], 'oveq12d', '( ( %s ` v ) x. ( %s ` v ) ) = ( %s x. ( %s x. %s ) )' % (PFM, E1, PFX('v'), V1, ZV))], 'eqtrd',
             '( %s ` v ) = ( %s x. ( %s x. %s ) )' % (GG, PFX('v'), V1, ZV))
    v1c = sv([vc, sv([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % V1)
    pfc = sv([sv([sv([sv([pfm, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (PFM, HP0)) if False else Lv(s([pfm, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (PFM, HP0))), w.inst('cncff')], 'syl',
                     '%s : %s --> CC' % (PFM, HP0)), vh], 'ffvelcdmd', '( %s ` v ) e. CC' % PFM)], 'x', 'x') if False else None
    pfvc = sv([pv, sv([sv([Lv(s([pfm, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (PFM, HP0))), w.inst('cncff')], 'syl', '%s : %s --> CC' % (PFM, HP0)), vh], 'ffvelcdmd', '( %s ` v ) e. CC' % PFM)],
              'eqeltrrd', '%s e. CC' % PFX('v'))
    zvc = sv([sv([sv([ZV], 'x', 'x') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    # ZV e. CC from e1v2: E1 v = ( v - 1 ) ZV in CC and v - 1 =/= 0; simpler: zetacvg series in CC via zl2chs at N = 1
    CH = tsub(stmt('zl2chs'), {'N': '1', 'X': U1, 'Z': 'v'})
    chs = sv([sv([Lv(nx1), zv], 'jca', ante_of(CH)[0]), w.inst('zl2chs')], 'syl', ante_of(CH)[1])
    zvc = sv([sc1, sv([chs, w.inst('simpl')], 'syl', '%s e. CC' % DSX1)], 'eqeltrrd', '%s e. CC' % ZV)
    m12 = sv([v1c, pfvc, zvc], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (V1, PFX('v'), ZV, PFX('v'), V1, ZV))
    egv = sv([sv([ev2, m12], 'eqtrd', '( %s ` v ) = ( %s x. ( %s x. %s ) )' % (E, PFX('v'), V1, ZV)), sv([gv2], 'eqcomd', '( %s x. ( %s x. %s ) ) = ( %s ` v )' % (PFX('v'), V1, ZV, GG))],
             'eqtrd', '( %s ` v ) = ( %s ` v )' % (E, GG))
    Av0 = '( %s /\\ v e. %s )' % (A0, HP0)
    agr = s([w.s([egv], 'ex', '( %s -> ( 1 < ( Re ` v ) -> ( %s ` v ) = ( %s ` v ) ) )' % (Av0, E, GG))], 'ralrimiva', 'A. v e. %s ( 1 < ( Re ` v ) -> ( %s ` v ) = ( %s ` v ) )' % (HP0, E, GG))
    HI = tsub(S['hp0id'], {'F': E, 'G': GG})
    hia, hic = ante_of(HI)
    hi = s([s([ehol, gg, agr], '3jca', hia), w.inst('hp0id')], 'syl', hic)
    BZ = '( %s ` z ) = ( %s ` z )' % (E, GG)
    eqz = w.s([w.s([], 'fveq2', '( z = S -> ( %s ` z ) = ( %s ` S ) )' % (E, E)), w.s([], 'fveq2', '( z = S -> ( %s ` z ) = ( %s ` S ) )' % (GG, GG))], 'eqeq12d',
              '( z = S -> ( %s <-> ( %s ` S ) = ( %s ` S ) ) )' % (BZ, E, GG))
    es = s([eqz, hi, sh], 'rspcdva', '( %s ` S ) = ( %s ` S )' % (E, GG))
    gs, _ = _cg.mptval(w, A0, 'b', HP0, '( ( %s ` b ) x. ( %s ` b ) )' % (PFM, E1), 'S', sh, exs=s([w.s([], 'ovex', '( ( %s ` S ) x. ( %s ` S ) ) e. _V' % (PFM, E1))], 'a1i',
                                                                                                      '( ( %s ` S ) x. ( %s ` S ) ) e. _V' % (PFM, E1)), gen=w.g)
    ps, _ = _cg.mptval(w, A0, 'j', HP0, PFX('j'), 'S', sh, exs=s([w.s([], 'sumex', '%s e. _V' % PFX('S'))], 'a1i', '%s e. _V' % PFX('S')), gen=w.g)
    scc = s([s([sh, s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( S e. %s <-> ( S e. CC /\\ 0 < ( Re ` S ) ) )' % HP0)], 'mpbid', '( S e. CC /\\ 0 < ( Re ` S ) )'),
             w.inst('simpl')], 'syl', 'S e. CC')
    pp = pfx_is_pfp(w, A0, pr, scc, 'S')
    eu = s([s([s([nx, w.inst('simpl')], 'syl', 'N e. NN'), scc], 'jca', '( N e. NN /\\ S e. CC )'), w.inst('euf1')], 'syl', '%s = %s' % (PFP('N', 'S'), EUF('N', 'S')))
    pe = s([s([ps, pp], 'eqtrd', '( %s ` S ) = %s' % (PFM, PFP('N', 'S'))), eu], 'eqtrd', '( %s ` S ) = %s' % (PFM, EUF('N', 'S')))
    fin = s([s([es, gs], 'eqtrd', '( %s ` S ) = ( ( %s ` S ) x. ( %s ` S ) )' % (E, PFM, E1)), s([pe], 'oveq1d', '( ( %s ` S ) x. ( %s ` S ) ) = ( %s x. ( %s ` S ) )' % (PFM, E1, EUF('N', 'S'), E1))],
            'eqtrd', S['zc1prin'].split(' -> ', 1)[1][:-2])
    w.lines.append('qed:%s:idi |- %s' % (fin, S['zc1prin']))
    return run8(w)


if __name__ == '__main__':
    gen_prmcy1()
    gen_zc1prin()
