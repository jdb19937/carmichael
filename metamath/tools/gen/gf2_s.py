"""Sortie GF2, section S: the contour shift Re w = 1 -> Re w = -99/100 of the Gram integrand
GI ( w ) = HF ( w ) / ( w + S ), HF ( w ) = G1 ( w ) MH ( 1 + S + w ) E ( 1 + S + w )
(Lean Hfull, differentiableAt_Hfull, rectInt_Gfull_principal, gramInt_line_shift(_principal)).
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_s.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L
import gf1lib as G1L
from gf1lib import tsub, proj, holeq, HOL
from mvlib import ringeq, ringeqp

S_ = L.S
HPM1 = G1L.HPM1
HPZ = "( `' Re \" ( 0 (,) +oo ) )"
TOP = '( TopOpen ` CCfld )'
EHOL = '( E e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D E ) )' % (HPZ, HPZ)
SP = '( ( 1 + S ) + %s )'
G1w = lambda v: G1L.G1('A', 'B', 'L', v)
MHs = lambda v: G1L.MH('N', 'R', 'C', v)
HFB = lambda v: '( %s x. ( %s x. ( E ` %s ) ) )' % (G1w(v), MHs(SP % v), SP % v)
HFF = '( w e. %s |-> %s )' % (HPM1, HFB('w'))
HFH = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) /\\ ( ( N e. V /\\ R e. W ) /\\ C : NN --> CC ) ) /\\ '
       '( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ %s ) ) )' % EHOL)
S_['gf2hf'] = '( %s -> %s )' % (HFH, HOL(HFF, HPM1))


def hpm1mem(w, a, v, vm, sc, s0):
    """v e. HPM1 -> v e. CC , -u 1 < Re v , ( v + ( 1 + S ) ) e. HPZ"""
    st = mkst(w, a)
    e = st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ -u 1 < ( Re ` %s ) ) )' % (v, HPM1, v, v))
    e2 = st([vm, e], 'mpbid', '( %s e. CC /\\ -u 1 < ( Re ` %s ) )' % (v, v))
    vc = st([e2], 'simpld', '%s e. CC' % v); vlo = st([e2], 'simprd', '-u 1 < ( Re ` %s )' % v)
    V1 = '( %s + ( 1 + S ) )' % v
    c1 = st([st([], '1cnd', '1 e. CC'), sc], 'addcld', '( 1 + S ) e. CC')
    v1c = st([vc, c1], 'addcld', '%s e. CC' % V1)
    r1 = st([vc, c1], 'readdd', '( Re ` %s ) = ( ( Re ` %s ) + ( Re ` ( 1 + S ) ) )' % (V1, v))
    r2 = st([st([], '1cnd', '1 e. CC'), sc], 'readdd', '( Re ` ( 1 + S ) ) = ( ( Re ` 1 ) + ( Re ` S ) )')
    re1 = a1(w, a, w.s([w.s([], '1re', '1 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
    rv = st([vc], 'recld', '( Re ` %s ) e. RR' % v); rs = st([sc], 'recld', '( Re ` S ) e. RR')
    rv1 = st([v1c], 'recld', '( Re ` %s ) e. RR' % V1)
    r3 = st([r1, st([st([r2, st([re1], 'oveq1d', '( ( Re ` 1 ) + ( Re ` S ) ) = ( 1 + ( Re ` S ) )')], 'eqtrd', '( Re ` ( 1 + S ) ) = ( 1 + ( Re ` S ) )')], 'oveq2d',
                     '( ( Re ` %s ) + ( Re ` ( 1 + S ) ) ) = ( ( Re ` %s ) + ( 1 + ( Re ` S ) ) )' % (v, v))], 'eqtrd',
            '( Re ` %s ) = ( ( Re ` %s ) + ( 1 + ( Re ` S ) ) )' % (V1, v))
    pos = lin.linarith(w, a, [r3, vlo, s0], '0 < ( Re ` %s )' % V1, leaves={'( Re ` %s )' % v: rv, '( Re ` S )': rs, '( Re ` %s )' % V1: rv1})
    hz = st([st([v1c, pos], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (V1, V1)), st([st([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl',
                                                                                     '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (V1, HPZ, V1, V1))], 'mpbird', '%s e. %s' % (V1, HPZ))
    return vc, vlo, v1c, hz


def gf2hf():
    w = W('gf2hf', 'The numerator ` H ( w ) = G_1 ( w ) M_h ( 1 + S + w ) E ( 1 + S + w ) ` is holomorphic on ` Re w > -u 1 ` '
          '(Lean ` differentiableAt_Hfull ` ; ~ gf1g1h , ~ gf1mhh , the interface ` E ` on ` HP 0 ` , ~ z6hshift , ~ holmul ).')
    a = HFH; st = mkst(w, a)
    sc = proj(w, a, 'S e. CC'); s0 = proj(w, a, '0 <_ ( Re ` S )')
    g1h = st([st([proj(w, a, 'A e. RR'), proj(w, a, 'B e. RR')], 'jca', '( A e. RR /\\ B e. RR )'), proj(w, a, 'L e. RR+'), w.inst('gf1g1h')], 'syl2anc',
             tsub(split_imp(G1L.S['gf1g1h'])[1], {}))
    G1M = '( w e. %s |-> %s )' % (HPM1, G1w('w'))
    MHS = '( s e. CC |-> %s )' % MHs('s')
    mhh = st([proj(w, a, '( ( N e. V /\\ R e. W ) /\\ C : NN --> CC )'), w.inst('gf1mhh')], 'syl', HOL(MHS, 'CC'))
    uo = a1(w, a, w.s([], 'z6mstopn', '%s e. %s' % (HPM1, TOP)), '%s e. %s' % (HPM1, TOP))
    c1 = st([st([], '1cnd', '1 e. CC'), sc], 'addcld', '( 1 + S ) e. CC')
    Aw = '( %s /\\ w e. %s )' % (a, HPM1); tw = mkst(w, Aw)
    wc, wlo, w1c, whz = hpm1mem(w, Aw, 'w', tw([], 'simpr', 'w e. %s' % HPM1), lift(w, sc, Aw), lift(w, s0, Aw))
    rC = st([w1c], 'ralrimiva', 'A. w e. %s ( w + ( 1 + S ) ) e. CC' % HPM1)
    rE = st([whz], 'ralrimiva', 'A. w e. %s ( w + ( 1 + S ) ) e. %s' % (HPM1, HPZ))
    M2 = '( b e. %s |-> ( %s ` ( b + ( 1 + S ) ) ) )' % (HPM1, MHS)
    M3 = '( b e. %s |-> ( E ` ( b + ( 1 + S ) ) ) )' % HPM1
    h2 = st([mhh, st([uo, c1, rC], '3jca', '( %s e. %s /\\ ( 1 + S ) e. CC /\\ A. w e. %s ( w + ( 1 + S ) ) e. CC )' % (HPM1, TOP, HPM1)), w.inst('z6hshift')], 'syl2anc',
            HOL(M2, HPM1))
    eh = proj(w, a, EHOL)
    h3 = st([eh, st([uo, c1, rE], '3jca', '( %s e. %s /\\ ( 1 + S ) e. CC /\\ A. w e. %s ( w + ( 1 + S ) ) e. %s )' % (HPM1, TOP, HPM1, HPZ)), w.inst('z6hshift')], 'syl2anc',
            HOL(M3, HPM1))
    P23 = '( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (HPM1, M2, M3)
    h23 = st([h2, h3, w.inst('holmul')], 'syl2anc', HOL(P23, HPM1))
    idze = w.s([], 'id', '( z = e -> z = e )')
    cst, B23e = w.congr('( ( %s ` z ) x. ( %s ` z ) )' % (M2, M3), {'z': 'e'}, 'z = e', {'z': idze})
    P23e = '( e e. %s |-> %s )' % (HPM1, B23e)
    cb = a1(w, a, w.s([cst], 'cbvmptv', '%s = %s' % (P23, P23e)), '%s = %s' % (P23, P23e))
    h23e = st([h23, holeq(w, a, cb, P23, P23e, HPM1)], 'mpd', HOL(P23e, HPM1))
    P = '( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (HPM1, G1M, P23e)
    hp = st([g1h, h23e, w.inst('holmul')], 'syl2anc', HOL(P, HPM1))
    # P = HFF
    Az = '( %s /\\ z e. %s )' % (a, HPM1); tz = mkst(w, Az)
    zm = tz([], 'simpr', 'z e. %s' % HPM1)
    zc, zlo, z1c, zhz = hpm1mem(w, Az, 'z', zm, lift(w, sc, Az), lift(w, s0, Az))
    com = tz([zc, lift(w, c1, Az)], 'addcomd', '( z + ( 1 + S ) ) = %s' % (SP % 'z'))
    v1, _ = mpv(w, Az, 'w', HPM1, G1w('w'), 'z', zm)
    zp = '( z + ( 1 + S ) )'
    m2v, _ = mpv(w, Az, 'b', HPM1, '( %s ` ( b + ( 1 + S ) ) )' % MHS, 'z', zm)
    m2s, _ = mpv(w, Az, 's', 'CC', MHs('s'), zp, z1c, exs=w.s([w.s([], 'sumex', '%s e. _V' % MHs(zp))], 'a1i', '( %s -> %s e. _V )' % (Az, MHs(zp))))
    m3v, _ = mpv(w, Az, 'b', HPM1, '( E ` ( b + ( 1 + S ) ) )', 'z', zm)
    B23z = '( ( %s ` z ) x. ( %s ` z ) )' % (M2, M3)
    p23v, _ = mpv(w, Az, 'e', HPM1, B23e, 'z', zm)
    MZ = MHs(SP % 'z'); EZ = '( E ` %s )' % (SP % 'z')
    mr, mrv = w.rewrite(MHs(zp), {zp: (SP % 'z', com)}, Az)
    assert mrv == MZ, mrv
    e2 = tz([tz([m2v, m2s], 'eqtrd', '( %s ` z ) = %s' % (M2, MHs(zp))), mr], 'eqtrd', '( %s ` z ) = %s' % (M2, MZ))
    e3 = tz([m3v, tz([com], 'fveq2d', '( E ` %s ) = %s' % (zp, EZ))], 'eqtrd', '( %s ` z ) = %s' % (M3, EZ))
    e23 = tz([p23v, tz([e2, e3], 'oveq12d', '%s = ( %s x. %s )' % (B23z, MZ, EZ))], 'eqtrd', '( %s ` z ) = ( %s x. %s )' % (P23e, MZ, EZ))
    pb = tz([v1, e23], 'oveq12d', '( ( %s ` z ) x. ( %s ` z ) ) = %s' % (G1M, P23e, HFB('z')))
    pq = st([pb], 'mpteq2dva', '%s = ( z e. %s |-> %s )' % (P, HPM1, HFB('z')))
    idwz = w.s([], 'id', '( z = w -> z = w )')
    cst2, _ = w.congr(HFB('z'), {'z': 'w'}, 'z = w', {'z': idwz})
    pq2 = st([pq, a1(w, a, w.s([cst2], 'cbvmptv', '( z e. %s |-> %s ) = %s' % (HPM1, HFB('z'), HFF)), '( z e. %s |-> %s ) = %s' % (HPM1, HFB('z'), HFF))], 'eqtrd',
             '%s = %s' % (P, HFF))
    fin = st([hp, holeq(w, a, pq2, P, HFF, HPM1)], 'mpd', HOL(HFF, HPM1))
    w.qed([fin], 'idi', S_['gf2hf'])
    return w


TPI = '( 2 x. ( _i x. _pi ) )'
DI = '( %s \\ { -u S } )' % HPM1
GIB = lambda v: '( %s / ( %s - -u S ) )' % (HFB(v), v)
GI = '( w e. %s |-> %s )' % (DI, GIB('w'))
CLL = '-u ( ; 9 9 / ; ; 1 0 0 )'
YS = '( ( abs ` ( Im ` S ) ) + 1 )'
A0 = lambda T: '( %s + ( _i x. -u %s ) )' % (CLL, T)
B0 = lambda T: '( 1 + ( _i x. %s ) )' % T
RECT = lambda T: '( %s rectint <. %s , %s >. )' % (GI, A0(T), B0(T))
RES = '( %s x. %s )' % (TPI, HFB('-u S'))
RH = '( %s /\\ ( ( Re ` S ) <_ ( 1 / ; 5 0 ) /\\ ( T e. RR /\\ %s <_ T ) ) )' % (HFH, YS)
S_['gf2rect'] = '( %s -> %s = %s )' % (RH, RECT('T'), RES)


def gf2rect():
    w = W('gf2rect', 'The rectangle identity (Lean ` rectInt_Gfull_principal ` , every character): the boundary integral of ` GI = HF / ( w + S ) ` '
          'over ` [ -99/100 , 1 ] x [ -u T , T ] ` , ` T >_ | Im S | + 1 ` , is ` 2 pi i HF ( -u S ) ` (~ rectintcau with ~ gf2hf , ~ crectfrd , ~ rectinteqe ).')
    a = RH; st = mkst(w, a)
    sc = proj(w, a, 'S e. CC'); s0 = proj(w, a, '0 <_ ( Re ` S )'); s1 = proj(w, a, '( Re ` S ) <_ ( 1 / ; 5 0 )')
    tr = proj(w, a, 'T e. RR'); ty = proj(w, a, '%s <_ T' % YS)
    hf = st([proj(w, a, HFH), w.inst('gf2hf')], 'syl', HOL(HFF, HPM1))
    hfc = st([hf], 'simpld', '%s e. ( %s -cn-> CC )' % (HFF, HPM1)); hfd = st([hf], 'simprd', '%s C_ dom ( CC _D %s )' % (HPM1, HFF))
    rs = st([sc], 'recld', '( Re ` S ) e. RR'); is_ = st([sc], 'imcld', '( Im ` S ) e. RR')
    isc = st([is_], 'recnd', '( Im ` S ) e. CC')
    abs_ = st([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR')
    le1 = st([is_], 'leabsd', '( Im ` S ) <_ ( abs ` ( Im ` S ) )')
    nle = st([st([st([is_], 'renegcld', '-u ( Im ` S ) e. RR')], 'leabsd', '-u ( Im ` S ) <_ ( abs ` -u ( Im ` S ) )'), st([isc], 'absnegd', '( abs ` -u ( Im ` S ) ) = ( abs ` ( Im ` S ) )')],
             'breqtrd', '-u ( Im ` S ) <_ ( abs ` ( Im ` S ) )')
    LV = {'( Re ` S )': rs, '( Im ` S )': is_, '( abs ` ( Im ` S ) )': abs_, 'T': tr}
    lin_ = lambda hyps, goal: lin.linarith(w, a, hyps, goal, leaves=LV)
    c99 = litr(w, a, CLL)
    ntr = st([tr], 'renegcld', '-u T e. RR')
    ic = a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    A_, B_, P = A0('T'), B0('T'), '-u S'
    RC = '( %s crect %s )' % (A_, B_)
    a0c = st([st([c99], 'recnd', '%s e. CC' % CLL), st([ic, st([ntr], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % A_)
    b0c = st([st([], '1cnd', '1 e. CC'), st([ic, st([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % B_)
    pc = st([sc], 'negcld', '%s e. CC' % P)
    eq = {('Re', A_): (st([c99, ntr], 'crred', '( Re ` %s ) = %s' % (A_, CLL)), CLL), ('Im', A_): (st([c99, ntr], 'crimd', '( Im ` %s ) = -u T' % A_), '-u T'),
          ('Re', B_): (st([st([], '1red', '1 e. RR'), tr], 'crred', '( Re ` %s ) = 1' % B_), '1'), ('Im', B_): (st([st([], '1red', '1 e. RR'), tr], 'crimd', '( Im ` %s ) = T' % B_), 'T'),
          ('Re', P): (st([sc], 'renegd', '( Re ` %s ) = -u ( Re ` S )' % P), '-u ( Re ` S )'), ('Im', P): (st([sc], 'imnegd', '( Im ` %s ) = -u ( Im ` S )' % P), '-u ( Im ` S )')}
    H = [s0, s1, le1, nle, ty]

    def lt(k, X, Y):
        ex, vx = eq[(k, X)]; ey, vy = eq[(k, Y)]
        s0_ = lin_(H, '%s < %s' % (vx, vy))
        return st([st([ex, s0_], 'eqbrtrd', '( %s ` %s ) < %s' % (k, X, vy)), ey], 'breqtrrd', '( %s ` %s ) < ( %s ` %s )' % (k, X, k, Y))
    PIN = '( %s e. CC /\\ ( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) ) )' % (
        P, A_, P, P, B_, A_, P, P, B_)
    pin = st([pc, st([st([lt('Re', A_, P), lt('Re', P, B_)], 'jca', '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (A_, P, P, B_)),
                      st([lt('Im', A_, P), lt('Im', P, B_)], 'jca', '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (A_, P, P, B_))], 'jca', PIN[len('( %s e. CC /\\ ' % P):-2])],
             'jca', PIN)
    # the rectangle lies in HPM1
    b1 = '( %s /\\ u e. %s )' % (a, RC); t1 = mkst(w, b1)
    el = t1([lift(w, a0c, b1), lift(w, b0c, b1), w.inst('elcrect')], 'syl2anc',
            '( u e. %s <-> ( u e. CC /\\ ( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` u ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (RC, A_, B_, A_, B_))
    m3 = t1([t1([], 'simpr', 'u e. %s' % RC), el], 'mpbid', '( u e. CC /\\ ( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` u ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A_, B_, A_, B_))
    uc = t1([m3], 'simp1d', 'u e. CC')
    ra = t1([lift(w, a0c, b1)], 'recld', '( Re ` %s ) e. RR' % A_); rb = t1([lift(w, b0c, b1)], 'recld', '( Re ` %s ) e. RR' % B_)
    gl = t1([t1([ra], 'rexrd', '( Re ` %s ) e. RR*' % A_), t1([rb], 'rexrd', '( Re ` %s ) e. RR*' % B_), t1([m3], 'simp2d', '( Re ` u ) e. ( ( Re ` %s ) [,] ( Re ` %s ) )' % (A_, B_)),
             w.inst('iccgelb')], 'syl3anc', '( Re ` %s ) <_ ( Re ` u )' % A_)
    cl_ = t1([t1([lift(w, eq[('Re', A_)][0], b1)], 'eqcomd', '%s = ( Re ` %s )' % (CLL, A_)), gl], 'eqbrtrd', '%s <_ ( Re ` u )' % CLL)
    ru = t1([uc], 'recld', '( Re ` u ) e. RR')
    g1 = lin.linarith(w, b1, [cl_], '-u 1 < ( Re ` u )', leaves={'( Re ` u )': ru})
    uh = t1([t1([uc, g1], 'jca', '( u e. CC /\\ -u 1 < ( Re ` u ) )'), t1([t1([t1([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl',
                                                                           '( u e. %s <-> ( u e. CC /\\ -u 1 < ( Re ` u ) ) )' % HPM1)], 'mpbird', 'u e. %s' % HPM1)
    rch = st([w.s([uh], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (a, RC, HPM1))], 'ssrdv', '%s C_ %s' % (RC, HPM1))
    rcd = st([rch, hfd], 'sstrd', '%s C_ dom ( CC _D %s )' % (RC, HFF))
    cau = st([st([a0c, b0c], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), pin, st([hfc, rcd], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (HFF, HPM1, RC, HFF)),
              w.inst('rectintcau')], 'syl3anc', '( ( z e. ( %s \\ { %s } ) |-> ( ( %s ` z ) / ( z - %s ) ) ) rectint <. %s , %s >. ) = ( %s x. ( %s ` %s ) )' % (
        RC, P, HFF, P, A_, B_, TPI, HFF, P))
    # HFF ` P
    nrs_hi = lin_([s1], '-u 1 < -u ( Re ` S )')
    ph_ = st([st([pc, st([nrs_hi, eq[('Re', P)][0]], 'breqtrrd', '-u 1 < ( Re ` %s )' % P)], 'jca', '( %s e. CC /\\ -u 1 < ( Re ` %s ) )' % (P, P)),
              st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ -u 1 < ( Re ` %s ) ) )' % (P, HPM1, P, P))],
             'mpbird', '%s e. %s' % (P, HPM1))
    hpv, _ = mpv(w, a, 'w', HPM1, HFB('w'), P, ph_)
    cauk = st([cau, st([hpv], 'oveq2d', '( %s x. ( %s ` %s ) ) = %s' % (TPI, HFF, P, RES))], 'eqtrd',
              '( ( z e. ( %s \\ { %s } ) |-> ( ( %s ` z ) / ( z - %s ) ) ) rectint <. %s , %s >. ) = %s' % (RC, P, HFF, P, A_, B_, RES))
    CM = '( z e. ( %s \\ { %s } ) |-> ( ( %s ` z ) / ( z - %s ) ) )' % (RC, P, HFF, P)
    # the frame
    FRAME = ('( ( ( %s cseg ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) ) u. ( ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) cseg %s ) ) u. '
             '( ( %s cseg ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) ) u. ( ( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) ) cseg %s ) ) )') % (A_, B_, A_, B_, A_, B_, B_, A_, B_, A_, B_, A_)
    E_ = '( %s \\ { %s , %s } )' % (RC, P, P)
    frm = st([st([a0c, b0c], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), pin, pin, w.inst('crectfrd')], 'syl3anc', '%s C_ %s' % (FRAME, E_))
    b2 = '( %s /\\ u e. %s )' % (a, E_); t2 = mkst(w, b2)
    e3 = t2([t2([], 'simpr', 'u e. %s' % E_), a1(w, b2, w.s([], 'eldifpr', '( u e. %s <-> ( u e. %s /\\ u =/= %s /\\ u =/= %s ) )' % (E_, RC, P, P)),
                                                  '( u e. %s <-> ( u e. %s /\\ u =/= %s /\\ u =/= %s ) )' % (E_, RC, P, P))], 'mpbid', '( u e. %s /\\ u =/= %s /\\ u =/= %s )' % (RC, P, P))
    urc = t2([e3], 'simp1d', 'u e. %s' % RC); unp = t2([e3], 'simp2d', 'u =/= %s' % P)
    uh2 = t2([lift(w, rch, b2), urc], 'sseldd', 'u e. %s' % HPM1)
    udi = t2([t2([uh2, unp], 'jca', '( u e. %s /\\ u =/= %s )' % (HPM1, P)), a1(w, b2, w.s([], 'eldifsn', '( u e. %s <-> ( u e. %s /\\ u =/= %s ) )' % (DI, HPM1, P)),
                                                                          '( u e. %s <-> ( u e. %s /\\ u =/= %s ) )' % (DI, HPM1, P))], 'mpbird', 'u e. %s' % DI)
    RCP = '( %s \\ { %s } )' % (RC, P)
    urcp = t2([t2([urc, unp], 'jca', '( u e. %s /\\ u =/= %s )' % (RC, P)), a1(w, b2, w.s([], 'eldifsn', '( u e. %s <-> ( u e. %s /\\ u =/= %s ) )' % (RCP, RC, P)),
                                                                        '( u e. %s <-> ( u e. %s /\\ u =/= %s ) )' % (RCP, RC, P))], 'mpbird', 'u e. %s' % RCP)
    giv, _ = mpv(w, b2, 'w', DI, GIB('w'), 'u', udi)
    cmv, _ = mpv(w, b2, 'z', RCP, '( ( %s ` z ) / ( z - %s ) )' % (HFF, P), 'u', urcp)
    hfu, _ = mpv(w, b2, 'w', HPM1, HFB('w'), 'u', uh2)
    pw = t2([giv, t2([cmv, t2([hfu], 'oveq1d', '( ( %s ` u ) / ( u - %s ) ) = %s' % (HFF, P, GIB('u')))], 'eqtrd', '( %s ` u ) = %s' % (CM, GIB('u')))], 'eqtr4d',
            '( %s ` u ) = ( %s ` u )' % (GI, CM))
    ral = st([pw], 'ralrimiva', 'A. u e. %s ( %s ` u ) = ( %s ` u )' % (E_, GI, CM))
    cnex = a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V')
    hcc = a1(w, a, w.s([], 'hpss', '%s C_ CC' % HPM1), '%s C_ CC' % HPM1)
    dicc = st([st([], 'difssd', '%s C_ %s' % (DI, HPM1)), hcc], 'sstrd', '%s C_ CC' % DI)
    giv_ = st([st([cnex, dicc], 'ssexd', '%s e. _V' % DI)], 'mptexd', '%s e. _V' % GI)
    rcc = st([a0c, b0c, w.inst('crectss')], 'syl2anc', '%s C_ CC' % RC)
    cmv_ = st([st([cnex, st([st([], 'difssd', '%s C_ %s' % (RCP, RC)), rcc], 'sstrd', '%s C_ CC' % RCP)], 'ssexd', '%s e. _V' % RCP)], 'mptexd', '%s e. _V' % CM)
    req = st([st([st([a0c, b0c], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), frm], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ %s C_ %s )' % (A_, B_, FRAME, E_)),
              st([giv_, cmv_], 'jca', '( %s e. _V /\\ %s e. _V )' % (GI, CM)), ral, w.inst('rectinteqe')], 'syl3anc', '%s = ( %s rectint <. %s , %s >. )' % (RECT('T'), CM, A_, B_))
    w.qed([req, cauk], 'eqtrd', S_['gf2rect'])
    return w


GSH = '( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ ( 1 / ; 5 0 ) ) )'
STRD = ('( ( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 ) /\\ ( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 1 ) \\/ %s <_ ( abs ` ( Im ` z ) ) ) ) -> z e. %s )' % (CLL, CLL, YS, DI))
S_['gf2grsd'] = '( %s -> A. z e. CC %s )' % (GSH, STRD)


def gf2grsd():
    w = W('gf2grsd', 'The strip hypothesis ` STRIPD ` of ~ z6shift for ` GI ` : the lines ` Re w = -99/100 ` , ` Re w = 1 ` and the horizontal edges at '
          'heights ` >_ | Im S | + 1 ` avoid the pole ` -u S ` and lie in ` Re w > -1 ` .')
    a = GSH
    H = split_imp(STRD)[0]
    c0 = '( %s /\\ z e. CC )' % a
    c = '( %s /\\ %s )' % (c0, H); t = mkst(w, c)
    zc = proj(w, c, 'z e. CC'); sc = proj(w, c, 'S e. CC'); s0 = proj(w, c, '0 <_ ( Re ` S )'); s1 = proj(w, c, '( Re ` S ) <_ ( 1 / ; 5 0 )')
    cl_ = proj(w, c, '%s <_ ( Re ` z )' % CLL)
    D = '( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 1 ) \\/ %s <_ ( abs ` ( Im ` z ) ) )' % (CLL, YS)
    dst = proj(w, c, D)
    rs = t([sc], 'recld', '( Re ` S ) e. RR')
    isr = t([sc], 'imcld', '( Im ` S ) e. RR'); isc = t([isr], 'recnd', '( Im ` S ) e. CC')
    ais = t([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR')
    rz = t([zc], 'recld', '( Re ` z ) e. RR')
    # z e. HPM1
    m1 = lin.linarith(w, c, [cl_], '-u 1 < ( Re ` z )', leaves={'( Re ` z )': rz})
    zh = t([t([zc, m1], 'jca', '( z e. CC /\\ -u 1 < ( Re ` z ) )'), t([t([t([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl',
                                                                     '( z e. %s <-> ( z e. CC /\\ -u 1 < ( Re ` z ) ) )' % HPM1)], 'mpbird', 'z e. %s' % HPM1)
    # z =/= -u S
    c2 = '( %s /\\ z = -u S )' % c; t2 = mkst(w, c2)
    zv = t2([], 'simpr', 'z = -u S')
    rze = t2([t2([zv], 'fveq2d', '( Re ` z ) = ( Re ` -u S )'), t2([lift(w, sc, c2)], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')], 'eqtrd', '( Re ` z ) = -u ( Re ` S )')
    ize = t2([t2([t2([zv], 'fveq2d', '( Im ` z ) = ( Im ` -u S )'), t2([lift(w, sc, c2)], 'imnegd', '( Im ` -u S ) = -u ( Im ` S )')], 'eqtrd', '( Im ` z ) = -u ( Im ` S )')], 'fveq2d',
             '( abs ` ( Im ` z ) ) = ( abs ` -u ( Im ` S ) )')
    iza = t2([ize, t2([lift(w, isc, c2)], 'absnegd', '( abs ` -u ( Im ` S ) ) = ( abs ` ( Im ` S ) )')], 'eqtrd', '( abs ` ( Im ` z ) ) = ( abs ` ( Im ` S ) )')
    izr = t2([t2([t2([lift(w, zc, c2)], 'imcld', '( Im ` z ) e. RR')], 'recnd', '( Im ` z ) e. CC')], 'abscld', '( abs ` ( Im ` z ) ) e. RR')
    L = {'( Re ` S )': lift(w, rs, c2), '( abs ` ( Im ` S ) )': lift(w, ais, c2), '( Re ` z )': lift(w, rz, c2), '( abs ` ( Im ` z ) )': izr}
    lo = lin.linarith(w, c2, [rze, lift(w, s1, c2)], '%s < ( Re ` z )' % CLL, leaves=L)
    hi = lin.linarith(w, c2, [rze, lift(w, s0, c2)], '( Re ` z ) < 1', leaves=L)
    im = lin.linarith(w, c2, [iza], '( abs ` ( Im ` z ) ) < %s' % YS, leaves=L)
    n1 = t2([t2([t2([lo], 'ltned', '%s =/= ( Re ` z )' % CLL)], 'necomd', '( Re ` z ) =/= %s' % CLL)], 'neneqd', '-. ( Re ` z ) = %s' % CLL)
    n2 = t2([t2([hi], 'ltned', '( Re ` z ) =/= 1')], 'neneqd', '-. ( Re ` z ) = 1')
    ysr = t2([lift(w, ais, c2), t2([], '1red', '1 e. RR')], 'readdcld', '%s e. RR' % YS)
    n3 = t2([im, t2([izr, ysr], 'ltnled', '( ( abs ` ( Im ` z ) ) < %s <-> -. %s <_ ( abs ` ( Im ` z ) ) )' % (YS, YS))], 'mpbid', '-. %s <_ ( abs ` ( Im ` z ) )' % YS)
    D1 = '( ( Re ` z ) = %s \\/ ( Re ` z ) = 1 )' % CLL
    nd1 = t2([t2([n1, n2], 'jca', '( -. ( Re ` z ) = %s /\\ -. ( Re ` z ) = 1 )' % CLL), a1(w, c2, w.s([], 'ioran', '( -. %s <-> ( -. ( Re ` z ) = %s /\\ -. ( Re ` z ) = 1 ) )' % (D1, CLL)),
                                                                                         '( -. %s <-> ( -. ( Re ` z ) = %s /\\ -. ( Re ` z ) = 1 ) )' % (D1, CLL))], 'mpbird', '-. %s' % D1)
    nd = t2([t2([nd1, n3], 'jca', '( -. %s /\\ -. %s <_ ( abs ` ( Im ` z ) ) )' % (D1, YS)), a1(w, c2, w.s([], 'ioran', '( -. %s <-> ( -. %s /\\ -. %s <_ ( abs ` ( Im ` z ) ) ) )' % (D, D1, YS)),
                                                                                          '( -. %s <-> ( -. %s /\\ -. %s <_ ( abs ` ( Im ` z ) ) ) )' % (D, D1, YS))], 'mpbird', '-. %s' % D)
    nz = w.s([lift(w, dst, c2), nd], 'pm2.65da', '( %s -> -. z = -u S )' % c)
    zn = t([nz], 'neqned', 'z =/= -u S')
    zdi = t([t([zh, zn], 'jca', '( z e. %s /\\ z =/= -u S )' % HPM1), a1(w, c, w.s([], 'eldifsn', '( z e. %s <-> ( z e. %s /\\ z =/= -u S ) )' % (DI, HPM1)),
                                                                       '( z e. %s <-> ( z e. %s /\\ z =/= -u S ) )' % (DI, HPM1))], 'mpbird', 'z e. %s' % DI)
    ex = w.s([zdi], 'ex', '( %s -> ( %s -> z e. %s ) )' % (c0, H, DI))
    w.qed([ex], 'ralrimiva', S_['gf2grsd'])
    return w


CBj = 'A. j e. NN ( abs ` ( C ` j ) ) <_ 1'
OMGN = '( 2 ^ ( # ` { p e. Prime | p || N } ) )'
CVXB = lambda v: ('( ( ; ; ; ; ; 2 0 0 0 0 0 x. %s ) x. ( ( ( ( N x. ( ( abs ` ( Im ` %s ) ) + 2 ) ) ^c if ( 1 <_ ( Re ` %s ) , 0 , ( ( 1 - ( Re ` %s ) ) / 2 ) ) ) '
                  'x. ( log ` ( N x. ( ( abs ` ( Im ` %s ) ) + 3 ) ) ) ) + ( 1 / ( abs ` ( %s - 1 ) ) ) ) )' % (OMGN, v, v, v, v, v))
CVXH = ('A. s e. %s ( ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` s ) /\\ ( Re ` s ) <_ 2 /\\ s =/= 1 ) -> ( abs ` ( ( E ` s ) / ( s - 1 ) ) ) <_ %s )' % (HPZ, CVXB('s')))
LSs = 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u s ) )'
DSER = 'A. s e. %s ( 1 < ( Re ` s ) -> ( E ` s ) = ( ( s - 1 ) x. %s ) )' % (HPZ, LSs)
EEs = '( ( exp ` ( B + L ) ) + ( exp ` ( A + L ) ) )'
HMNR = G1L.HM('N', 'R')
LB0 = '( ( ; ; ; ; ; 4 0 0 0 0 0 x. %s ) x. ( ( N x. ( ( abs ` ( Im ` S ) ) + 3 ) ) ^ 2 ) )' % OMGN
M5 = '( ( ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) x. %s ) x. ( %s x. %s ) )' % (EEs, LB0, HMNR)
E4 = lambda x: '( 2 ^c -u ( %s / 4 ) )' % x
E2 = lambda x: '( 2 ^c -u ( %s / 2 ) )' % x
MSH = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) ) /\\ L e. RR+ ) /\\ ( ( ( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) ) /\\ ( C : NN --> CC /\\ %s ) ) /\\ '
       '( ( %s /\\ ( %s /\\ %s ) ) /\\ %s ) ) )' % (CBj, EHOL, DSER, CVXH, GSH))
STRM = '( ( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 ) /\\ %s <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) )' % (CLL, YS, GI, M5, E4('( abs ` ( Im ` z ) )'))
S_['gf2grmaj'] = '( %s -> A. z e. CC %s )' % (MSH, STRM)


def gf2grmaj():
    w = W('gf2grmaj', 'The strip hypothesis ` STRIPM ` of ~ z6shift for ` GI ` (Lean ` norm_Gfull_le ` ): ` | GI ( z ) | <_ M5 2 ^ ( - | Im z | / 4 ) ` on '
          '` -99/100 <_ Re z <_ 1 ` , ` | Im z | >_ | Im S | + 1 ` (~ z6gstrip , ~ gf1kb , ~ gf1mhb , ~ z6lstrip , ~ pol2exp , ~ z6gmaj ).')
    a = MSH; st = mkst(w, a)
    H = split_imp(STRM)[0]
    c0 = '( %s /\\ z e. CC )' % a
    c = '( %s /\\ %s )' % (c0, H); t = mkst(w, c)
    P_ = lambda x: proj(w, c, x)
    zc = P_('z e. CC'); sc = P_('S e. CC'); s0 = P_('0 <_ ( Re ` S )'); s1 = P_('( Re ` S ) <_ ( 1 / ; 5 0 )')
    cl_ = P_('%s <_ ( Re ` z )' % CLL); zh = P_('( Re ` z ) <_ 1'); ys = P_('%s <_ ( abs ` ( Im ` z ) )' % YS)
    rs = t([sc], 'recld', '( Re ` S ) e. RR'); rz = t([zc], 'recld', '( Re ` z ) e. RR')
    isr = t([sc], 'imcld', '( Im ` S ) e. RR'); isc = t([isr], 'recnd', '( Im ` S ) e. CC')
    ais = t([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR'); ag0 = t([isc], 'absge0d', '0 <_ ( abs ` ( Im ` S ) )')
    izr = t([zc], 'imcld', '( Im ` z ) e. RR'); izc = t([izr], 'recnd', '( Im ` z ) e. CC')
    Y = '( abs ` ( Im ` z ) )'
    yr = t([izc], 'abscld', '%s e. RR' % Y); y0 = t([izc], 'absge0d', '0 <_ %s' % Y)
    L_ = {'( Re ` S )': rs, '( Re ` z )': rz, '( abs ` ( Im ` S ) )': ais, Y: yr}
    lin_ = lambda hyps, goal, lv=None: lin.linarith(w, c, hyps, goal, leaves=lv or L_)
    y1 = lin_([ys, ag0], '1 <_ %s' % Y)
    # z e. DI by gf2grsd, z =/= 0
    gsd = st([proj(w, a, GSH), w.inst('gf2grsd')], 'syl', 'A. z e. CC %s' % STRD)
    Hp = split_imp(STRD)[0]
    r19 = w.s([gsd], 'r19.21bi', '( %s -> %s )' % (c0, STRD))
    hp = t([t([cl_, zh], 'jca', '( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 )' % CLL), t([ys], 'olcd', '( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 1 ) \\/ %s <_ %s )' % (CLL, YS, Y))], 'jca', Hp)
    zdi = t([hp, lift(w, r19, c)], 'mpd', 'z e. %s' % DI)
    zh1 = t([zdi], 'eldifad', 'z e. %s' % HPM1)
    nsn = t([zdi], 'eldifbd', '-. z e. { -u S }')
    zns = t([w.s([nsn, w.s([], 'velsn', '( z e. { -u S } <-> z = -u S )')], 'sylnib', '( %s -> -. z = -u S )' % c)], 'neqned', 'z =/= -u S')
    # z =/= 0
    c2 = '( %s /\\ z = 0 )' % c; t2 = mkst(w, c2)
    iz0 = t2([t2([t2([t2([], 'simpr', 'z = 0')], 'fveq2d', '( Im ` z ) = ( Im ` 0 )'), a1(w, c2, w.s([], 'im0', '( Im ` 0 ) = 0'), '( Im ` 0 ) = 0')], 'eqtrd', '( Im ` z ) = 0')],
              'fveq2d', '%s = ( abs ` 0 )' % Y)
    iz00 = t2([iz0, a1(w, c2, w.s([], 'abs0', '( abs ` 0 ) = 0'), '( abs ` 0 ) = 0')], 'eqtrd', '%s = 0' % Y)
    L2_ = {Y: lift(w, yr, c2)}
    ylt = lin.linarith(w, c2, [iz00], '%s < 1' % Y, leaves=L2_)
    nle = t2([ylt, t2([lift(w, yr, c2), t2([], '1red', '1 e. RR')], 'ltnled', '( %s < 1 <-> -. 1 <_ %s )' % (Y, Y))], 'mpbid', '-. 1 <_ %s' % Y)
    z0n = t([w.s([lift(w, y1, c2), nle], 'pm2.65da', '( %s -> -. z = 0 )' % c)], 'neqned', 'z =/= 0')
    zlo1 = lin_([cl_], '-u 1 < ( Re ` z )')
    # the value of GI and its factorization
    gv, _ = mpv(w, c, 'w', DI, GIB('w'), 'z', zdi)
    AR = ( proj(w, c, 'A e. RR'), proj(w, c, 'B e. RR'), proj(w, c, 'L e. RR+') )
    g1v = t([t([t([AR[0], AR[1]], 'jca', '( A e. RR /\\ B e. RR )'), AR[2]], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ )'),
             t([zc, zlo1, z0n], '3jca', '( z e. CC /\\ -u 1 < ( Re ` z ) /\\ z =/= 0 )'), w.inst('gf1g1v')], 'syl2anc', '%s = ( ( _G ` z ) x. %s )' % (G1w('z'), G1L.KK('A', 'B', 'L', 'z')))
    W_ = SP % 'z'
    Gz = '( _G ` z )'; Kz = G1L.KK('A', 'B', 'L', 'z'); Mz = MHs(W_); Ez = '( E ` %s )' % W_; Dn = '( %s - 1 )' % W_
    Qz = '( %s / %s )' % (Ez, Dn)
    c1_ = t([t([], '1cnd', '1 e. CC'), sc], 'addcld', '( 1 + S ) e. CC')
    wc = t([c1_, zc], 'addcld', '%s e. CC' % W_)
    dq = ringeq(w, c, '( z - -u S )', Dn, Closure(w, c, {'S': sc, 'z': zc}))
    dn0 = t([dq, t([zc, t([sc], 'negcld', '-u S e. CC'), zns], 'subne0d', '( z - -u S ) =/= 0')], 'eqnetrrd', '%s =/= 0' % Dn)
    dnc = t([wc, t([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % Dn)
    zdg = t([t([zc, t([zlo1, z0n], 'jca', '( -u 1 < ( Re ` z ) /\\ z =/= 0 )')], 'jca', '( z e. CC /\\ ( -u 1 < ( Re ` z ) /\\ z =/= 0 ) )'), w.inst('z6rdg')], 'syl',
             'z e. ( CC \\ ( ZZ \\ NN ) )')
    gc = t([zdg, w.inst('gamcl')], 'syl', '%s e. CC' % Gz)
    rsz = t([c1_, zc], 'readdd', '( Re ` %s ) = ( ( Re ` ( 1 + S ) ) + ( Re ` z ) )' % W_)
    r2 = t([t([t([], '1cnd', '1 e. CC'), sc], 'readdd', '( Re ` ( 1 + S ) ) = ( ( Re ` 1 ) + ( Re ` S ) )'),
            t([a1(w, c, w.s([w.s([], '1re', '1 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'oveq1d', '( ( Re ` 1 ) + ( Re ` S ) ) = ( 1 + ( Re ` S ) )')],
           'eqtrd', '( Re ` ( 1 + S ) ) = ( 1 + ( Re ` S ) )')
    rw_ = t([rsz, t([r2], 'oveq1d', '( ( Re ` ( 1 + S ) ) + ( Re ` z ) ) = ( ( 1 + ( Re ` S ) ) + ( Re ` z ) )')], 'eqtrd', '( Re ` %s ) = ( ( 1 + ( Re ` S ) ) + ( Re ` z ) )' % W_)
    rwr = t([wc], 'recld', '( Re ` %s ) e. RR' % W_)
    L3 = dict(L_); L3['( Re ` %s )' % W_] = rwr
    w0 = lin_([rw_, s0, cl_], '0 <_ ( Re ` %s )' % W_, L3)
    w100 = lin_([rw_, s0, cl_], '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W_, L3)
    # E ( W ) e. CC : W e. HPZ
    wpos = lin_([rw_, s0, cl_], '0 < ( Re ` %s )' % W_, L3)
    whz = t([t([wc, wpos], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), t([t([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl',
                                                                                       '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (W_, HPZ, W_, W_))], 'mpbird', '%s e. %s' % (W_, HPZ))
    ecn = proj(w, c, 'E e. ( %s -cn-> CC )' % HPZ)
    ezc = t([t([ecn, w.inst('cncff')], 'syl', 'E : %s --> CC' % HPZ), whz], 'ffvelcdmd', '%s e. CC' % Ez)
    qc = t([ezc, dnc, dn0], 'divcld', '%s e. CC' % Qz)
    # MH bound (gf1mhb, with the k-binder)
    cbj = proj(w, c, CBj)
    idjk = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( C ` j ) = ( C ` k ) )')], 'fveq2d', '( j = k -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` k ) ) )')], 'breq1d',
               '( j = k -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` k ) ) <_ 1 ) )')
    CBk = 'A. k e. NN ( abs ` ( C ` k ) ) <_ 1'
    cbk = t([cbj, w.s([idjk], 'cbvralvw', '( %s <-> %s )' % (CBj, CBk))], 'sylib', CBk)
    mhb = t([t([P_('N e. NN'), P_('R e. RR')], 'jca', '( N e. NN /\\ R e. RR )'), t([P_('C : NN --> CC'), cbk], 'jca', '( C : NN --> CC /\\ %s )' % CBk),
             t([wc, w0], 'jca', '( %s e. CC /\\ 0 <_ ( Re ` %s ) )' % (W_, W_)), w.inst('gf1mhb')], 'syl3anc', '( %s e. CC /\\ ( abs ` %s ) <_ %s )' % (Mz, Mz, HMNR))
    mzc = t([mhb], 'simpld', '%s e. CC' % Mz); mb = t([mhb], 'simprd', '( abs ` %s ) <_ %s' % (Mz, HMNR))
    # KK bound
    kb0 = t([t([t([t([AR[0], AR[1]], 'jca', '( A e. RR /\\ B e. RR )'), t([P_('0 <_ A'), P_('0 <_ B')], 'jca', '( 0 <_ A /\\ 0 <_ B )')], 'jca',
                  '( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) )'), AR[2], zc, w.inst('gf1kb')], 'syl3anc', tsub(split_imp(G1L.S['gf1kb'])[1], {'W': 'z'}))],
            'simprd', '( ( Re ` z ) <_ 1 -> ( abs ` %s ) <_ %s )' % (Kz, EEs))
    kb = t([zh, kb0], 'mpd', '( abs ` %s ) <_ %s' % (Kz, EEs))
    kzc = t([kb, w.inst('z6absle')], 'syl', '%s e. CC' % Kz)
    # algebra: GIB ( z ) = ( Gz Kz ) ( Qz Mz )
    HB_ = HFB('z')
    e1 = t([t([t([g1v], 'oveq1d', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (G1w('z'), Mz, Ez, Gz, Kz, Mz, Ez))], 'oveq1d',
              '( %s / ( z - -u S ) ) = ( ( ( %s x. %s ) x. ( %s x. %s ) ) / ( z - -u S ) )' % (HB_, Gz, Kz, Mz, Ez)),
            t([dq], 'oveq2d', '( ( ( %s x. %s ) x. ( %s x. %s ) ) / ( z - -u S ) ) = ( ( ( %s x. %s ) x. ( %s x. %s ) ) / %s )' % (Gz, Kz, Mz, Ez, Gz, Kz, Mz, Ez, Dn))], 'eqtrd',
           '%s = ( ( ( %s x. %s ) x. ( %s x. %s ) ) / %s )' % (GIB('z'), Gz, Kz, Mz, Ez, Dn))
    GK = '( %s x. %s )' % (Gz, Kz); ME = '( %s x. %s )' % (Mz, Ez)
    gkc = t([gc, kzc], 'mulcld', '%s e. CC' % GK); mec = t([mzc, ezc], 'mulcld', '%s e. CC' % ME)
    e2 = t([gkc, mec, dnc, dn0], 'divassd', '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (GK, ME, Dn, GK, ME, Dn))
    e3 = t([mzc, ezc, dnc, dn0], 'divassd', '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (Mz, Ez, Dn, Mz, Ez, Dn))
    e4 = t([mzc, qc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (Mz, Qz, Qz, Mz))
    QM = '( %s x. %s )' % (Qz, Mz)
    e34 = t([e3, e4], 'eqtrd', '( %s / %s ) = %s' % (ME, Dn, QM))
    gval = t([t([e1, e2], 'eqtrd', '%s = ( %s x. ( %s / %s ) )' % (GIB('z'), GK, ME, Dn)), t([e34], 'oveq2d', '( %s x. ( %s / %s ) ) = ( %s x. %s )' % (GK, ME, Dn, GK, QM))], 'eqtrd',
             '%s = ( %s x. %s )' % (GIB('z'), GK, QM))
    PROD = '( ( ( abs ` %s ) x. ( abs ` %s ) ) x. ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Gz, Kz, Qz, Mz)
    ab = t([t([gkc, t([qc, mzc], 'mulcld', '%s e. CC' % QM)], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GK, QM, GK, QM)),
            t([t([gc, kzc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GK, Gz, Kz)), t([qc, mzc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (QM, Qz, Mz))],
              'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = %s' % (GK, QM, PROD))], 'eqtrd', '( abs ` ( %s x. %s ) ) = %s' % (GK, QM, PROD))
    agr = t([t([t([gv, gval], 'eqtrd', '( %s ` z ) = ( %s x. %s )' % (GI, GK, QM))], 'fveq2d', '( abs ` ( %s ` z ) ) = ( abs ` ( %s x. %s ) )' % (GI, GK, QM)), ab], 'eqtrd',
            '( abs ` ( %s ` z ) ) = %s' % (GI, PROD))
    # Gamma
    z3 = lin_([zh], '( Re ` z ) <_ 3')
    gb = t([zc, t([t([cl_, z3], 'jca', '( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 )' % CLL), y1], 'jca', '( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 ) /\\ 1 <_ %s )' % (CLL, Y)),
            w.inst('z6gstrip')], 'syl2anc', '( abs ` %s ) <_ ( ; ; ; 1 6 3 2 x. %s )' % (Gz, E2(Y)))
    # E ( W ) / ( W - 1 )
    IW = '( Im ` %s )' % W_; AIW = '( abs ` %s )' % IW
    iw1 = t([c1_, zc], 'imaddd', '%s = ( ( Im ` ( 1 + S ) ) + ( Im ` z ) )' % IW)
    iw2 = t([t([t([], '1cnd', '1 e. CC'), sc], 'imaddd', '( Im ` ( 1 + S ) ) = ( ( Im ` 1 ) + ( Im ` S ) )'),
             t([t([a1(w, c, w.s([], 'im1', '( Im ` 1 ) = 0'), '( Im ` 1 ) = 0')], 'oveq1d', '( ( Im ` 1 ) + ( Im ` S ) ) = ( 0 + ( Im ` S ) )'),
                t([isc], 'addlidd', '( 0 + ( Im ` S ) ) = ( Im ` S )')], 'eqtrd', '( ( Im ` 1 ) + ( Im ` S ) ) = ( Im ` S )')], 'eqtrd', '( Im ` ( 1 + S ) ) = ( Im ` S )')
    iw = t([iw1, t([iw2], 'oveq1d', '( ( Im ` ( 1 + S ) ) + ( Im ` z ) ) = ( ( Im ` S ) + ( Im ` z ) )')], 'eqtrd', '%s = ( ( Im ` S ) + ( Im ` z ) )' % IW)
    iwc = t([wc], 'imcld', '%s e. RR' % IW); iwcc = t([iwc], 'recnd', '%s e. CC' % IW)
    awr = t([iwcc], 'abscld', '%s e. RR' % AIW)
    dd_ = t([t([t([iw], 'oveq1d', '( %s - ( Im ` S ) ) = ( ( ( Im ` S ) + ( Im ` z ) ) - ( Im ` S ) )' % IW), t([isc, izc], 'pncan2d', '( ( ( Im ` S ) + ( Im ` z ) ) - ( Im ` S ) ) = ( Im ` z )')],
                'eqtrd', '( %s - ( Im ` S ) ) = ( Im ` z )' % IW)], 'fveq2d', '( abs ` ( %s - ( Im ` S ) ) ) = %s' % (IW, Y))
    t2d = t([dd_, t([iwcc, isc], 'abs2dif2d', '( abs ` ( %s - ( Im ` S ) ) ) <_ ( %s + ( abs ` ( Im ` S ) ) )' % (IW, AIW))], 'eqbrtrrd', '%s <_ ( %s + ( abs ` ( Im ` S ) ) )' % (Y, AIW))
    L4 = dict(L_); L4[AIW] = awr
    w1 = lin_([t2d, ys], '1 <_ %s' % AIW, L4)
    LH = '( ( ( N e. NN /\\ ( C : NN --> CC /\\ %s ) ) /\\ ( %s /\\ %s ) ) /\\ ( %s e. CC /\\ ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` %s ) /\\ 1 <_ %s ) ) )' % (CBj, DSER, CVXH, W_, W_, AIW)
    from gf1lib import build
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    LN = '( N x. ( %s + 3 ) )' % AIW
    lb = t([build(w, c, LH, {'N e. NN': P_('N e. NN'), 'C : NN --> CC': P_('C : NN --> CC'), CBj: cbj, DSER: P_(DSER), CVXH: P_(CVXH), '%s e. CC' % W_: wc,
                             '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W_: w100, '1 <_ %s' % AIW: w1}), w.inst('z6lstrip')], 'syl',
           '( abs ` %s ) <_ ( %s x. ( %s ^ 2 ) )' % (Qz, K4, LN))
    # ( N ( | Im W | + 3 ) ) ^ 2 <_ ( N ( | Im S | + 3 ) ) ^ 2 ( 1 + y ) ^ 2
    tri = t([t([iw], 'fveq2d', '%s = ( abs ` ( ( Im ` S ) + ( Im ` z ) ) )' % AIW), t([isc, izc], 'abstrid', '( abs ` ( ( Im ` S ) + ( Im ` z ) ) ) <_ ( ( abs ` ( Im ` S ) ) + %s )' % Y)],
            'eqbrtrd', '%s <_ ( ( abs ` ( Im ` S ) ) + %s )' % (AIW, Y))
    ASY = '( ( abs ` ( Im ` S ) ) x. %s )' % Y
    asy0 = t([ais, yr, ag0, y0], 'mulge0d', '0 <_ %s' % ASY)
    asyr = t([ais, yr], 'remulcld', '%s e. RR' % ASY)
    A3 = '( ( abs ` ( Im ` S ) ) + 3 )'; Y1 = '( 1 + %s )' % Y
    L5 = dict(L4); L5[ASY] = asyr
    lhs3 = '( %s + 3 )' % AIW
    u1 = lin.linarith(w, c, [tri, asy0, y0], '%s <_ ( %s x. %s )' % (lhs3, A3, Y1), leaves=L5, products=True)
    nr = t([P_('N e. NN')], 'nnred', 'N e. RR'); n0 = t([t([P_('N e. NN')], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N')
    three = a1(w, c, w.s([], '3re', '3 e. RR'), '3 e. RR')
    l3r = t([awr, three], 'readdcld', '%s e. RR' % lhs3)
    a3r = t([ais, three], 'readdcld', '%s e. RR' % A3); y1r = t([t([], '1red', '1 e. RR'), yr], 'readdcld', '%s e. RR' % Y1)
    ayr = t([a3r, y1r], 'remulcld', '( %s x. %s ) e. RR' % (A3, Y1))
    u2 = t([l3r, ayr, nr, n0, u1], 'lemul2ad', '( N x. %s ) <_ ( N x. ( %s x. %s ) )' % (lhs3, A3, Y1))
    NA = '( N x. %s )' % A3
    u3 = t([u2, t([t([nr], 'recnd', 'N e. CC'), t([a3r], 'recnd', '%s e. CC' % A3), t([y1r], 'recnd', '%s e. CC' % Y1)], 'mulassd',
                  '( %s x. %s ) = ( N x. ( %s x. %s ) )' % (NA, Y1, A3, Y1))], 'breqtrrd', '%s <_ ( %s x. %s )' % (LN, NA, Y1))
    RN = '( %s x. %s )' % (NA, Y1)
    lnr = t([nr, l3r], 'remulcld', '%s e. RR' % LN); rnr = t([t([nr, a3r], 'remulcld', '%s e. RR' % NA), y1r], 'remulcld', '%s e. RR' % RN)
    l30 = lin_([t([iwcc], 'absge0d', '0 <_ %s' % AIW)], '0 <_ %s' % lhs3, L4)
    ln0 = t([nr, l3r, n0, l30], 'mulge0d', '0 <_ %s' % LN)
    rn0 = lin.linarith(w, c, [u3, ln0], '0 <_ %s' % RN, leaves={LN: lnr, RN: rnr})
    sq = t([u3, t([lnr, rnr, ln0, rn0], 'le2sqd', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (LN, RN, LN, RN))], 'mpbid', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LN, RN))
    nac = t([t([nr, a3r], 'remulcld', '%s e. RR' % NA)], 'recnd', '%s e. CC' % NA)
    sqm = t([nac, t([y1r], 'recnd', '%s e. CC' % Y1)], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (RN, NA, Y1))
    sq2 = t([sq, sqm], 'breqtrd', '( %s ^ 2 ) <_ ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (LN, NA, Y1))
    from z6b_m import omgfacts
    rr_, ge1 = omgfacts(w, c, P_('N e. NN'))
    k4r = t([a1(w, c, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR'), rr_], 'remulcld', '%s e. RR' % K4)
    k40 = lin.linarith(w, c, [ge1], '0 <_ %s' % K4, leaves={OMGN: rr_})
    ln2 = t([lnr], 'resqcld', '( %s ^ 2 ) e. RR' % LN)
    na2 = t([t([nr, a3r], 'remulcld', '%s e. RR' % NA)], 'resqcld', '( %s ^ 2 ) e. RR' % NA); y12 = t([y1r], 'resqcld', '( %s ^ 2 ) e. RR' % Y1)
    sq3 = t([ln2, t([na2, y12], 'remulcld', '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) e. RR' % (NA, Y1)), k4r, k40, sq2], 'lemul2ad',
            '( %s x. ( %s ^ 2 ) ) <_ ( %s x. ( ( %s ^ 2 ) x. ( %s ^ 2 ) ) )' % (K4, LN, K4, NA, Y1))
    LB0Q = '( %s x. ( %s ^ 2 ) )' % (LB0, Y1)
    assert LB0 == '( %s x. ( %s ^ 2 ) )' % (K4, NA)
    sq4 = t([sq3, t([t([k4r], 'recnd', '%s e. CC' % K4), t([na2], 'recnd', '( %s ^ 2 ) e. CC' % NA), t([y12], 'recnd', '( %s ^ 2 ) e. CC' % Y1)], 'mulassd',
                    '( ( %s x. ( %s ^ 2 ) ) x. ( %s ^ 2 ) ) = ( %s x. ( ( %s ^ 2 ) x. ( %s ^ 2 ) ) )' % (K4, NA, Y1, K4, NA, Y1))], 'breqtrrd', '( %s x. ( %s ^ 2 ) ) <_ %s' % (K4, LN, LB0Q))
    AQ = '( abs ` %s )' % Qz
    aqr = t([qc], 'abscld', '%s e. RR' % AQ)
    vb = t([aqr, t([k4r, ln2], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (K4, LN)), t([t([k4r, na2], 'remulcld', '%s e. RR' % LB0), y12], 'remulcld', '%s e. RR' % LB0Q), lb, sq4],
           'letrd', '%s <_ %s' % (AQ, LB0Q))
    # pol2exp and the product
    pe = t([yr, y0, w.inst('pol2exp')], 'syl2anc', '( ( ( 1 + %s ) ^ 2 ) x. %s ) <_ ( ; ; 1 2 8 x. %s )' % (Y, E2(Y), E4(Y)))
    G_ = '( abs ` %s )' % Gz; X_ = '( abs ` %s )' % Kz; M_ = '( abs ` %s )' % Mz
    lr = t([AR[2]], 'rpred', 'L e. RR')
    eer = t([t([t([t([AR[1], lr], 'readdcld', '( B + L ) e. RR')], 'rpefcld', '( exp ` ( B + L ) ) e. RR+'),
                t([t([AR[0], lr], 'readdcld', '( A + L ) e. RR')], 'rpefcld', '( exp ` ( A + L ) ) e. RR+')], 'rpaddcld', '%s e. RR+' % EEs)], 'rpred', '%s e. RR' % EEs)
    mr = t([mzc], 'abscld', '%s e. RR' % M_)
    two = a1(w, c, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')
    e2r = t([t([two, t([t([yr], 'rehalfcld', '( %s / 2 ) e. RR' % Y)], 'renegcld', '-u ( %s / 2 ) e. RR' % Y)], 'rpcxpcld', '%s e. RR+' % E2(Y))], 'rpred', '%s e. RR' % E2(Y))
    e4r = t([t([two, t([t([yr, a1(w, c, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, c, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')], 'redivcld', '( %s / 4 ) e. RR' % Y)],
                       'renegcld', '-u ( %s / 4 ) e. RR' % Y)], 'rpcxpcld', '%s e. RR+' % E4(Y))], 'rpred', '%s e. RR' % E4(Y))
    # HM e. RR , 0 <_ HM (gf1hm)
    HMB = '( ( CTau ^ 2 ) x. ( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) )'
    hm = t([P_('N e. NN'), t([P_('R e. RR'), P_('1 <_ R')], 'jca', '( R e. RR /\\ 1 <_ R )'), w.inst('gf1hm')], 'syl2anc', '( 0 <_ %s /\\ %s <_ %s )' % (HMNR, HMNR, HMB))
    hm0 = t([hm], 'simpld', '0 <_ %s' % HMNR); hmle = t([hm], 'simprd', '%s <_ %s' % (HMNR, HMB))
    ct = a1(w, c, w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'), w.s([w.s([], '2re', '2 e. RR'), w.s([w.s([], '2nn0', '2 e. NN0'), num.nn0(w, 800)], 'nn0expcli',
                                                                                                              '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('reexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR')],
                       'eqeltri', 'CTau e. RR'), 'CTau e. RR')
    rp_ = t([P_('R e. RR'), lin_([P_('1 <_ R')], '0 < R', {'R': P_('R e. RR')})], 'elrpd', 'R e. RR+')
    hbr = t([t([ct], 'resqcld', '( CTau ^ 2 ) e. RR'), t([t([rp_, litr(w, c, '( ; ; 8 0 1 / ; ; 4 0 0 )')], 'rpcxpcld', '( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR+')], 'rpred',
                                                            '( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR')], 'remulcld', '%s e. RR' % HMB)
    brh = w.s([w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (HMNR, HMB, HMNR, HMB))
    hmx = t([t([hmle, brh], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (HMNR, HMB))], 'simpld', '%s e. RR*' % HMNR)
    hmr = t([t([hmx, hbr], 'jca', '( %s e. RR* /\\ %s e. RR )' % (HMNR, HMB)), t([hm0, hmle], 'jca', '( 0 <_ %s /\\ %s <_ %s )' % (HMNR, HMNR, HMB)), w.inst('xrrege0')],
            'syl2anc', '%s e. RR' % HMNR)
    # z6gmaj
    ee0 = t([t([t([t([AR[1], lr], 'readdcld', '( B + L ) e. RR')], 'rpefcld', '( exp ` ( B + L ) ) e. RR+'),
                t([t([AR[0], lr], 'readdcld', '( A + L ) e. RR')], 'rpefcld', '( exp ` ( A + L ) ) e. RR+')], 'rpaddcld', '%s e. RR+' % EEs)], 'rpge0d', '0 <_ %s' % EEs)
    lb0r = t([k4r, na2], 'remulcld', '%s e. RR' % LB0)
    lb00 = t([k4r, na2, k40, t([t([nr, a3r], 'remulcld', '%s e. RR' % NA)], 'sqge0d', '0 <_ ( %s ^ 2 )' % NA)], 'mulge0d', '0 <_ %s' % LB0)
    sub_ = {'G': G_, 'X': X_, 'V': AQ, 'M': M_, 'A': '; ; ; 1 6 3 2', 'E': E2(Y), 'K': EEs, 'B': LB0, 'Q': '( ( 1 + %s ) ^ 2 )' % Y, 'Z': HMNR, 'F': E4(Y)}
    GMA = ('( ( ( ( ( G e. RR /\\ 0 <_ G ) /\\ G <_ ( A x. E ) ) /\\ ( ( X e. RR /\\ 0 <_ X ) /\\ X <_ K ) ) /\\ ( ( ( V e. RR /\\ 0 <_ V ) /\\ V <_ ( B x. Q ) ) /\\ '
           '( ( M e. RR /\\ 0 <_ M ) /\\ M <_ Z ) ) ) /\\ ( ( ( ( A e. RR /\\ 0 <_ A ) /\\ K e. RR ) /\\ ( ( B e. RR /\\ 0 <_ B ) /\\ Z e. RR ) ) /\\ '
           '( ( E e. RR /\\ Q e. RR ) /\\ ( F e. RR /\\ ( Q x. E ) <_ ( ; ; 1 2 8 x. F ) ) ) ) )')
    GMC = '( ( G x. X ) x. ( V x. M ) ) <_ ( ( ( ( A x. ; ; 1 2 8 ) x. K ) x. ( B x. Z ) ) x. F )'
    fg = {}
    fg['%s e. RR' % G_] = t([gc], 'abscld', '%s e. RR' % G_); fg['0 <_ %s' % G_] = t([gc], 'absge0d', '0 <_ %s' % G_)
    fg['%s e. RR' % X_] = t([kzc], 'abscld', '%s e. RR' % X_); fg['0 <_ %s' % X_] = t([kzc], 'absge0d', '0 <_ %s' % X_)
    fg['%s e. RR' % AQ] = aqr; fg['0 <_ %s' % AQ] = t([qc], 'absge0d', '0 <_ %s' % AQ)
    fg['%s e. RR' % M_] = mr; fg['0 <_ %s' % M_] = t([mzc], 'absge0d', '0 <_ %s' % M_)
    fg['%s <_ ( ; ; ; 1 6 3 2 x. %s )' % (G_, E2(Y))] = gb
    fg['%s <_ %s' % (X_, EEs)] = kb
    fg['%s <_ ( %s x. ( ( 1 + %s ) ^ 2 ) )' % (AQ, LB0, Y)] = vb
    fg['%s <_ %s' % (M_, HMNR)] = mb
    fg['; ; ; 1 6 3 2 e. RR'] = a1(w, c, num.real(w, '; ; ; 1 6 3 2'), '; ; ; 1 6 3 2 e. RR')
    fg['0 <_ ; ; ; 1 6 3 2'] = a1(w, c, num.ge0_nat(w, 1632), '0 <_ ; ; ; 1 6 3 2')
    fg['%s e. RR' % EEs] = eer
    fg['%s e. RR' % LB0] = lb0r; fg['0 <_ %s' % LB0] = lb00
    fg['%s e. RR' % HMNR] = hmr
    fg['%s e. RR' % E2(Y)] = e2r; fg['( ( 1 + %s ) ^ 2 ) e. RR' % Y] = y12
    fg['%s e. RR' % E4(Y)] = e4r
    fg['( ( ( 1 + %s ) ^ 2 ) x. %s ) <_ ( ; ; 1 2 8 x. %s )' % (Y, E2(Y), E4(Y))] = pe
    gm = t([build(w, c, tsub(GMA, sub_), fg), w.inst('z6gmaj')], 'syl', tsub(GMC, sub_))
    fin = t([agr, gm], 'eqbrtrd', '( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (GI, M5, E4(Y)))
    ex = w.s([fin], 'ex', '( %s -> ( %s -> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) ) )' % (c0, H, GI, M5, E4(Y)))
    w.qed([ex], 'ralrimiva', S_['gf2grmaj'])
    return w


LIh = lambda G, c, t='h': '( %s lint <. ( %s + ( _i x. -u %s ) ) , ( %s + ( _i x. %s ) ) >. )' % (G, c, t, c, t)
VLhF = lambda G, c: '( h e. RR+ |-> %s )' % LIh(G, c)
VLh = lambda G, c: '( ~~>r ` %s )' % VLhF(G, c)
S_['gf2shiftr'] = '( %s -> ( %s - %s ) = %s )' % (MSH, VLh(GI, '1'), VLh(GI, CLL), RES)


def hmreal(w, c, P_):
    """( c -> HM e. RR ) (gf1hm, xrrege0)"""
    t = mkst(w, c)
    HMB = '( ( CTau ^ 2 ) x. ( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) )'
    hm = t([P_('N e. NN'), t([P_('R e. RR'), P_('1 <_ R')], 'jca', '( R e. RR /\\ 1 <_ R )'), w.inst('gf1hm')], 'syl2anc', '( 0 <_ %s /\\ %s <_ %s )' % (HMNR, HMNR, HMB))
    hm0 = t([hm], 'simpld', '0 <_ %s' % HMNR); hmle = t([hm], 'simprd', '%s <_ %s' % (HMNR, HMB))
    ct = a1(w, c, w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'), w.s([w.s([], '2re', '2 e. RR'), w.s([w.s([], '2nn0', '2 e. NN0'), num.nn0(w, 800)], 'nn0expcli',
                                                                                                              '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('reexpcl')], 'mp2an',
                                                                                         '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR')], 'eqeltri', 'CTau e. RR'), 'CTau e. RR')
    rp_ = t([P_('R e. RR'), lin.linarith(w, c, [P_('1 <_ R')], '0 < R', leaves={'R': P_('R e. RR')})], 'elrpd', 'R e. RR+')
    hbr = t([t([ct], 'resqcld', '( CTau ^ 2 ) e. RR'), t([t([rp_, litr(w, c, '( ; ; 8 0 1 / ; ; 4 0 0 )')], 'rpcxpcld', '( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR+')], 'rpred',
                                                            '( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR')], 'remulcld', '%s e. RR' % HMB)
    brh = w.s([w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (HMNR, HMB, HMNR, HMB))
    hmx = t([t([hmle, brh], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (HMNR, HMB))], 'simpld', '%s e. RR*' % HMNR)
    return t([t([hmx, hbr], 'jca', '( %s e. RR* /\\ %s e. RR )' % (HMNR, HMB)), t([hm0, hmle], 'jca', '( 0 <_ %s /\\ %s <_ %s )' % (HMNR, HMNR, HMB)), w.inst('xrrege0')],
             'syl2anc', '%s e. RR' % HMNR)


def gf2shiftr():
    w = W('gf2shiftr', 'The contour shift from ` Re w = 1 ` to ` Re w = -99/100 ` (Lean ` gramInt_line_shift ` and ` gramInt_line_shift_principal ` in one statement): '
          '~ z6shift with the rectangle identity ~ gf2rect , the strip ~ gf2grsd and the majorant ~ gf2grmaj .')
    a = MSH; st = mkst(w, a)
    P_ = lambda x: proj(w, a, x)
    sc = P_('S e. CC'); s0 = P_('0 <_ ( Re ` S )'); s1 = P_('( Re ` S ) <_ ( 1 / ; 5 0 )')
    c99 = litr(w, a, CLL)
    h1 = st([st([c99, st([], '1red', '1 e. RR')], 'jca', '( %s e. RR /\\ 1 e. RR )' % CLL), lin.linarith(w, a, [], '%s < 1' % CLL)], 'jca', '( ( %s e. RR /\\ 1 e. RR ) /\\ %s < 1 )' % (CLL, CLL))
    # GI continuous on DI
    HH = '( ( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) /\\ ( ( N e. NN /\\ R e. RR ) /\\ C : NN --> CC ) ) /\\ ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ %s ) ) )' % EHOL
    from gf1lib import build
    hf = st([build(w, a, HH, {x: P_(x) for x in ['A e. RR', 'B e. RR', 'L e. RR+', 'N e. NN', 'R e. RR', 'C : NN --> CC', 'S e. CC', '0 <_ ( Re ` S )', EHOL]}), w.inst('gf2hf')],
            'syl', HOL(HFF, HPM1))
    hfc = st([hf], 'simpld', '%s e. ( %s -cn-> CC )' % (HFF, HPM1))
    dih = a1(w, a, w.s([], 'difss', '%s C_ %s' % (DI, HPM1)), '%s C_ %s' % (DI, HPM1))
    hr = st([hfc, st([dih, w.inst('rescncf')], 'syl', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HFF, HPM1, HFF, DI, DI))], 'mpd',
            '( %s |` %s ) e. ( %s -cn-> CC )' % (HFF, DI, DI))
    HFD = '( w e. %s |-> %s )' % (DI, HFB('w'))
    hd = st([hr, st([st([dih, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (HFF, DI, HFD))], 'eleq1d',
                    '( ( %s |` %s ) e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (HFF, DI, DI, HFD, DI))], 'mpbid', '%s e. ( %s -cn-> CC )' % (HFD, DI))
    hcc = a1(w, a, w.s([], 'hpss', '%s C_ CC' % HPM1), '%s C_ CC' % HPM1)
    dicc = st([dih, hcc], 'sstrd', '%s C_ CC' % DI)
    ccs = a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    idd = st([dicc, ccs, w.inst('cncfmptid')], 'syl2anc', '( w e. %s |-> w ) e. ( %s -cn-> CC )' % (DI, DI))
    cs = st([st([sc], 'negcld', '-u S e. CC'), dicc, ccs, w.inst('cncfmptc')], 'syl3anc', '( w e. %s |-> -u S ) e. ( %s -cn-> CC )' % (DI, DI))
    DM = '( w e. %s |-> ( w - -u S ) )' % DI
    dmc = st([idd, cs], 'subcncf', '%s e. ( %s -cn-> CC )' % (DM, DI))
    aw = '( %s /\\ w e. %s )' % (a, DI); tw = mkst(w, aw)
    wdi = tw([], 'simpr', 'w e. %s' % DI)
    wc = tw([lift(w, dicc, aw), wdi], 'sseldd', 'w e. CC')
    wns = tw([w.s([tw([wdi], 'eldifbd', '-. w e. { -u S }'), w.s([], 'velsn', '( w e. { -u S } <-> w = -u S )')], 'sylnib', '( %s -> -. w = -u S )' % aw)], 'neqned', 'w =/= -u S')
    wd0 = tw([wc, tw([lift(w, sc, aw)], 'negcld', '-u S e. CC'), wns], 'subne0d', '( w - -u S ) =/= 0')
    wdm = tw([tw([tw([wc, tw([lift(w, sc, aw)], 'negcld', '-u S e. CC')], 'subcld', '( w - -u S ) e. CC'), wd0], 'jca', '( ( w - -u S ) e. CC /\\ ( w - -u S ) =/= 0 )'),
              w.s([], 'eldifsn', '( ( w - -u S ) e. ( CC \\ { 0 } ) <-> ( ( w - -u S ) e. CC /\\ ( w - -u S ) =/= 0 ) )')], 'sylibr', '( w - -u S ) e. ( CC \\ { 0 } )')
    dmf = w.s([wdm], 'fmpttd', '( %s -> %s : %s --> ( CC \\ { 0 } ) )' % (a, DM, DI))
    dmh = st([st([a1(w, a, w.s([], 'difss', '( CC \\ { 0 } ) C_ CC'), '( CC \\ { 0 } ) C_ CC'), dmc], 'jca', '( ( CC \\ { 0 } ) C_ CC /\\ %s e. ( %s -cn-> CC ) )' % (DM, DI)),
              w.inst('cncfcdm')], 'syl', '( %s e. ( %s -cn-> ( CC \\ { 0 } ) ) <-> %s : %s --> ( CC \\ { 0 } ) )' % (DM, DI, DM, DI))
    dmH = st([dmf, dmh], 'mpbird', '%s e. ( %s -cn-> ( CC \\ { 0 } ) )' % (DM, DI))
    gic = w.s([hd, dmH], 'divcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (a, GI, DI))
    # strips
    gsd = st([P_(GSH), w.inst('gf2grsd')], 'syl', 'A. z e. CC %s' % STRD)
    gmj = st([P_(MSH), w.inst('gf2grmaj')], 'syl', 'A. z e. CC %s' % STRM)
    # M5 e. RR , YS e. RR+
    from z6b_m import omgfacts
    rr_, ge1 = omgfacts(w, a, P_('N e. NN'))
    isc = st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')
    ais = st([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR')
    A3 = '( ( abs ` ( Im ` S ) ) + 3 )'
    NA = '( N x. %s )' % A3
    nar = st([st([P_('N e. NN')], 'nnred', 'N e. RR'), st([ais, a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'readdcld', '%s e. RR' % A3)], 'remulcld', '%s e. RR' % NA)
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    lb0r = st([st([a1(w, a, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR'), rr_], 'remulcld', '%s e. RR' % K4), st([nar], 'resqcld', '( %s ^ 2 ) e. RR' % NA)],
              'remulcld', '%s e. RR' % LB0)
    lr = st([P_('L e. RR+')], 'rpred', 'L e. RR')
    eer = st([st([st([st([P_('B e. RR'), lr], 'readdcld', '( B + L ) e. RR')], 'rpefcld', '( exp ` ( B + L ) ) e. RR+'),
                  st([st([P_('A e. RR'), lr], 'readdcld', '( A + L ) e. RR')], 'rpefcld', '( exp ` ( A + L ) ) e. RR+')], 'rpaddcld', '%s e. RR+' % EEs)], 'rpred', '%s e. RR' % EEs)
    m5r = st([st([a1(w, a, w.s([num.real(w, '; ; ; 1 6 3 2'), num.real(w, '; ; 1 2 8')], 'remulcli', '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR'), '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR'), eer], 'remulcld', '( ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) x. %s ) e. RR' % EEs),
              st([lb0r, hmreal(w, a, P_)], 'remulcld', '( %s x. %s ) e. RR' % (LB0, HMNR))], 'remulcld', '%s e. RR' % M5)
    ysp = st([st([ais, st([], '1red', '1 e. RR')], 'readdcld', '%s e. RR' % YS), lin.linarith(w, a, [st([isc], 'absge0d', '0 <_ ( abs ` ( Im ` S ) )')], '0 < %s' % YS,
                                                                                               leaves={'( abs ` ( Im ` S ) )': ais})], 'elrpd', '%s e. RR+' % YS)
    # RES e. CC
    nrs = lin.linarith(w, a, [s1], '-u 1 < -u ( Re ` S )', leaves={'( Re ` S )': st([sc], 'recld', '( Re ` S ) e. RR')})
    ph_ = st([st([st([sc], 'negcld', '-u S e. CC'), st([nrs, st([sc], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')], 'breqtrrd', '-u 1 < ( Re ` -u S )')], 'jca',
                 '( -u S e. CC /\\ -u 1 < ( Re ` -u S ) )'), st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl',
                                                              '( -u S e. %s <-> ( -u S e. CC /\\ -u 1 < ( Re ` -u S ) ) )' % HPM1)], 'mpbird', '-u S e. %s' % HPM1)
    hpv, _ = mpv(w, a, 'w', HPM1, HFB('w'), '-u S', ph_)
    hpc = st([hpv, st([st([hfc, w.inst('cncff')], 'syl', '%s : %s --> CC' % (HFF, HPM1)), ph_], 'ffvelcdmd', '( %s ` -u S ) e. CC' % HFF)], 'eqeltrrd', '%s e. CC' % HFB('-u S'))
    tpc = st([st([], '2cnd', '2 e. CC'), st([a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), a1(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')],
             'mulcld', '%s e. CC' % TPI)
    resc = st([tpc, hpc], 'mulcld', '%s e. CC' % RES)
    # the rectangle identity for every h >_ YS
    ah = '( %s /\\ h e. RR+ )' % a; th = mkst(w, ah)
    ahy = '( %s /\\ %s <_ h )' % (ah, YS); ty = mkst(w, ahy)
    hr_ = ty([ty([], 'simplr', 'h e. RR+')], 'rpred', 'h e. RR')
    HFHx = '( ( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) /\\ ( ( N e. NN /\\ R e. RR ) /\\ C : NN --> CC ) ) /\\ ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ %s ) ) )' % EHOL
    rh = '( %s /\\ ( ( Re ` S ) <_ ( 1 / ; 5 0 ) /\\ ( h e. RR /\\ %s <_ h ) ) )' % (HFHx, YS)
    ri = ty([ty([lift(w, build(w, a, HFHx, {x: P_(x) for x in ['A e. RR', 'B e. RR', 'L e. RR+', 'N e. NN', 'R e. RR', 'C : NN --> CC', 'S e. CC', '0 <_ ( Re ` S )', EHOL]}), ahy),
                 ty([lift(w, s1, ahy), ty([hr_, ty([], 'simpr', '%s <_ h' % YS)], 'jca', '( h e. RR /\\ %s <_ h )' % YS)], 'jca',
                    '( ( Re ` S ) <_ ( 1 / ; 5 0 ) /\\ ( h e. RR /\\ %s <_ h ) )' % YS)], 'jca', rh), w.inst('gf2rect')], 'syl', '%s = %s' % (RECT('h'), RES))
    rall = st([w.s([ri], 'ex', '( %s -> ( %s <_ h -> %s = %s ) )' % (ah, YS, RECT('h'), RES))], 'ralrimiva', 'A. h e. RR+ ( %s <_ h -> %s = %s )' % (YS, RECT('h'), RES))
    Z1 = '( ( %s e. RR /\\ 1 e. RR ) /\\ %s < 1 )' % (CLL, CLL)
    Z2 = '( ( %s e. ( %s -cn-> CC ) /\\ A. z e. CC %s ) /\\ ( ( %s e. RR /\\ %s e. RR+ ) /\\ A. z e. CC %s ) )' % (GI, DI, STRD, M5, YS, STRM)
    Z3 = '( %s e. CC /\\ A. h e. RR+ ( %s <_ h -> %s = %s ) )' % (RES, YS, RECT('h'), RES)
    z2 = st([st([gic, gsd], 'jca', '( %s e. ( %s -cn-> CC ) /\\ A. z e. CC %s )' % (GI, DI, STRD)), st([st([m5r, ysp], 'jca', '( %s e. RR /\\ %s e. RR+ )' % (M5, YS)), gmj], 'jca',
                                                                                                     '( ( %s e. RR /\\ %s e. RR+ ) /\\ A. z e. CC %s )' % (M5, YS, STRM))], 'jca', Z2)
    z3 = st([resc, rall], 'jca', Z3)
    fin = st([h1, z2, z3, w.inst('z6shift')], 'syl3anc', split_imp(S_['gf2shiftr'])[1])
    w.qed([fin], 'idi', S_['gf2shiftr'])
    return w


def gicont(w, a, P_):
    """( a -> GI e. ( DI -cn-> CC ) ) under an antecedent carrying MSH's facts"""
    st = mkst(w, a)
    sc = P_('S e. CC')
    from gf1lib import build
    # GI continuous on DI
    HH = '( ( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) /\\ ( ( N e. NN /\\ R e. RR ) /\\ C : NN --> CC ) ) /\\ ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ %s ) ) )' % EHOL
    from gf1lib import build
    hf = st([build(w, a, HH, {x: P_(x) for x in ['A e. RR', 'B e. RR', 'L e. RR+', 'N e. NN', 'R e. RR', 'C : NN --> CC', 'S e. CC', '0 <_ ( Re ` S )', EHOL]}), w.inst('gf2hf')],
            'syl', HOL(HFF, HPM1))
    hfc = st([hf], 'simpld', '%s e. ( %s -cn-> CC )' % (HFF, HPM1))
    dih = a1(w, a, w.s([], 'difss', '%s C_ %s' % (DI, HPM1)), '%s C_ %s' % (DI, HPM1))
    hr = st([hfc, st([dih, w.inst('rescncf')], 'syl', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HFF, HPM1, HFF, DI, DI))], 'mpd',
            '( %s |` %s ) e. ( %s -cn-> CC )' % (HFF, DI, DI))
    HFD = '( w e. %s |-> %s )' % (DI, HFB('w'))
    hd = st([hr, st([st([dih, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (HFF, DI, HFD))], 'eleq1d',
                    '( ( %s |` %s ) e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (HFF, DI, DI, HFD, DI))], 'mpbid', '%s e. ( %s -cn-> CC )' % (HFD, DI))
    hcc = a1(w, a, w.s([], 'hpss', '%s C_ CC' % HPM1), '%s C_ CC' % HPM1)
    dicc = st([dih, hcc], 'sstrd', '%s C_ CC' % DI)
    ccs = a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    idd = st([dicc, ccs, w.inst('cncfmptid')], 'syl2anc', '( w e. %s |-> w ) e. ( %s -cn-> CC )' % (DI, DI))
    cs = st([st([sc], 'negcld', '-u S e. CC'), dicc, ccs, w.inst('cncfmptc')], 'syl3anc', '( w e. %s |-> -u S ) e. ( %s -cn-> CC )' % (DI, DI))
    DM = '( w e. %s |-> ( w - -u S ) )' % DI
    dmc = st([idd, cs], 'subcncf', '%s e. ( %s -cn-> CC )' % (DM, DI))
    aw = '( %s /\\ w e. %s )' % (a, DI); tw = mkst(w, aw)
    wdi = tw([], 'simpr', 'w e. %s' % DI)
    wc = tw([lift(w, dicc, aw), wdi], 'sseldd', 'w e. CC')
    wns = tw([w.s([tw([wdi], 'eldifbd', '-. w e. { -u S }'), w.s([], 'velsn', '( w e. { -u S } <-> w = -u S )')], 'sylnib', '( %s -> -. w = -u S )' % aw)], 'neqned', 'w =/= -u S')
    wd0 = tw([wc, tw([lift(w, sc, aw)], 'negcld', '-u S e. CC'), wns], 'subne0d', '( w - -u S ) =/= 0')
    wdm = tw([tw([tw([wc, tw([lift(w, sc, aw)], 'negcld', '-u S e. CC')], 'subcld', '( w - -u S ) e. CC'), wd0], 'jca', '( ( w - -u S ) e. CC /\\ ( w - -u S ) =/= 0 )'),
              w.s([], 'eldifsn', '( ( w - -u S ) e. ( CC \\ { 0 } ) <-> ( ( w - -u S ) e. CC /\\ ( w - -u S ) =/= 0 ) )')], 'sylibr', '( w - -u S ) e. ( CC \\ { 0 } )')
    dmf = w.s([wdm], 'fmpttd', '( %s -> %s : %s --> ( CC \\ { 0 } ) )' % (a, DM, DI))
    dmh = st([st([a1(w, a, w.s([], 'difss', '( CC \\ { 0 } ) C_ CC'), '( CC \\ { 0 } ) C_ CC'), dmc], 'jca', '( ( CC \\ { 0 } ) C_ CC /\\ %s e. ( %s -cn-> CC ) )' % (DM, DI)),
              w.inst('cncfcdm')], 'syl', '( %s e. ( %s -cn-> ( CC \\ { 0 } ) ) <-> %s : %s --> ( CC \\ { 0 } ) )' % (DM, DI, DM, DI))
    dmH = st([dmf, dmh], 'mpbird', '%s e. ( %s -cn-> ( CC \\ { 0 } ) )' % (DM, DI))
    gic = w.s([hd, dmH], 'divcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (a, GI, DI))
    return gic


def m5ys(w, a, P_):
    """( a -> M5 e. RR ) , ( a -> YS e. RR+ )"""
    st = mkst(w, a)
    sc = P_('S e. CC')
    # M5 e. RR , YS e. RR+
    from z6b_m import omgfacts
    rr_, ge1 = omgfacts(w, a, P_('N e. NN'))
    isc = st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')
    ais = st([isc], 'abscld', '( abs ` ( Im ` S ) ) e. RR')
    A3 = '( ( abs ` ( Im ` S ) ) + 3 )'
    NA = '( N x. %s )' % A3
    nar = st([st([P_('N e. NN')], 'nnred', 'N e. RR'), st([ais, a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'readdcld', '%s e. RR' % A3)], 'remulcld', '%s e. RR' % NA)
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    lb0r = st([st([a1(w, a, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR'), rr_], 'remulcld', '%s e. RR' % K4), st([nar], 'resqcld', '( %s ^ 2 ) e. RR' % NA)],
              'remulcld', '%s e. RR' % LB0)
    lr = st([P_('L e. RR+')], 'rpred', 'L e. RR')
    eer = st([st([st([st([P_('B e. RR'), lr], 'readdcld', '( B + L ) e. RR')], 'rpefcld', '( exp ` ( B + L ) ) e. RR+'),
                  st([st([P_('A e. RR'), lr], 'readdcld', '( A + L ) e. RR')], 'rpefcld', '( exp ` ( A + L ) ) e. RR+')], 'rpaddcld', '%s e. RR+' % EEs)], 'rpred', '%s e. RR' % EEs)
    m5r = st([st([a1(w, a, w.s([num.real(w, '; ; ; 1 6 3 2'), num.real(w, '; ; 1 2 8')], 'remulcli', '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR'), '( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) e. RR'), eer], 'remulcld', '( ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) x. %s ) e. RR' % EEs),
              st([lb0r, hmreal(w, a, P_)], 'remulcld', '( %s x. %s ) e. RR' % (LB0, HMNR))], 'remulcld', '%s e. RR' % M5)
    ysp = st([st([ais, st([], '1red', '1 e. RR')], 'readdcld', '%s e. RR' % YS), lin.linarith(w, a, [st([isc], 'absge0d', '0 <_ ( abs ` ( Im ` S ) )')], '0 < %s' % YS,
                                                                                               leaves={'( abs ` ( Im ` S ) )': ais})], 'elrpd', '%s e. RR+' % YS)
    return m5r, ysp


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
