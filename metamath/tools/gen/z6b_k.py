"""Sortie Z6b, section 3/5 kit: the product rule off a point (z6dvoff), H_1 holomorphic (z6hm), Gone (z6ff, z6ffv).
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_k.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp, lift, Closure
from z6a_e3 import conjs, build, unpack, c_
from z6a_mlib import cbvm, toqed, mpval, holeq, HOLG, c1, opnss, TOP
import lin
from lin import linarith

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def z6dvoff():
    w = W('z6dvoff', 'A product ` G x. H ` with ` G ` holomorphic on ` U ` and ` H ` continuous on ` U ` is differentiable wherever ` H ` is '
          '(~ dvmulbr pointwise, ~ offvalfv ).')
    a = ante('z6dvoff'); st = mkst(w, a)
    gcn = st([], 'simpll', 'G e. ( U -cn-> CC )'); ug = st([], 'simplr', 'U C_ dom ( CC _D G )')
    hcn = st([], 'simprl', 'H e. ( U -cn-> CC )'); vh = st([], 'simprr', 'V C_ dom ( CC _D H )')
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : U --> CC )' % a)
    hf = w.s([hcn, w.inst('cncff')], 'syl', '( %s -> H : U --> CC )' % a)
    ucc = w.s([gcn, w.inst('cncfrss')], 'syl', '( %s -> U C_ CC )' % a)
    b = '( %s /\\ y e. V )' % a; sb = mkst(w, b)
    L = lambda s_, f_: lift(w, s_, b)
    yv = sb([], 'simpr', 'y e. V')
    yh = sb([L(vh, 0), yv], 'sseldd', 'y e. dom ( CC _D H )')
    ccb = c_(w, b, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    hb = sb([ccb, L(hf, 0), L(ucc, 0)], 'dvbss', 'dom ( CC _D H ) C_ U')
    yu = sb([hb, yh], 'sseldd', 'y e. U')
    yg = sb([L(ug, 0), yu], 'sseldd', 'y e. dom ( CC _D G )')

    def br(Fn, ym):
        fun = w.s([w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (Fn, Fn)), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D %s )' % Fn)
        bi = w.s([fun, w.inst('funfvbrb')], 'ax-mp', '( y e. dom ( CC _D %s ) <-> y ( CC _D %s ) ( ( CC _D %s ) ` y ) )' % (Fn, Fn, Fn))
        return sb([ym, c_(w, b, bi, '( y e. dom ( CC _D %s ) <-> y ( CC _D %s ) ( ( CC _D %s ) ` y ) )' % (Fn, Fn, Fn))], 'mpbid',
                  'y ( CC _D %s ) ( ( CC _D %s ) ` y )' % (Fn, Fn))
    bg = br('G', yg); bh = br('H', yh)
    ej = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
    PR = '( G oF x. H )'
    mb = sb([L(gf, 0), L(ucc, 0), L(hf, 0), L(ucc, 0), ccb, bg, bh, ej], 'dvmulbr',
            'y ( CC _D %s ) ( ( ( ( CC _D G ) ` y ) x. ( H ` y ) ) + ( ( ( CC _D H ) ` y ) x. ( G ` y ) ) )' % PR)
    yd = sb([c_(w, b, w.s([], 'reldv', 'Rel ( CC _D %s )' % PR), 'Rel ( CC _D %s )' % PR), mb, w.inst('releldm')], 'syl2anc', 'y e. dom ( CC _D %s )' % PR)
    ss = st([w.s([yd], 'ex', '( %s -> ( y e. V -> y e. dom ( CC _D %s ) ) )' % (a, PR))], 'ssrdv', 'V C_ dom ( CC _D %s )' % PR)
    uv = st([c_(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), ucc], 'ssexd', 'U e. _V')
    MP_ = '( z e. U |-> ( ( G ` z ) x. ( H ` z ) ) )'
    of = st([uv, st([gf], 'ffnd', 'G Fn U'), st([hf], 'ffnd', 'H Fn U')], 'offvalfv', '%s = %s' % (PR, MP_))
    dd = st([st([of], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (PR, MP_))], 'dmeqd', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (PR, MP_))
    w.qed([ss, dd], 'sseqtrd', STATEMENTS['z6dvoff'])
    return w


def u5mem(w, Aw, v, sc):
    """( Aw -> v e. CC ) and ( Aw -> -u ( Re ` S ) < ( Re ` v ) ) from ( Aw -> v e. U5 ) (the simpr of Aw)"""
    t = mkst(w, Aw)
    vm = t([], 'simpr', '%s e. %s' % (v, U5))
    nr = t([t([sc], 'recld', '( Re ` S ) e. RR')], 'renegcld', '-u ( Re ` S ) e. RR')
    bi = t([nr, w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ -u ( Re ` S ) < ( Re ` %s ) ) )' % (v, U5, v, v))
    both = t([vm, bi], 'mpbid', '( %s e. CC /\\ -u ( Re ` S ) < ( Re ` %s ) )' % (v, v))
    return vm, t([both], 'simpld', '%s e. CC' % v), t([both], 'simprd', '-u ( Re ` S ) < ( Re ` %s )' % v)


def hpzpt(w, Aw, v, vc, vlo, sc, rev=False):
    """( Aw -> ( v + S ) e. HPZ ) (or ( S + v ) when rev)"""
    t = mkst(w, Aw)
    X = '( S + %s )' % v if rev else '( %s + S )' % v
    xc = t([sc, vc] if rev else [vc, sc], 'addcld', '%s e. CC' % X)
    rs = t([sc], 'recld', '( Re ` S ) e. RR'); rv = t([vc], 'recld', '( Re ` %s ) e. RR' % v)
    RX = '( ( Re ` S ) + ( Re ` %s ) )' % v if rev else '( ( Re ` %s ) + ( Re ` S ) )' % v
    re = t([sc, vc] if rev else [vc, sc], 'readdd', '( Re ` %s ) = %s' % (X, RX))
    gt = linarith(w, Aw, [vlo], '0 < %s' % RX, leaves={'( Re ` S )': rs, '( Re ` %s )' % v: rv})
    gt2 = t([gt, re], 'breqtrrd', '0 < ( Re ` %s )' % X)
    bi = t([c_(w, Aw, w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (X, HPZ, X, X))
    return t([t([xc, gt2], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (X, X)), bi], 'mpbird', '%s e. %s' % (X, HPZ))


def z6hm():
    w = W('z6hm', 'Lean ` differentiable_Hone ` : ` H_1 ( w ) = X ^ w E ( S + w ) M_r ( S + w ) ` is holomorphic on ` Re w > -u Re S ` '
          '(~ cxfhol , ~ z6mrhol , the interface ` E ` holomorphic on ` HP 0 ` , ~ z6hshift , ~ holmul ).')
    a = ante('z6hm'); f = unpack(w, a); st = mkst(w, a)
    sc = f['S e. CC']; dr = f['D e. RR']; d1 = f['1 < D']
    uo = c_(w, a, w.s([], 'z6mstopn', '%s e. %s' % (U5, TOP)), '%s e. %s' % (U5, TOP))
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1D); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2D); z12 = st([zz], 'simp3d', '%s < %s' % (Z1D, Z2D))
    HAB = sub(HAB0, {'A': Z1D, 'B': Z2D})
    hab = st([st([st([z1rp], 'rpred', '%s e. RR' % Z1D), st([z1rp], 'rpgt0d', '0 < %s' % Z1D)], 'jca', '( %s e. RR /\\ 0 < %s )' % (Z1D, Z1D)),
              st([st([z2rp], 'rpred', '%s e. RR' % Z2D), z12], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca', HAB)
    MS = '( s e. CC |-> %s )' % MRr('R', 's')
    mh = st([st([st([hab, f['R e. NN']], 'jca', '( %s /\\ R e. NN )' % HAB), f['C : NN --> CC']], 'jca', '( ( %s /\\ R e. NN ) /\\ C : NN --> CC )' % HAB),
             w.inst('z6mrhol')], 'syl', HOLG(MS, 'CC'))
    drp = st([dr, linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    xrp = st([drp, c_(w, a, __import__('num').real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % XPD)
    CX = '( c e. CC |-> ( %s ^c c ) )' % XPD
    xh = st([xrp, w.inst('cxfhol')], 'syl', HOLG(CX, 'CC'))
    # the shifts
    Aw = '( %s /\\ w e. %s )' % (a, U5)
    _, wc, wlo = u5mem(w, Aw, 'w', lift(w, sc, Aw))
    t = mkst(w, Aw)
    w0 = t([wc, c_(w, Aw, w.s([], '0cn', '0 e. CC'), '0 e. CC')], 'addcld', '( w + 0 ) e. CC')
    wS = t([wc, lift(w, sc, Aw)], 'addcld', '( w + S ) e. CC')
    r0 = st([w0], 'ralrimiva', 'A. w e. %s ( w + 0 ) e. CC' % U5)
    rS = st([wS], 'ralrimiva', 'A. w e. %s ( w + S ) e. CC' % U5)
    rE = st([hpzpt(w, Aw, 'w', wc, wlo, lift(w, sc, Aw))], 'ralrimiva', 'A. w e. %s ( w + S ) e. %s' % (U5, HPZ))
    zero = c_(w, a, w.s([], '0cn', '0 e. CC'), '0 e. CC')
    M1 = '( d e. %s |-> ( %s ` ( d + 0 ) ) )' % (U5, CX)
    M2 = '( d e. %s |-> ( E ` ( d + S ) ) )' % U5
    M3 = '( d e. %s |-> ( %s ` ( d + S ) ) )' % (U5, MS)
    h1 = st([xh, st([uo, zero, r0], '3jca', '( %s e. %s /\\ 0 e. CC /\\ A. w e. %s ( w + 0 ) e. CC )' % (U5, TOP, U5)), w.inst('z6hshift')], 'syl2anc', HOLG(M1, U5))
    eh = st([f['E e. ( %s -cn-> CC )' % HPZ], f['%s C_ dom ( CC _D E )' % HPZ]], 'jca', HOLG('E', HPZ))
    h2 = st([eh, st([uo, sc, rE], '3jca', '( %s e. %s /\\ S e. CC /\\ A. w e. %s ( w + S ) e. %s )' % (U5, TOP, U5, HPZ)), w.inst('z6hshift')], 'syl2anc', HOLG(M2, U5))
    h3 = st([mh, st([uo, sc, rS], '3jca', '( %s e. %s /\\ S e. CC /\\ A. w e. %s ( w + S ) e. CC )' % (U5, TOP, U5)), w.inst('z6hshift')], 'syl2anc', HOLG(M3, U5))
    P23 = '( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (U5, M2, M3)
    h23 = st([h2, h3, w.inst('holmul')], 'syl2anc', HOLG(P23, U5))
    cb, P23e = cbvm(w, a, 'z', 'e', U5, '( ( %s ` z ) x. ( %s ` z ) )' % (M2, M3))
    h23e = holeq(w, a, P23, P23e, U5, h23, cb)
    P = '( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (U5, M1, P23e)
    hp = st([h1, h23e, w.inst('holmul')], 'syl2anc', HOLG(P, U5))
    # the values
    Az = '( %s /\\ z e. %s )' % (a, U5)
    zm, zc, zlo = u5mem(w, Az, 'z', lift(w, sc, Az))
    tz = mkst(w, Az)
    scz = lift(w, sc, Az)
    v1, _ = mpval(w, Az, 'd', U5, '( %s ` ( d + 0 ) )' % CX, 'z', zm)
    z0 = tz([zc, c_(w, Az, w.s([], '0cn', '0 e. CC'), '0 e. CC')], 'addcld', '( z + 0 ) e. CC')
    v1b, _ = mpval(w, Az, 'c', 'CC', '( %s ^c c )' % XPD, '( z + 0 )', z0)
    v1c = tz([tz([zc], 'addridd', '( z + 0 ) = z')], 'oveq2d', '( %s ^c ( z + 0 ) ) = ( %s ^c z )' % (XPD, XPD))
    e1 = tz([tz([v1, v1b], 'eqtrd', '( %s ` z ) = ( %s ^c ( z + 0 ) )' % (M1, XPD)), v1c], 'eqtrd', '( %s ` z ) = ( %s ^c z )' % (M1, XPD))
    com = tz([zc, scz], 'addcomd', '( z + S ) = ( S + z )')
    v2, _ = mpval(w, Az, 'd', U5, '( E ` ( d + S ) )', 'z', zm)
    e2 = tz([v2, tz([com], 'fveq2d', '( E ` ( z + S ) ) = ( E ` ( S + z ) )')], 'eqtrd', '( %s ` z ) = ( E ` ( S + z ) )' % M2)
    v3, _ = mpval(w, Az, 'd', U5, '( %s ` ( d + S ) )' % MS, 'z', zm)
    zS = tz([zc, scz], 'addcld', '( z + S ) e. CC')
    v3b, _ = mpval(w, Az, 's', 'CC', MRr('R', 's'), '( z + S )', zS)
    e3 = tz([tz([v3, v3b], 'eqtrd', '( %s ` z ) = %s' % (M3, MRr('R', '( z + S )'))), tz([com], 'fveq2d', '%s = %s' % (MRr('R', '( z + S )'), MRr('R', '( S + z )')))],
            'eqtrd', '( %s ` z ) = %s' % (M3, MRr('R', '( S + z )')))
    B23 = '( ( %s ` e ) x. ( %s ` e ) )' % (M2, M3)
    v4, _ = mpval(w, Az, 'e', U5, B23, 'z', zm)
    RHS23 = '( ( E ` ( S + z ) ) x. %s )' % MRr('R', '( S + z )')
    e4 = tz([v4, tz([e2, e3], 'oveq12d', '( ( %s ` z ) x. ( %s ` z ) ) = %s' % (M2, M3, RHS23))], 'eqtrd', '( %s ` z ) = %s' % (P23e, RHS23))
    body = tz([e1, e4], 'oveq12d', '( ( %s ` z ) x. ( %s ` z ) ) = %s' % (M1, P23e, HMX('z')))
    mq = st([body], 'mpteq2dva', '%s = ( z e. %s |-> %s )' % (P, U5, HMX('z')))
    cb2, HMw = cbvm(w, a, 'z', 'w', U5, HMX('z'))
    assert HMw == HM, HMw
    fin = holeq(w, a, P, HM, U5, hp, st([mq, cb2], 'eqtrd', '%s = %s' % (P, HM)))
    toqed(w, fin, 'z6hm')
    return w


C0 = '( ( CC _D %s ) ` 0 )' % HM
DSB = 'if ( a = 0 , %s , ( ( ( %s ` a ) - ( %s ` 0 ) ) / ( a - 0 ) ) )' % (C0, HM, HM)


def zin5(w, a, sc, rpos):
    """( a -> 0 e. U5 ) from S e. CC , 0 < Re S"""
    st = mkst(w, a)
    rs = st([sc], 'recld', '( Re ` S ) e. RR')
    nr = st([rs], 'renegcld', '-u ( Re ` S ) e. RR')
    re0 = c_(w, a, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')
    lt = st([linarith(w, a, [rpos], '-u ( Re ` S ) < 0', leaves={'( Re ` S )': rs}), re0], 'breqtrrd', '-u ( Re ` S ) < ( Re ` 0 )')
    bi = st([nr, w.inst('elhp2')], 'syl', '( 0 e. %s <-> ( 0 e. CC /\\ -u ( Re ` S ) < ( Re ` 0 ) ) )' % U5)
    return st([st([c_(w, a, w.s([], '0cn', '0 e. CC'), '0 e. CC'), lt], 'jca', '( 0 e. CC /\\ -u ( Re ` S ) < ( Re ` 0 ) )'), bi], 'mpbird', '0 e. %s' % U5)


def z6ff():
    w = W('z6ff', 'Lean ` differentiableAt_Gone ` with the removable point: ` Gone ( w ) = _G ( w + 1 ) dslope H_1 0 w ` is continuous on '
          '` Re w > -u Re S ` (~ dscn , ~ z6gamhol shifted by ~ z6hshift , ~ mulcncf ) and differentiable off ` 0 ` (~ dsdv , ~ z6dvoff ).')
    a = ante('z6ff'); f = unpack(w, a); st = mkst(w, a)
    sc = f['S e. CC']; rpos = f['0 < ( Re ` S )']; rle = f['( Re ` S ) <_ 1']
    hm, _ = applyn(w, a, 'z6hm', {}, f)
    hcn = st([hm], 'simpld', '%s e. ( %s -cn-> CC )' % (HM, U5)); hdv = st([hm], 'simprd', '%s C_ dom ( CC _D %s )' % (U5, HM))
    z0 = zin5(w, a, sc, rpos)
    z0d = st([hdv, z0], 'sseldd', '0 e. dom ( CC _D %s )' % HM)
    dcn = st([hcn, z0d, st([], 'eqidd', '%s = %s' % (C0, C0)), w.inst('dscn')], 'syl3anc', '%s e. ( %s -cn-> CC )' % (DSM, U5))
    c0c = st([c_(w, a, w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (HM, HM)), '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (HM, HM)), z0d],
             'ffvelcdmd', '%s e. CC' % C0)
    ddv = st([hcn, z0, c0c, w.inst('dsdv')], 'syl3anc', '( dom ( CC _D %s ) \\ { 0 } ) C_ dom ( CC _D %s )' % (HM, DSM))
    vdv = st([st([hdv], 'ssdifd', '( %s \\ { 0 } ) C_ ( dom ( CC _D %s ) \\ { 0 } )' % (U5, HM)), ddv], 'sstrd', '( %s \\ { 0 } ) C_ dom ( CC _D %s )' % (U5, DSM))
    # Gamma ( w + 1 )
    uo = c_(w, a, w.s([], 'z6mstopn', '%s e. %s' % (U5, TOP)), '%s e. %s' % (U5, TOP))
    GZ = '( z e. %s |-> ( _G ` z ) )' % HPZ
    g = c_(w, a, w.s([], 'z6gamhol', STATEMENTS['z6gamhol']), HOLG(GZ, HPZ))
    cg, GZc = cbvm(w, a, 'z', 'c', HPZ, '( _G ` z )')
    gc = holeq(w, a, GZ, GZc, HPZ, g, cg)
    Aw = '( %s /\\ w e. %s )' % (a, U5)
    _, wc, wlo = u5mem(w, Aw, 'w', lift(w, sc, Aw))
    one = c_(w, Aw, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    t = mkst(w, Aw)
    rs = t([lift(w, sc, Aw)], 'recld', '( Re ` S ) e. RR'); rw = t([wc], 'recld', '( Re ` w ) e. RR')
    w1 = t([wc, one], 'addcld', '( w + 1 ) e. CC')
    re1 = t([t([wc, one], 'readdd', '( Re ` ( w + 1 ) ) = ( ( Re ` w ) + ( Re ` 1 ) )'),
             t([c_(w, Aw, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'oveq2d', '( ( Re ` w ) + ( Re ` 1 ) ) = ( ( Re ` w ) + 1 )')], 'eqtrd',
            '( Re ` ( w + 1 ) ) = ( ( Re ` w ) + 1 )')
    gt = t([linarith(w, Aw, [wlo, lift(w, rle, Aw)], '0 < ( ( Re ` w ) + 1 )', leaves={'( Re ` S )': rs, '( Re ` w )': rw}), re1], 'breqtrrd', '0 < ( Re ` ( w + 1 ) )')
    bi = t([c_(w, Aw, w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( ( w + 1 ) e. %s <-> ( ( w + 1 ) e. CC /\\ 0 < ( Re ` ( w + 1 ) ) ) )' % HPZ)
    w1h = t([t([w1, gt], 'jca', '( ( w + 1 ) e. CC /\\ 0 < ( Re ` ( w + 1 ) ) )'), bi], 'mpbird', '( w + 1 ) e. %s' % HPZ)
    r1 = st([w1h], 'ralrimiva', 'A. w e. %s ( w + 1 ) e. %s' % (U5, HPZ))
    G1 = '( d e. %s |-> ( %s ` ( d + 1 ) ) )' % (U5, GZc)
    h1 = st([gc, st([uo, c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC'), r1], '3jca', '( %s e. %s /\\ 1 e. CC /\\ A. w e. %s ( w + 1 ) e. %s )' % (U5, TOP, U5, HPZ)),
             w.inst('z6hshift')], 'syl2anc', HOLG(G1, U5))
    g1cn = st([h1], 'simpld', '%s e. ( %s -cn-> CC )' % (G1, U5))
    PZ = '( z e. %s |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (U5, G1, DSM)
    dv = st([h1, st([dcn, vdv], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s \\ { 0 } ) C_ dom ( CC _D %s ) )' % (DSM, U5, U5, DSM)), w.inst('z6dvoff')], 'syl2anc',
            '( %s \\ { 0 } ) C_ dom ( CC _D %s )' % (U5, PZ))
    def asmpt(Fn, fcn):
        ff = st([fcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (Fn, U5))
        eq = st([ff], 'feqmptd', '%s = ( z e. %s |-> ( %s ` z ) )' % (Fn, U5, Fn))
        return st([fcn, st([eq], 'eleq1d', '( %s e. ( %s -cn-> CC ) <-> ( z e. %s |-> ( %s ` z ) ) e. ( %s -cn-> CC ) )' % (Fn, U5, U5, Fn, U5))], 'mpbid',
                  '( z e. %s |-> ( %s ` z ) ) e. ( %s -cn-> CC )' % (U5, Fn, U5))
    cn = w.s([asmpt(G1, g1cn), asmpt(DSM, dcn)], 'mulcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (a, PZ, U5))
    # PZ = FF
    Az = '( %s /\\ z e. %s )' % (a, U5)
    zm = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, U5))
    tz = mkst(w, Az)
    # ( z + 1 ) e. HPZ from the quantified fact
    idk = w.s([], 'id', '( w = z -> w = z )')
    sb_, _ = w.congr('( w + 1 )', {'w': 'z'}, 'w = z', {'w': idk})
    el = w.s([sb_], 'eleq1d', '( w = z -> ( ( w + 1 ) e. %s <-> ( z + 1 ) e. %s ) )' % (HPZ, HPZ))
    rs_ = w.s([el], 'rspcv', '( z e. %s -> ( A. w e. %s ( w + 1 ) e. %s -> ( z + 1 ) e. %s ) )' % (U5, U5, HPZ, HPZ))
    z1h = tz([zm, lift(w, r1, Az), rs_], 'sylc', '( z + 1 ) e. %s' % HPZ)
    v1, _ = mpval(w, Az, 'd', U5, '( %s ` ( d + 1 ) )' % GZc, 'z', zm)
    v2, _ = mpval(w, Az, 'c', HPZ, '( _G ` c )', '( z + 1 )', z1h)
    e1 = tz([v1, v2], 'eqtrd', '( %s ` z ) = ( _G ` ( z + 1 ) )' % G1)
    body = tz([e1], 'oveq1d', '( ( %s ` z ) x. ( %s ` z ) ) = ( ( _G ` ( z + 1 ) ) x. ( %s ` z ) )' % (G1, DSM, DSM))
    mq = st([body], 'mpteq2dva', '%s = ( z e. %s |-> ( ( _G ` ( z + 1 ) ) x. ( %s ` z ) ) )' % (PZ, U5, DSM))
    cb2, FFb = cbvm(w, a, 'z', 'b', U5, '( ( _G ` ( z + 1 ) ) x. ( %s ` z ) )' % DSM)
    assert FFb == FF, FFb
    eq = st([mq, cb2], 'eqtrd', '%s = %s' % (PZ, FF))
    cnF = st([cn, st([eq], 'eleq1d', '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (PZ, U5, FF, U5))], 'mpbid', '%s e. ( %s -cn-> CC )' % (FF, U5))
    dvF = st([dv, st([st([eq], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (PZ, FF))], 'dmeqd', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (PZ, FF))], 'sseqtrd',
             '( %s \\ { 0 } ) C_ dom ( CC _D %s )' % (U5, FF))
    w.qed([cnF, dvF], 'jca', STATEMENTS['z6ff'])
    return w


def z6ffv():
    w = W('z6ffv', 'Lean ` Gone_eq_of_ne ` , ` Hone_zero ` : off ` 0 ` , ` Gone ( W ) = _G ( W ) H_1 ( W ) ` because ` H_1 ( 0 ) = E ( S ) M_r ( S ) = 0 ` '
          '(~ dsvaln , ~ gamp1 ).')
    a = ante('z6ffv'); f = unpack(w, a); st = mkst(w, a)
    sc = f['S e. CC']; wu = f['W e. %s' % U5]; wdg = f['W e. %s' % DG]; wne = f['W =/= 0']; es0 = f['( E ` S ) = 0']
    hm, _ = applyn(w, a, 'z6hm', {}, f)
    hcn = st([hm], 'simpld', '%s e. ( %s -cn-> CC )' % (HM, U5))
    z0 = zin5(w, a, sc, f['0 < ( Re ` S )'])
    wc = st([wdg], 'eldifad', 'W e. CC')
    # FF ` W
    v1, _ = mpval(w, a, 'b', U5, '( ( _G ` ( b + 1 ) ) x. ( %s ` b ) )' % DSM, 'W', wu)
    dsv = st([st([hcn, z0], 'jca', '( %s e. ( %s -cn-> CC ) /\\ 0 e. %s )' % (HM, U5, U5)), st([wu, wne], 'jca', '( W e. %s /\\ W =/= 0 )' % U5), w.inst('dsvaln')],
             'syl2anc', '( %s ` W ) = ( ( ( %s ` W ) - ( %s ` 0 ) ) / ( W - 0 ) )' % (DSM, HM, HM))
    hw, _ = mpval(w, a, 'w', U5, HMX('w'), 'W', wu)
    h0, _ = mpval(w, a, 'w', U5, HMX('w'), '0', z0)
    s0 = st([sc], 'addridd', '( S + 0 ) = S')
    MS0 = MRr('R', '( S + 0 )')
    es00 = st([st([s0], 'fveq2d', '( E ` ( S + 0 ) ) = ( E ` S )'), es0], 'eqtrd', '( E ` ( S + 0 ) ) = 0')
    # M_r ( S + 0 ) e. CC : from z6mrhol's mapping being a function CC --> CC is heavy; use the product with 0 through mul02d needs A e. CC.
    MSm = '( s e. CC |-> %s )' % MRr('R', 's')
    zz = st([st([f['D e. RR'], f['1 < D']], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1D); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2D); z12 = st([zz], 'simp3d', '%s < %s' % (Z1D, Z2D))
    HAB = sub(HAB0, {'A': Z1D, 'B': Z2D})
    hab = st([st([st([z1rp], 'rpred', '%s e. RR' % Z1D), st([z1rp], 'rpgt0d', '0 < %s' % Z1D)], 'jca', '( %s e. RR /\\ 0 < %s )' % (Z1D, Z1D)),
              st([st([z2rp], 'rpred', '%s e. RR' % Z2D), z12], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca', HAB)
    mh = st([st([st([hab, f['R e. NN']], 'jca', '( %s /\\ R e. NN )' % HAB), f['C : NN --> CC']], 'jca', '( ( %s /\\ R e. NN ) /\\ C : NN --> CC )' % HAB),
             w.inst('z6mrhol')], 'syl', HOLG(MSm, 'CC'))
    mff = st([st([mh], 'simpld', '%s e. ( CC -cn-> CC )' % MSm), w.inst('cncff')], 'syl', '%s : CC --> CC' % MSm)
    s0c = st([sc, c_(w, a, w.s([], '0cn', '0 e. CC'), '0 e. CC')], 'addcld', '( S + 0 ) e. CC')
    mv0, _ = mpval(w, a, 's', 'CC', MRr('R', 's'), '( S + 0 )', s0c)
    mc = st([mv0, st([mff, s0c], 'ffvelcdmd', '( %s ` ( S + 0 ) ) e. CC' % MSm)], 'eqeltrrd', '%s e. CC' % MS0)
    p0 = st([st([es00], 'oveq1d', '( ( E ` ( S + 0 ) ) x. %s ) = ( 0 x. %s )' % (MS0, MS0)), st([mc], 'mul02d', '( 0 x. %s ) = 0' % MS0)], 'eqtrd',
            '( ( E ` ( S + 0 ) ) x. %s ) = 0' % MS0)
    x0c = st([st([st([f['D e. RR'], linarith(w, a, [f['1 < D']], '0 < D', leaves={'D': f['D e. RR']})], 'elrpd', 'D e. RR+'),
                  c_(w, a, __import__('num').real(w, '( 6 / 5 )'), '( 6 / 5 ) e. RR')], 'rpcxpcld', '%s e. RR+' % XPD)], 'rpcnd', '%s e. CC' % XPD)
    xp0 = st([x0c, c_(w, a, w.s([], '0cn', '0 e. CC'), '0 e. CC')], 'cxpcld', '( %s ^c 0 ) e. CC' % XPD)
    hz = st([st([p0], 'oveq2d', '%s = ( ( %s ^c 0 ) x. 0 )' % (HMX('0'), XPD)), st([xp0], 'mul01d', '( ( %s ^c 0 ) x. 0 ) = 0' % XPD)], 'eqtrd', '%s = 0' % HMX('0'))
    h00 = st([h0, hz], 'eqtrd', '( %s ` 0 ) = 0' % HM)
    hwc0 = st([st([hcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (HM, U5)), wu], 'ffvelcdmd', '( %s ` W ) e. CC' % HM)
    hwc = st([hw, hwc0], 'eqeltrrd', '%s e. CC' % HMX('W'))
    num_ = st([st([hw, h00], 'oveq12d', '( ( %s ` W ) - ( %s ` 0 ) ) = ( %s - 0 )' % (HM, HM, HMX('W'))), st([hwc], 'subid1d', '( %s - 0 ) = %s' % (HMX('W'), HMX('W')))],
              'eqtrd', '( ( %s ` W ) - ( %s ` 0 ) ) = %s' % (HM, HM, HMX('W')))
    q = st([num_, st([wc], 'subid1d', '( W - 0 ) = W')], 'oveq12d', '( ( ( %s ` W ) - ( %s ` 0 ) ) / ( W - 0 ) ) = ( %s / W )' % (HM, HM, HMX('W')))
    dsw = st([dsv, q], 'eqtrd', '( %s ` W ) = ( %s / W )' % (DSM, HMX('W')))
    gp = st([wdg, w.inst('gamp1')], 'syl', '( _G ` ( W + 1 ) ) = ( ( _G ` W ) x. W )')
    gc = st([wdg, w.inst('gamcl')], 'syl', '( _G ` W ) e. CC')
    e1 = st([v1, st([gp, dsw], 'oveq12d', '( ( _G ` ( W + 1 ) ) x. ( %s ` W ) ) = ( ( ( _G ` W ) x. W ) x. ( %s / W ) )' % (DSM, HMX('W')))], 'eqtrd',
            '( %s ` W ) = ( ( ( _G ` W ) x. W ) x. ( %s / W ) )' % (FF, HMX('W')))
    dq = st([hwc, wc, wne], 'divcld', '( %s / W ) e. CC' % HMX('W'))
    e2 = st([gc, wc, dq], 'mulassd', '( ( ( _G ` W ) x. W ) x. ( %s / W ) ) = ( ( _G ` W ) x. ( W x. ( %s / W ) ) )' % (HMX('W'), HMX('W')))
    e3 = st([st([hwc, wc, wne], 'divcan2d', '( W x. ( %s / W ) ) = %s' % (HMX('W'), HMX('W')))], 'oveq2d',
            '( ( _G ` W ) x. ( W x. ( %s / W ) ) ) = ( ( _G ` W ) x. %s )' % (HMX('W'), HMX('W')))
    w.qed([st([e1, e2], 'eqtrd', '( %s ` W ) = ( ( _G ` W ) x. ( W x. ( %s / W ) ) )' % (FF, HMX('W'))), e3], 'eqtrd', STATEMENTS['z6ffv'])
    return w


def z6rdg():
    w = W('z6rdg', 'A complex number right of ` Re = -u 1 ` other than ` 0 ` is not a nonpositive integer, so it lies in the domain of Gamma.')
    a = ante('z6rdg'); st = mkst(w, a)
    uc = st([], 'simpl', 'U e. CC'); ul = st([], 'simprl', '-u 1 < ( Re ` U )'); un = st([], 'simprr', 'U =/= 0')
    ZN = '( ZZ \\ NN )'
    b = '( %s /\\ U e. %s )' % (a, ZN); sb = mkst(w, b)
    um = sb([], 'simpr', 'U e. %s' % ZN)
    uz = sb([um], 'eldifad', 'U e. ZZ'); unn = sb([um], 'eldifbd', '-. U e. NN')
    ur = sb([uz], 'zred', 'U e. RR')
    ul2 = sb([lift(w, ul, b), sb([ur], 'rered', '( Re ` U ) = U')], 'breqtrd', '-u 1 < U')
    zl = sb([c_(w, b, w.s([], 'neg1z', '-u 1 e. ZZ'), '-u 1 e. ZZ'), uz, w.inst('zltp1le')], 'syl2anc', '( -u 1 < U <-> ( -u 1 + 1 ) <_ U )')
    le1 = sb([ul2, zl], 'mpbid', '( -u 1 + 1 ) <_ U')
    ge0 = linarith(w, b, [le1], '0 <_ U', leaves={'U': ur})
    gt0 = sb([sb([ge0, sb([lift(w, un, b)], 'necomd' if False else 'id', 'U =/= 0') if False else lift(w, un, b)], 'jca', '( 0 <_ U /\\ U =/= 0 )'),
              sb([c_(w, b, w.s([], '0re', '0 e. RR'), '0 e. RR'), ur], 'ltlend', '( 0 < U <-> ( 0 <_ U /\\ U =/= 0 ) )')], 'mpbird', '0 < U')
    unn2 = sb([sb([uz, gt0], 'jca', '( U e. ZZ /\\ 0 < U )'), c_(w, b, w.s([], 'elnnz', '( U e. NN <-> ( U e. ZZ /\\ 0 < U ) )'), '( U e. NN <-> ( U e. ZZ /\\ 0 < U ) )')],
              'mpbird', 'U e. NN')
    nz = w.s([unn2, unn], 'pm2.65da', '( %s -> -. U e. %s )' % (a, ZN))
    w.qed([st([st([uc, nz], 'jca', '( U e. CC /\\ -. U e. %s )' % ZN), c_(w, a, w.s([], 'eldif', '( U e. %s <-> ( U e. CC /\\ -. U e. %s ) )' % (DG, ZN)),
                                                                         '( U e. %s <-> ( U e. CC /\\ -. U e. %s ) )' % (DG, ZN))], 'mpbird', 'U e. %s' % DG) if False else
           st([uc, nz], 'jca', '( U e. CC /\\ -. U e. %s )' % ZN), c_(w, a, w.s([], 'eldif', '( U e. %s <-> ( U e. CC /\\ -. U e. %s ) )' % (DG, ZN)),
                                                                     '( U e. %s <-> ( U e. CC /\\ -. U e. %s ) )' % (DG, ZN))], 'mpbird', STATEMENTS['z6rdg'])
    return w


def z6pdg():
    w = W('z6pdg', 'The pole ` 1 - S ` of ` L ( S + w ) ` lies in the domain of Gamma: its imaginary part is nonzero, or ` S ` is real and '
          '` 0 < 1 - S < 1 ` (~ z6mndg , ~ btwnnz ).')
    a = ante('z6pdg'); st = mkst(w, a)
    f = unpack(w, a)
    sc = f['S e. CC']; lo = f['( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )']; hi = f['( Re ` S ) <_ 1']; ne1 = f['S =/= 1']
    one = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    pc = st([one, sc], 'subcld', '( 1 - S ) e. CC')
    P = '( 1 - S )'
    OR = '( -. ( Re ` %s ) e. ZZ \\/ ( Im ` %s ) =/= 0 )' % (P, P)
    # Im S =/= 0
    c2 = '( %s /\\ ( Im ` S ) =/= 0 )' % a; s2 = mkst(w, c2)
    im = s2([s2([lift(w, one, c2), lift(w, sc, c2)], 'imsubd', '( Im ` %s ) = ( ( Im ` 1 ) - ( Im ` S ) )' % P),
             s2([c_(w, c2, w.s([], 'im1', '( Im ` 1 ) = 0'), '( Im ` 1 ) = 0')], 'oveq1d', '( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) )')], 'eqtrd',
            '( Im ` %s ) = ( 0 - ( Im ` S ) )' % P)
    isn = s2([], 'simpr', '( Im ` S ) =/= 0')
    d0 = s2([c_(w, c2, w.s([], '0cn', '0 e. CC'), '0 e. CC'), s2([s2([lift(w, sc, c2)], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC'),
             s2([isn], 'necomd', '0 =/= ( Im ` S )')], 'subne0d', '( 0 - ( Im ` S ) ) =/= 0')
    o2 = s2([s2([im, d0], 'eqnetrd', '( Im ` %s ) =/= 0' % P)], 'olcd', OR)
    e2 = w.s([o2], 'ex', '( %s -> ( ( Im ` S ) =/= 0 -> %s ) )' % (a, OR))
    # Im S = 0
    c1 = '( %s /\\ ( Im ` S ) = 0 )' % a; s1 = mkst(w, c1)
    sc1 = lift(w, sc, c1)
    i0 = s1([], 'simpr', '( Im ` S ) = 0')
    rp = s1([sc1], 'replimd', 'S = ( ( Re ` S ) + ( _i x. ( Im ` S ) ) )')
    rs = s1([sc1], 'recld', '( Re ` S ) e. RR')
    t1 = s1([s1([i0], 'oveq2d', '( _i x. ( Im ` S ) ) = ( _i x. 0 )'), s1([c_(w, c1, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')], 'mul01d', '( _i x. 0 ) = 0')], 'eqtrd',
            '( _i x. ( Im ` S ) ) = 0')
    t2 = s1([s1([t1], 'oveq2d', '( ( Re ` S ) + ( _i x. ( Im ` S ) ) ) = ( ( Re ` S ) + 0 )'), s1([s1([rs], 'recnd', '( Re ` S ) e. CC')], 'addridd', '( ( Re ` S ) + 0 ) = ( Re ` S )')],
            'eqtrd', '( ( Re ` S ) + ( _i x. ( Im ` S ) ) ) = ( Re ` S )')
    sre = s1([rp, t2], 'eqtrd', 'S = ( Re ` S )')
    rne = s1([s1([sre, lift(w, ne1, c1)], 'eqnetrrd', '( Re ` S ) =/= 1')], 'necomd', '1 =/= ( Re ` S )')
    lt1 = s1([s1([lift(w, hi, c1), rne], 'jca', '( ( Re ` S ) <_ 1 /\\ 1 =/= ( Re ` S ) )'),
              s1([rs, c_(w, c1, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'ltlend', '( ( Re ` S ) < 1 <-> ( ( Re ` S ) <_ 1 /\\ 1 =/= ( Re ` S ) ) )')], 'mpbird', '( Re ` S ) < 1')
    X = '( 1 - ( Re ` S ) )'
    g0 = linarith(w, c1, [lt1], '0 < %s' % X, leaves={'( Re ` S )': rs})
    l1 = linarith(w, c1, [lift(w, lo, c1)], '%s < ( 0 + 1 )' % X, leaves={'( Re ` S )': rs})
    nz = s1([c_(w, c1, w.s([], '0z', '0 e. ZZ'), '0 e. ZZ'), g0, l1, w.inst('btwnnz')], 'syl3anc', '-. %s e. ZZ' % X)
    rpv = s1([s1([lift(w, one, c1), sc1], 'resubd', '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` S ) )' % P),
              s1([c_(w, c1, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'oveq1d', '( ( Re ` 1 ) - ( Re ` S ) ) = %s' % X)], 'eqtrd', '( Re ` %s ) = %s' % (P, X))
    o1 = s1([s1([rpv, nz], 'eqneltrd', '-. ( Re ` %s ) e. ZZ' % P)], 'orcd', OR)
    e1 = w.s([o1], 'ex', '( %s -> ( ( Im ` S ) = 0 -> %s ) )' % (a, OR))
    orr = st([e1, e2], 'pm2.61dne', OR)
    w.qed([st([pc, orr], 'jca', '( %s e. CC /\\ %s )' % (P, OR)), w.inst('z6mndg')], 'syl', STATEMENTS['z6pdg'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6dvoff, z6hm, z6ff, z6ffv, z6rdg, z6pdg]:
        if want(fn.__name__):
            if not run(fn()):
                break
