"""Z6a (block z6ab): generic holomorphy helpers -- the identity, exp o F, F ( z + N )."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_ghlib import *

S_HID = '( D e. %s -> %s )' % (TOP, HOLG('( z e. D |-> z )', 'D'))
S_HEXP = '( %s -> %s )' % (HOLG('F', 'D'), HOLG('( z e. D |-> ( exp ` ( F ` z ) ) )', 'D'))
S_HSHIFT = ('( ( %s /\\ ( U e. %s /\\ N e. CC /\\ A. w e. U ( w + N ) e. D ) ) -> %s )'
            % (HOLG('F', 'D'), TOP, HOLG('( z e. U |-> ( F ` ( z + N ) ) )', 'U')))


def hid():
    w = W('z6hid', 'The identity is holomorphic on every open set.')
    A0 = 'D e. %s' % TOP
    s = st(w, A0)
    uo = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    ucc = opnss(w, A0, uo, 'D')
    sc = c1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    did = s([sc], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    Az = '( %s /\\ z e. CC )' % A0
    zc = w.s([], 'simpr', '( %s -> z e. CC )' % Az)
    o1 = c1(w, Az, 'ax-1cn', '1 e. CC')
    dr = dvres(w, A0, 'z', 'D', 'z', '1', did, zc, o1, uo, ucc)
    Ad = '( %s /\\ z e. D )' % A0
    zd = w.s([w.s([ucc], 'adantr', '( %s -> D C_ CC )' % Ad), w.s([], 'simpr', '( %s -> z e. D )' % Ad)], 'sseldd', '( %s -> z e. CC )' % Ad)
    h = holfromdv(w, A0, 'z', 'D', 'z', '1', dr, zd, c1(w, Ad, 'ax-1cn', '1 e. CC'), ucc)
    w.lines[-1] = w.lines[-1].replace(h + ':', 'qed:', 1)
    return run(w)


def hexp():
    w = W('z6hexp', 'The exponential of a holomorphic function is holomorphic ( ~ dvef , ~ dvmptco ).')
    A0 = HOLG('F', 'D')
    s = st(w, A0)
    fcn = w.s([], 'simpl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    ff = s([fcn, w.inst('cncff')], 'syl', 'F : D --> CC')
    dss = s([fcn, w.inst('cncfrss')], 'syl', 'D C_ CC')
    fd = w.s([], 'holf', '( %s -> ( CC _D F ) : D --> CC )' % A0)
    sc = c1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    Az = '( %s /\\ z e. D )' % A0
    zd = w.s([], 'simpr', '( %s -> z e. D )' % Az)
    fz = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Az), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % Az)
    dz = w.s([w.s([fd], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % Az), zd], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` z ) e. CC )' % Az)
    Ay = '( %s /\\ y e. CC )' % A0
    ey = w.s([w.s([], 'simpr', '( %s -> y e. CC )' % Ay), w.inst('efcl')], 'syl', '( %s -> ( exp ` y ) e. CC )' % Ay)
    inner = w.s([], 'holdv', '( %s -> ( CC _D ( z e. D |-> ( F ` z ) ) ) = ( z e. D |-> ( ( CC _D F ) ` z ) ) )' % A0)
    em = s([c1(w, A0, 'eff', 'exp : CC --> CC')], 'feqmptd', 'exp = ( y e. CC |-> ( exp ` y ) )')
    outer = s([w.s([em], 'oveq2d', '( %s -> ( CC _D exp ) = ( CC _D ( y e. CC |-> ( exp ` y ) ) ) )' % A0), c1(w, A0, 'dvef', '( CC _D exp ) = exp'), em], '3eqtr3d',
              '( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( y e. CC |-> ( exp ` y ) )')
    fe = w.s([], 'fveq2', '( y = ( F ` z ) -> ( exp ` y ) = ( exp ` ( F ` z ) ) )')
    co = s([sc, sc, fz, dz, ey, ey, inner, outer, fe, fe], 'dvmptco',
           '( CC _D ( z e. D |-> ( exp ` ( F ` z ) ) ) ) = ( z e. D |-> ( ( exp ` ( F ` z ) ) x. ( ( CC _D F ) ` z ) ) )')
    efz = w.s([fz, w.inst('efcl')], 'syl', '( %s -> ( exp ` ( F ` z ) ) e. CC )' % Az)
    db = w.s([efz, dz], 'mulcld', '( %s -> ( ( exp ` ( F ` z ) ) x. ( ( CC _D F ) ` z ) ) e. CC )' % Az)
    h = holfromdv(w, A0, 'z', 'D', '( exp ` ( F ` z ) )', '( ( exp ` ( F ` z ) ) x. ( ( CC _D F ) ` z ) )', co, efz, db, dss)
    w.lines[-1] = w.lines[-1].replace(h + ':', 'qed:', 1)
    return run(w)


def hshift():
    w = W('z6hshift', 'A holomorphic function composed with a translation ` z + N ` that maps the open set ` U ` '
          'into its domain is holomorphic on ` U ` ( ~ holdv , ~ dvmptco ).')
    A0 = '( %s /\\ ( U e. %s /\\ N e. CC /\\ A. w e. U ( w + N ) e. D ) )' % (HOLG('F', 'D'), TOP)
    s = st(w, A0)
    hol = w.s([], 'simpl', '( %s -> %s )' % (A0, HOLG('F', 'D')))
    uo = w.s([], 'simpr1', '( %s -> U e. %s )' % (A0, TOP))
    nc = w.s([], 'simpr2', '( %s -> N e. CC )' % A0)
    ral = w.s([], 'simpr3', '( %s -> A. w e. U ( w + N ) e. D )' % A0)
    ucc = opnss(w, A0, uo, 'U')
    fcn = s([hol, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )')
    ff = s([fcn, w.inst('cncff')], 'syl', 'F : D --> CC')
    fd = s([hol, w.inst('holf')], 'syl', '( CC _D F ) : D --> CC')
    sc = c1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    # inner derivative on CC, then on U
    Ac = '( %s /\\ z e. CC )' % A0
    zc = w.s([], 'simpr', '( %s -> z e. CC )' % Ac)
    o1 = c1(w, Ac, 'ax-1cn', '1 e. CC')
    ncz = w.s([nc], 'adantr', '( %s -> N e. CC )' % Ac)
    o0 = c1(w, Ac, 'c0ex', '0 e. _V')
    did = s([sc], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    dc = s([sc, nc], 'dvmptc', '( CC _D ( z e. CC |-> N ) ) = ( z e. CC |-> 0 )')
    dadd = s([sc, zc, o1, did, ncz, o0, dc], 'dvmptadd', '( CC _D ( z e. CC |-> ( z + N ) ) ) = ( z e. CC |-> ( 1 + 0 ) )')
    zn = w.s([zc, ncz], 'addcld', '( %s -> ( z + N ) e. CC )' % Ac)
    b10 = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'addcli', '( 1 + 0 ) e. CC')], 'a1i', '( %s -> ( 1 + 0 ) e. CC )' % Ac)
    dz = dvres(w, A0, 'z', 'U', '( z + N )', '( 1 + 0 )', dadd, zn, b10, uo, ucc)
    Au = '( %s /\\ z e. U )' % A0
    zu = w.s([], 'simpr', '( %s -> z e. U )' % Au)
    znd = w.s([w.s([], 'oveq1', '( w = z -> ( w + N ) = ( z + N ) )')], 'eleq1d', '( w = z -> ( ( w + N ) e. D <-> ( z + N ) e. D ) )')
    mem = w.s([znd, w.s([ral], 'adantr', '( %s -> A. w e. U ( w + N ) e. D )' % Au), zu], 'rspcdva', '( %s -> ( z + N ) e. D )' % Au)
    b10u = w.s([w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '0cn', '0 e. CC')], 'addcli', '( 1 + 0 ) e. CC')], 'a1i', '( %s -> ( 1 + 0 ) e. CC )' % Au)
    Ay = '( %s /\\ y e. D )' % A0
    yd = w.s([], 'simpr', '( %s -> y e. D )' % Ay)
    fy = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Ay), yd], 'ffvelcdmd', '( %s -> ( F ` y ) e. CC )' % Ay)
    dy = w.s([w.s([fd], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % Ay), yd], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` y ) e. CC )' % Ay)
    outer = s([hol, w.inst('holdv')], 'syl', '( CC _D ( y e. D |-> ( F ` y ) ) ) = ( y e. D |-> ( ( CC _D F ) ` y ) )')
    e1 = w.s([], 'fveq2', '( y = ( z + N ) -> ( F ` y ) = ( F ` ( z + N ) ) )')
    e2 = w.s([], 'fveq2', '( y = ( z + N ) -> ( ( CC _D F ) ` y ) = ( ( CC _D F ) ` ( z + N ) ) )')
    DB = '( ( ( CC _D F ) ` ( z + N ) ) x. ( 1 + 0 ) )'
    co = s([sc, sc, mem, b10u, fy, dy, dz, outer, e1, e2], 'dvmptco',
           '( CC _D ( z e. U |-> ( F ` ( z + N ) ) ) ) = ( z e. U |-> %s )' % DB)
    fzn = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % Au), mem], 'ffvelcdmd', '( %s -> ( F ` ( z + N ) ) e. CC )' % Au)
    dzn = w.s([w.s([fd], 'adantr', '( %s -> ( CC _D F ) : D --> CC )' % Au), mem], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` ( z + N ) ) e. CC )' % Au)
    db = w.s([dzn, b10u], 'mulcld', '( %s -> %s e. CC )' % (Au, DB))
    h = holfromdv(w, A0, 'z', 'U', '( F ` ( z + N ) )', DB, co, fzn, db, ucc)
    w.lines[-1] = w.lines[-1].replace(h + ':', 'qed:', 1)
    return run(w)


if __name__ == '__main__':
    want = sys.argv[1:]
    for lab, fn in [('z6hid', hid), ('z6hexp', hexp), ('z6hshift', hshift)]:
        if lab in want:
            if fn():
                status(lab)
