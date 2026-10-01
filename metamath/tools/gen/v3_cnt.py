"""Sortie v3: the residue-class count.

cntmod  ( ( T e. NN0 /\\ D e. NN /\\ R e. ( 0 ..^ D ) ) ->
            ( abs ` ( ( # ` { x e. ( 1 ... T ) | ( x mod D ) = R } ) - ( T / D ) ) ) <_ 1 )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v3_lib import mkst
from lin import linarith
from cl import lift

A = '( T e. NN0 /\\ D e. NN /\\ R e. ( 0 ..^ D ) )'
SETM = '{ x e. ( 1 ... T ) | ( x mod D ) = R }'
SETD = '{ x e. ( 1 ... T ) | D || ( x - R ) }'
UU = '( ( T - R ) / D )'
VV = '( ( 0 - R ) / D )'
V1 = '( ( ( 1 - 1 ) - R ) / D )'
FU = '( |_ ` %s )' % UU
FV = '( |_ ` %s )' % VV
FV1 = '( |_ ` %s )' % V1
CNT = '( # ` %s )' % SETM
TD = '( T / D )'


def cntmod():
    w = W('cntmod', 'The number of n in ( 1 ... T ) in a fixed residue class mod D '
                    'differs from T / D by at most 1.')
    st = mkst(w, A)
    t0 = st([], 'simp1', 'T e. NN0')
    dn = st([], 'simp2', 'D e. NN')
    rf = st([], 'simp3', 'R e. ( 0 ..^ D )')
    rz = st([rf, w.inst('elfzoelz')], 'syl', 'R e. ZZ')
    rr = st([rz], 'zred', 'R e. RR')
    rc = st([rr], 'recnd', 'R e. CC')
    tr = st([t0], 'nn0red', 'T e. RR')
    tc = st([tr], 'recnd', 'T e. CC')
    drp = st([dn], 'nnrpd', 'D e. RR+')
    dr = st([drp], 'rpred', 'D e. RR')
    dc = st([dr], 'recnd', 'D e. CC')
    dne = st([drp], 'rpne0d', 'D =/= 0')
    onez = w.s([], 'a1i', '( %s -> 1 e. ZZ )' % A, name=None)
    # mmj2 wants the closed fact lifted: 1 e. ZZ
    w.lines.pop()
    z1 = w.s([], '1z', '1 e. ZZ')
    onez = st([z1], 'a1i', '1 e. ZZ')
    # T e. ( ZZ>= ` ( 1 - 1 ) )
    e10 = w.s([], '1m1e0', '( 1 - 1 ) = 0')
    e10d = st([e10], 'a1i', '( 1 - 1 ) = 0')
    uzeq = st([e10d], 'fveq2d', '( ZZ>= ` ( 1 - 1 ) ) = ( ZZ>= ` 0 )')
    nu = w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')
    nud = st([nu], 'a1i', 'NN0 = ( ZZ>= ` 0 )')
    tuz0 = st([t0, nud], 'eleqtrd', 'T e. ( ZZ>= ` 0 )')
    tuz = st([tuz0, uzeq], 'eleqtrrd', 'T e. ( ZZ>= ` ( 1 - 1 ) )')
    # hashdvds
    hd = st([dn, onez, tuz, rz], 'hashdvds',
            '( # ` %s ) = ( %s - %s )' % (SETD, FU, FV1))
    # ( 1 - 1 ) -> 0 inside
    r1 = st([e10d], 'oveq1d', '( ( 1 - 1 ) - R ) = ( 0 - R )')
    r2 = st([r1], 'oveq1d', '%s = %s' % (V1, VV))
    r3 = st([r2], 'fveq2d', '%s = %s' % (FV1, FV))
    r4 = st([r3], 'oveq2d', '( %s - %s ) = ( %s - %s )' % (FU, FV1, FU, FV))
    hd2 = st([hd, r4], 'eqtrd', '( # ` %s ) = ( %s - %s )' % (SETD, FU, FV))
    # the index sets agree
    AX = '( %s /\\ x e. ( 1 ... T ) )' % A
    sx = mkst(w, AX)
    xz = sx([sx([], 'simpr', 'x e. ( 1 ... T )'), w.inst('elfzelz')], 'syl', 'x e. ZZ')
    md = sx([lift(w, dn, AX), xz, lift(w, rz, AX), w.inst('moddvds')], 'syl3anc',
            '( ( x mod D ) = ( R mod D ) <-> D || ( x - R ) )')
    rm = sx([lift(w, rf, AX), w.inst('zmodidfzoimp')], 'syl', '( R mod D ) = R')
    eqb = sx([rm], 'eqeq2d', '( ( x mod D ) = ( R mod D ) <-> ( x mod D ) = R )')
    bic = sx([eqb, md], 'bitr3d', '( ( x mod D ) = R <-> D || ( x - R ) )')
    seteq = st([bic], 'rabbidva', '%s = %s' % (SETM, SETD))
    hs = st([seteq], 'fveq2d', '%s = ( # ` %s )' % (CNT, SETD))
    cnteq = st([hs, hd2], 'eqtrd', '%s = ( %s - %s )' % (CNT, FU, FV))
    # closures
    trc = st([tc, rc], 'subcld', '( T - R ) e. CC')
    trr = st([tr, rr], 'resubcld', '( T - R ) e. RR')
    z0 = w.s([], '0cn', '0 e. CC')
    z0d = st([z0], 'a1i', '0 e. CC')
    z0r = st([], '0red', '0 e. RR')
    zrr = st([z0r, rr], 'resubcld', '( 0 - R ) e. RR')
    zrc = st([z0d, rc], 'subcld', '( 0 - R ) e. CC')
    ur = st([trr, drp], 'rerpdivcld', '%s e. RR' % UU)
    vr = st([zrr, drp], 'rerpdivcld', '%s e. RR' % VV)
    tdr = st([tr, drp], 'rerpdivcld', '%s e. RR' % TD)
    fur = st([ur, w.inst('reflcl')], 'syl', '%s e. RR' % FU)
    fvr = st([vr, w.inst('reflcl')], 'syl', '%s e. RR' % FV)
    # the floor sandwich
    f1 = st([ur, w.inst('flle')], 'syl', '%s <_ %s' % (FU, UU))
    f2 = st([ur, w.inst('flltp1')], 'syl', '%s < ( %s + 1 )' % (UU, FU))
    f3 = st([vr, w.inst('flle')], 'syl', '%s <_ %s' % (FV, VV))
    f4 = st([vr, w.inst('flltp1')], 'syl', '%s < ( %s + 1 )' % (VV, FV))
    # ( UU - VV ) = ( T / D )
    ds = st([trc, zrc, dc, dne], 'divsubdird',
            '( ( ( T - R ) - ( 0 - R ) ) / D ) = ( %s - %s )' % (UU, VV))
    nc = st([tc, z0d, rc, w.inst('nnncan2')], 'syl3anc',
            '( ( T - R ) - ( 0 - R ) ) = ( T - 0 )')
    si = st([tc], 'subid1d', '( T - 0 ) = T')
    nn = st([nc, si], 'eqtrd', '( ( T - R ) - ( 0 - R ) ) = T')
    dd = st([nn], 'oveq1d', '( ( ( T - R ) - ( 0 - R ) ) / D ) = %s' % TD)
    feq = st([ds, dd], 'eqtr3d', '( %s - %s ) = %s' % (UU, VV, TD))
    leaves = {FU: fur, FV: fvr, UU: ur, VV: vr, TD: tdr}
    g1 = linarith(w, A, [f1, f2, f3, f4, feq],
                  '-u 1 <_ ( ( %s - %s ) - %s )' % (FU, FV, TD), leaves=leaves)
    g2 = linarith(w, A, [f1, f2, f3, f4, feq],
                  '( ( %s - %s ) - %s ) <_ 1' % (FU, FV, TD), leaves=leaves)
    sub = st([fur, fvr], 'resubcld', '( %s - %s ) e. RR' % (FU, FV))
    dif = st([sub, tdr], 'resubcld', '( ( %s - %s ) - %s ) e. RR' % (FU, FV, TD))
    one = st([], '1red', '1 e. RR')
    al = st([dif, one], 'absled',
            '( ( abs ` ( ( %s - %s ) - %s ) ) <_ 1 <-> ( -u 1 <_ ( ( %s - %s ) - %s ) /\\ ( ( %s - %s ) - %s ) <_ 1 ) )'
            % (FU, FV, TD, FU, FV, TD, FU, FV, TD))
    ab = st([al, g1, g2], 'mpbir2and', '( abs ` ( ( %s - %s ) - %s ) ) <_ 1' % (FU, FV, TD))
    b1 = st([cnteq], 'oveq1d', '( %s - %s ) = ( ( %s - %s ) - %s )' % (CNT, TD, FU, FV, TD))
    b2 = st([b1], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( ( %s - %s ) - %s ) )' % (CNT, TD, FU, FV, TD))
    w.qed([b2, ab], 'eqbrtrd', '( %s -> ( abs ` ( %s - %s ) ) <_ 1 )' % (A, CNT, TD))
    return w


if __name__ == '__main__':
    import sys
    cntmod().run()
