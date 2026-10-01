"""Sortie DSH, section C: dshdih = Lean detection_identity_half, from dshdetid at R = 1 (dshp11, dshrs1, dshvlc).
Run: MM_DB=sorties/dsh.mm MM_ENGINE=mmatch python3 tools/gen/dsh_h.py"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dshenv import *
import dshlib as L
from tm import W
from z6a_e3 import unpack, c_, build
from cl import split_imp
from z6alib import mkst, run


def dshdih():
    w = W('dshdih', '**Lean ` detection_identity_half ` ** (L1.a): for a zero ` S ` of ` L ( s , chi ) ` with ` 39 / 50 <_ Re S <_ 1 ` , the half-line detector at '
          '` z1 = D ` , ` z2 = 2 D ` , ` R = 1 ` , ` X = Ypar D = D ^ ( 151 / 100 ) ` satisfies ` F + e ^ ( -1 / X ) = E_ctr^half + E_pole ` , '
          '` E_ctr^half = ( 1 / 2 pi i ) VL ( GR ( 1 ) , 1/2 - Re S ) ` (~ dshdetid at ` R = 1 ` : ~ dshp11 , ~ dshrs1 , ~ dshvlc ).')
    a = L.A7H; f = unpack(w, a); st = mkst(w, a)
    A7P = split_imp(STATEMENTS['dshdetid'])[0]
    di = st([build(w, a, A7P, f), w.inst('dshdetid')], 'syl', split_imp(STATEMENTS['dshdetid'])[1])
    nn = f['N e. NN']
    E1_ = '( exp ` ( -u 1 / %s ) )' % L.YP
    P1S = 'sum_ r e. ( N RSet 1 ) ( 1 / r )'
    p1 = st([nn, w.inst('dshp11')], 'syl', '%s = 1' % P1S)
    yc = st([st([st([f['D e. RR'], f['1 < D']], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('dshyp')], 'syl', '( %s e. RR+ /\\ 1 < %s )' % (L.YP, L.YP))], 'simpld', '%s e. RR+' % L.YP)
    dv = st([c_(w, a, w.s([], 'neg1cn', '-u 1 e. CC'), '-u 1 e. CC'), st([yc], 'rpcnd', '%s e. CC' % L.YP), st([yc], 'rpne0d', '%s =/= 0' % L.YP)], 'divcld',
            '( -u 1 / %s ) e. CC' % L.YP)
    e1c = st([dv], 'efcld', '%s e. CC' % E1_)
    m1 = st([st([p1], 'oveq2d', '( %s x. %s ) = ( %s x. 1 )' % (E1_, P1S, E1_)), st([e1c], 'mulridd', '( %s x. 1 ) = %s' % (E1_, E1_))], 'eqtrd',
            '( %s x. %s ) = %s' % (E1_, P1S, E1_))
    lhs = st([m1], 'oveq2d', '( %s + ( %s x. %s ) ) = ( %s + %s )' % (L.FDVH, E1_, P1S, L.FDVH, E1_))
    # the r-sum of the contour terms at R = 1
    VLr = lambda r: VL(GR(r), CL)
    SUMV = 'sum_ r e. ( N RSet 1 ) ( ( 1 / r ) x. %s )' % VLr('r')
    rs = st([nn, w.inst('dshrs1')], 'syl', '( N RSet 1 ) = { 1 }')
    e3 = st([rs], 'sumeq1d', '%s = sum_ r e. { 1 } ( ( 1 / r ) x. %s )' % (SUMV, VLr('r')))
    cg, B1 = w.congr('( ( 1 / r ) x. %s )' % VLr('r'), {'r': '1'}, 'r = 1', {'r': w.s([], 'id', '( r = 1 -> r = 1 )')})
    fz = dict(f)
    fz['1 e. NN'] = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    fz['( mmu ` 1 ) =/= 0'] = c_(w, a, w.s([w.s([], 'muone', '( mmu ` 1 ) = 1'), w.s([], 'ax-1ne0', '1 =/= 0')], 'eqnetri', '( mmu ` 1 ) =/= 0'), '( mmu ` 1 ) =/= 0')
    SHA = split_imp(STATEMENTS['dshvlc'])[0].replace('R e. NN', '1 e. NN').replace('( mmu ` R )', '( mmu ` 1 )')
    from z6blib import applyn
    vc, _ = applyn(w, a, 'dshvlc', {'R': '1'}, fz)
    V1 = VLr('1')
    d1 = c_(w, a, w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')
    v1 = st([st([d1], 'oveq1d', '%s = ( 1 x. %s )' % (B1, V1)), st([vc], 'mullidd', '( 1 x. %s ) = %s' % (V1, V1))], 'eqtrd', '%s = %s' % (B1, V1))
    b1c = st([v1, vc], 'eqeltrd', '%s e. CC' % B1)
    sn = st([st([fz['1 e. NN'], b1c], 'jca', '( 1 e. NN /\\ %s e. CC )' % B1),
             w.s([cg], 'sumsn', '( ( 1 e. NN /\\ %s e. CC ) -> sum_ r e. { 1 } ( ( 1 / r ) x. %s ) = %s )' % (B1, VLr('r'), B1))], 'syl',
            'sum_ r e. { 1 } ( ( 1 / r ) x. %s ) = %s' % (VLr('r'), B1))
    sm = st([st([e3, sn], 'eqtrd', '%s = %s' % (SUMV, B1)), v1], 'eqtrd', '%s = %s' % (SUMV, V1))
    IT = '( 1 / %s )' % TPI
    r1 = st([sm], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (IT, SUMV, IT, V1))
    assert '( %s x. %s )' % (IT, V1) == L.ECTRH
    rhs = st([r1], 'oveq1d', '( ( %s x. %s ) + %s ) = ( %s + %s )' % (IT, SUMV, L.EPH(), L.ECTRH, L.EPH()))
    x1 = st([st([lhs], 'eqcomd', '( %s + %s ) = ( %s + ( %s x. %s ) )' % (L.FDVH, E1_, L.FDVH, E1_, P1S)), di], 'eqtrd',
            '( %s + %s ) = ( ( %s x. %s ) + %s )' % (L.FDVH, E1_, IT, SUMV, L.EPH()))
    s = st([x1, rhs], 'eqtrd', '( %s + %s ) = ( %s + %s )' % (L.FDVH, E1_, L.ECTRH, L.EPH()))
    L.toqed(w, s, 'dshdih')
    return w


if __name__ == '__main__':
    run(dshdih())
