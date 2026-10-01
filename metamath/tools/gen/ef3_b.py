"""Sortie EF3: continuity of the strip integrand (ef3ldc, Lean contOn_vert_stripInt)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
import lin
lin.FASTPATH = True

DF = '( CC _D F )'


def ld0_elim(w, A, u, uin):
    """from uin : ( A -> u e. LD0 ): ( A -> u e. HP0 ), ( A -> ( F ` u ) =/= 0 )"""
    s = St(w, A)
    e = w.s([w.s([w.s([], 'fveq2', '( v = %s -> ( F ` v ) = ( F ` %s ) )' % (u, u))], 'neeq1d', '( v = %s -> ( ( F ` v ) =/= 0 <-> ( F ` %s ) =/= 0 ) )' % (u, u))],
            'elrab', '( %s e. %s <-> ( %s e. %s /\\ ( F ` %s ) =/= 0 ) )' % (u, LD0, u, HP0, u))
    b = s([uin, e], 'sylib', '( %s e. %s /\\ ( F ` %s ) =/= 0 )' % (u, HP0, u))
    return s([b, w.inst('simpl')], 'syl', '%s e. %s' % (u, HP0)), s([b, w.inst('simpr')], 'syl', '( F ` %s ) =/= 0' % u)


def gen_ldc():
    w = W('ef3ldc', 'Lean ` contOn_vert_stripInt ` : the strip integrand ` ( F \' / F ) ( u ) Y ^ u / u ` is continuous on the zero-free part of the right half-plane.')
    A0, G = ante_of(S['ef3ldc'])
    s = St(w, A0)
    hol = s([], 'simpl', HOLF('F', HP0)); yp = s([], 'simpr', 'Y e. RR+')
    fcn = s([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0)
    dvh = s([hol, w.inst('ef2dvh')], 'syl', HOLF(DF, HP0))
    dcn = s([dvh, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (DF, HP0))
    ss = s([w.s([], 'ssrab2', '%s C_ %s' % (LD0, HP0))], 'a1i', '%s C_ %s' % (LD0, HP0))
    def resm(Fn, cn):
        rc = s([ss, cn, w.inst('rescncf')], 'sylc', '( %s |` %s ) e. ( %s -cn-> CC )' % (Fn, LD0, LD0))
        ff = s([cn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (Fn, HP0))
        eq = s([ff, ss], 'feqresmpt', '( %s |` %s ) = ( u e. %s |-> ( %s ` u ) )' % (Fn, LD0, LD0, Fn))
        return s([eq, rc], 'eqeltrrd', '( u e. %s |-> ( %s ` u ) ) e. ( %s -cn-> CC )' % (LD0, Fn, LD0))
    g1 = resm(DF, dcn)
    g2 = resm('F', fcn)
    A1 = '( %s /\\ u e. %s )' % (A0, LD0)
    s1 = St(w, A1)
    uin = s1([], 'simpr', 'u e. %s' % LD0)
    uh, fnz = ld0_elim(w, A1, 'u', uin)
    fc = s1([s1([lift(w, fcn, A1), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), uh], 'ffvelcdmd', '( F ` u ) e. CC')
    fd = s1([fc, fnz], 'eldifsnd', '( F ` u ) e. ( CC \\ { 0 } )')
    fm = s([fd], 'fmpttd', '( u e. %s |-> ( F ` u ) ) : %s --> ( CC \\ { 0 } )' % (LD0, LD0))
    dss = s([w.s([], 'difss', '( CC \\ { 0 } ) C_ CC')], 'a1i', '( CC \\ { 0 } ) C_ CC')
    g2b = s([fm, s([dss, g2, w.inst('cncfcdm')], 'syl2anc', '( ( u e. %s |-> ( F ` u ) ) e. ( %s -cn-> ( CC \\ { 0 } ) ) <-> ( u e. %s |-> ( F ` u ) ) : %s --> ( CC \\ { 0 } ) )' % (LD0, LD0, LD0, LD0))],
            'mpbird', '( u e. %s |-> ( F ` u ) ) e. ( %s -cn-> ( CC \\ { 0 } ) )' % (LD0, LD0))
    q = s([g1, g2b], 'divcncf', '( u e. %s |-> ( ( %s ` u ) / ( F ` u ) ) ) e. ( %s -cn-> CC )' % (LD0, DF, LD0))
    # Y ^ u / u
    A2 = '( %s /\\ z e. %s )' % (A0, LD0)
    s2 = St(w, A2)
    zh, _ = ld0_elim(w, A2, 'z', s2([], 'simpr', 'z e. %s' % LD0))
    e2 = s2([s2([], '0red', '0 e. RR') if False else s2([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % HP0)
    zz = s2([zh, e2], 'mpbid', '( z e. CC /\\ 0 < ( Re ` z ) )')
    zc = s2([zz, w.inst('simpl')], 'syl', 'z e. CC')
    rz = s2([s2([zz, w.inst('simpr')], 'syl', '0 < ( Re ` z )')], 'gt0ne0d', '( Re ` z ) =/= 0')
    r0 = w.s([w.s([], 'fveq2', '( z = 0 -> ( Re ` z ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( z = 0 -> ( Re ` z ) = 0 )')
    zn = s2([rz, w.s([r0], 'necon3i', '( ( Re ` z ) =/= 0 -> z =/= 0 )')], 'syl', 'z =/= 0')
    zd = s2([zc, zn], 'eldifsnd', 'z e. ( CC \\ { 0 } )')
    ld = s([w.s([zd], 'ex', '( %s -> ( z e. %s -> z e. ( CC \\ { 0 } ) ) )' % (A0, LD0))], 'ssrdv', '%s C_ ( CC \\ { 0 } )' % LD0)
    pk = s([yp, ld, w.inst('pkfcn')], 'syl2anc', '( z e. %s |-> ( ( Y ^c z ) / z ) ) e. ( %s -cn-> CC )' % (LD0, LD0))
    cb = w.s([w.s([w.s([], 'oveq2', '( z = u -> ( Y ^c z ) = ( Y ^c u ) )'), w.s([], 'id', '( z = u -> z = u )')], 'oveq12d', '( z = u -> ( ( Y ^c z ) / z ) = ( ( Y ^c u ) / u ) )')],
             'cbvmptv', '( z e. %s |-> ( ( Y ^c z ) / z ) ) = ( u e. %s |-> ( ( Y ^c u ) / u ) )' % (LD0, LD0))
    pk2 = s([s([cb], 'a1i', '( z e. %s |-> ( ( Y ^c z ) / z ) ) = ( u e. %s |-> ( ( Y ^c u ) / u ) )' % (LD0, LD0)), pk], 'eqeltrrd', '( u e. %s |-> ( ( Y ^c u ) / u ) ) e. ( %s -cn-> CC )' % (LD0, LD0))
    w.qed([q, pk2], 'mulcncf', S['ef3ldc'])
    return run8(w)


if __name__ == '__main__':
    gen_ldc()
