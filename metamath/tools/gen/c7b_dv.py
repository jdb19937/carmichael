"""C7b section 5: the logarithmic derivative of L ( chi ) (lchrdvval, lchrlogdv)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
import congr as _cg
from c7b_lch import val, ex_, NXZ, vmtcl
lin.FASTPATH = True

HPT = HP()
NXT = '( %s /\\ ( %s /\\ Z e. %s ) )' % (NX, T1, HPT)
DER = '( ( CC _D %s ) ` Z )' % LSFX
LSA = '( z e. %s |-> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u z ) ) )' % (HPT, AX)


def ctx(w, A0):
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    t1 = w.s([], 'simprl', '( %s -> %s )' % (A0, T1))
    zh = w.s([], 'simprr', '( %s -> Z e. %s )' % (A0, HPT))
    tr = w.s([t1, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
    tg = w.s([t1, w.inst('simpr')], 'syl', '( %s -> 1 < T )' % A0)
    bi = w.s([tr, w.inst('elhp2')], 'syl', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ T < %s ) ) )' % (A0, HPT, RZ))
    zz = w.s([zh, bi], 'mpbid', '( %s -> ( Z e. CC /\\ T < %s ) )' % (A0, RZ))
    zc = w.s([zz], 'simpld', '( %s -> Z e. CC )' % A0)
    tz = w.s([zz], 'simprd', '( %s -> T < %s )' % (A0, RZ))
    z1 = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), tr, w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ)), tg, tz], 'lttrd', '( %s -> 1 < %s )' % (A0, RZ))
    zp = w.s([zc, z1], 'jca', '( %s -> %s )' % (A0, ZP1))
    return nx, t1, zh, zc, zp


if __name__ == '__main__' and (not only or 'lchrdvval' in only):
    w = W('lchrdvval', 'The derivative of ` L ( chi ) ` on ` Re > T > 1 ` is ` -u L ( chi log ) ` (C5\'s ~ dserdvval at the character).')
    A0 = NXT
    nx, t1, zh, zc, zp = ctx(w, A0)
    cfb = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX(AX, '1')))
    RAW = '-u sum_ k e. NN ( ( ( %s ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) )' % AX
    dv = w.s([w.s([w.s([cfb, t1], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CFBX(AX, '1'), T1)), zh], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ Z e. %s ) )' % (A0, CFBX(AX, '1'), T1, HPT)),
              w.inst('dserdvval')], 'syl', '( %s -> ( ( CC _D %s ) ` Z ) = %s )' % (A0, LSA, RAW))
    Az = '( %s /\\ z e. %s )' % (A0, HPT)
    Azk = '( %s /\\ k e. NN )' % Az
    nxk = w.s([w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Az, NX))], 'adantr', '( %s -> %s )' % (Azk, NX)), w.s([], 'simpr', '( %s -> k e. NN )' % Azk)], 'jca',
              '( %s -> ( %s /\\ k e. NN ) )' % (Azk, NX))
    vk = w.s([nxk, w.inst('lchrval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Azk, AX, CHV('k')))
    inner = w.s([w.s([vk], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u z ) ) = %s )' % (Azk, AX, CHT('k', 'z')))], 'sumeq2dv',
                '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u z ) ) = sum_ k e. NN %s )' % (Az, AX, CHT('k', 'z')))
    meq = w.s([inner], 'mpteq2dva', '( %s -> %s = %s )' % (A0, LSA, LSFX))
    deq = w.s([w.s([meq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, LSA, LSFX))], 'fveq1d', '( %s -> ( ( CC _D %s ) ` Z ) = %s )' % (A0, LSA, DER))
    Ak = '( %s /\\ k e. NN )' % A0
    nxk2 = w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX)), w.s([], 'simpr', '( %s -> k e. NN )' % Ak)], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, NX))
    vk2 = w.s([nxk2, w.inst('lchrval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak, AX, CHV('k')))
    t = w.s([w.s([w.s([vk2], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( log ` k ) ) = ( %s x. ( log ` k ) ) )' % (Ak, AX, CHV('k')))], 'oveq1d',
                 '( %s -> ( ( ( %s ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) ) = %s )' % (Ak, AX, LGT('k')))], 'sumeq2dv',
            '( %s -> sum_ k e. NN ( ( ( %s ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) ) = sum_ k e. NN %s )' % (A0, AX, LGT('k')))
    ng = w.s([t], 'negeqd', '( %s -> %s = -u sum_ k e. NN %s )' % (A0, RAW, LGT('k')))
    w.qed([w.s([deq, dv], 'eqtr3d', '( %s -> %s = %s )' % (A0, DER, RAW)), ng], 'eqtrd', '( %s -> %s = -u sum_ k e. NN %s )' % (A0, DER, LGT('k')))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchrlogdv' in only):
    w = W('lchrlogdv', 'The logarithmic derivative ` L\' / L ( chi ) = -u L ( chi Lam ) ` on ` Re > T > 1 ` '
          '(Mathlib ` LSeries_twist_vonMangoldt_eq ` divided by ` L ( chi ) =/= 0 ` ).')
    A0 = NXT
    nx, t1, zh, zc, zp = ctx(w, A0)
    nxz = w.s([nx, zp], 'jca', '( %s -> %s )' % (A0, NXZ))
    SV = 'sum_ k e. NN %s' % VMT('k')
    SC = 'sum_ k e. NN %s' % CHT('k')
    SL = 'sum_ k e. NN %s' % LGT('k')
    dv = w.s([], 'lchrdvval', '( %s -> %s = -u %s )' % (A0, DER, SL))
    cv = w.s([nxz, w.inst('lchrconv')], 'syl', '( %s -> ( %s x. %s ) = %s )' % (A0, SV, SC, SL))
    ne = w.s([nxz, w.inst('lchrne0')], 'syl', '( %s -> %s =/= 0 )' % (A0, SC))
    # SV e. CC by isumcl, SC e. CC by dsercl
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    vc = vmtcl(w, Ak, 'k', w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX)), kn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))
    vv, _ = val(w, Ak, VMT('n'), 'k', kn, ex_(w, Ak, VMT('k'), vc))
    svc = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0), vv, vc, w.s([nxz, w.inst('lchvmcvg')], 'syl',
               '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (A0, VMT('n')))], 'isumcl', '( %s -> %s e. CC )' % (A0, SV))
    Ak2 = Ak
    nxk = w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX)), kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, NX))
    ck = w.s([nxk, w.inst('lchrval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak, AX, CHV('k')))
    s3 = w.s([w.s([ck], 'oveq1d', '( %s -> %s = %s )' % (Ak, TRM(AX, 'k'), CHT('k')))], 'sumeq2dv', '( %s -> %s = %s )' % (A0, SER(AX), SC))
    cfb = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX(AX, '1')))
    c2 = w.s([w.s([cfb, zp], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CFBX(AX, '1'), ZP1)), w.inst('dsercl')], 'syl', '( %s -> %s e. CC )' % (A0, SER(AX)))
    scc = w.s([s3, c2], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, SC))
    q1 = w.s([dv], 'oveq1d', '( %s -> ( %s / %s ) = ( -u %s / %s ) )' % (A0, DER, SC, SL, SC))
    slc = w.s([cv, w.s([svc, scc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A0, SV, SC))], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, SL))
    q2 = w.s([slc, scc, ne], 'divnegd', '( %s -> -u ( %s / %s ) = ( -u %s / %s ) )' % (A0, SL, SC, SL, SC))
    q3a = w.s([w.s([cv], 'oveq1d', '( %s -> ( ( %s x. %s ) / %s ) = ( %s / %s ) )' % (A0, SV, SC, SC, SL, SC)),
               w.s([svc, scc, ne], 'divcan4d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (A0, SV, SC, SC, SV))], 'eqtr3d', '( %s -> ( %s / %s ) = %s )' % (A0, SL, SC, SV))
    q3 = w.s([q3a], 'negeqd', '( %s -> -u ( %s / %s ) = -u %s )' % (A0, SL, SC, SV))
    w.qed([q1, w.s([q2, q3], 'eqtr3d', '( %s -> ( -u %s / %s ) = -u %s )' % (A0, SL, SC, SV))], 'eqtrd', '( %s -> ( %s / %s ) = -u %s )' % (A0, DER, SC, SV))
    run7b(w)
