"""Sortie C10: the centre bound 1/2 <_ abs L ( 2 + i T ) (lchrlb)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
import congr as _cg
from c10_freeze import S as FS
from c9_h import c0_facts
import c9_h
patch_stmt(c9_h)
import lin
lin.FASTPATH = True

MUMAP = '( q e. NN |-> ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` q ) ) x. ( mmu ` q ) ) )'


def lval(w, A0, c0, re0, T=None):
    """( A0 -> ( LFN ` C0 ) = LSs(C0) ) and ( A0 -> ( C0 e. CC /\\ 1 < Re C0 ) )"""
    ch = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0), w.inst('elhp2')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (A0, C0, HP0, C0, C0))
    c0h = w.s([w.s([c0, w.s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A0, C0))], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (A0, C0, C0)), ch], 'mpbird', '( %s -> %s e. %s )' % (A0, C0, HP0))
    vx = w.s([w.s([], 'sumex', '%s e. _V' % LSs(C0))], 'a1i', '( %s -> %s e. _V )' % (A0, LSs(C0)))
    fv, val = _cg.mptval(w, A0, 's', HP0, LSs('s'), C0, c0h, exs=vx, gen=w.g)
    g1 = w.s([lin8(w, A0, [], '1 < 2', {}), re0], 'breqtrrd', '( %s -> 1 < ( Re ` %s ) )' % (A0, C0))
    z1 = w.s([c0, g1], 'jca', '( %s -> ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (A0, C0, C0))
    return fv, z1, c0h


def gen_lchrctr():
    w = W('lchrctr', 'The centre bound ` 1 / 2 <_ abs L ( 2 + i T ) ` for nonprincipal ` chi ` (Lean ` one_third_le_norm_LFunction_of_two_le_re ` has ` 1 / 3 ` ): ` L ` times the Moebius series is ` 1 ` ( ~ lchrmu ) and the Moebius series is at most ` zeta ( 2 ) <_ 2 ` in modulus ( ~ dserbnd ).')
    A0 = '( %s /\\ T e. RR )' % CHI
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); tr = s([], 'simpr', 'T e. RR')
    nx = s([chi, w.inst('simpl')], 'syl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )')
    c0, re0, im0 = c0_facts(w, A0, tr)
    fv, z1, c0h = lval(w, A0, c0, re0)
    AG = tsub(stmt('lchragr'), {'Z': C0})
    aga, agc = ante_of(AG)
    agr = s([s([chi, z1], 'jca', aga), w.inst('lchragr')], 'syl', agc)
    DS = agc.split(' = ', 1)[1]
    lds = s([fv, agr], 'eqtrd', '( %s ` %s ) = %s' % (LFN, C0, DS))
    MU = tsub(stmt('lchrmu'), {'Z': C0})
    mua, muc = ante_of(MU)
    mu = s([s([nx, z1], 'jca', mua), w.inst('lchrmu')], 'syl', muc)
    MS = muc.split(' x. sum_', 1)[0][2:]
    assert muc == '( %s x. %s ) = 1' % (MS, DS), muc
    # dserbnd on the Moebius coefficients
    cf = s([nx, w.inst('lchmucfb')], 'syl', '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (MUMAP, MUMAP))
    DB = tsub(stmt('dserbnd'), {'A': MUMAP, 'C': '1', 'Z': C0})
    dba, dbc = ante_of(DB)
    db = s([s([cf, z1], 'jca', dba), w.inst('dserbnd')], 'syl', dbc)
    SMA = 'sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u %s ) )' % (MUMAP, C0)
    Ak = '( %s /\\ k e. NN )' % A0
    mv = w.s([w.s([], 'simpr', '( %s -> k e. NN )' % Ak), w.inst('lchmuval')], 'syl', '( %s -> ( %s ` k ) = ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( mmu ` k ) ) )' % (Ak, MUMAP))
    mv2 = w.s([mv], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u %s ) ) = ( ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( mmu ` k ) ) x. ( k ^c -u %s ) ) )' % (Ak, MUMAP, C0, C0))
    se = s([mv2], 'sumeq2dv', '%s = %s' % (SMA, MS))
    RHS = dbc.split(' <_ ', 1)[1]
    # RHS = 1 x. ( 1 + ( 1 / ( ( Re ` C0 ) - 1 ) ) ) = 2
    r1 = s([re0], 'oveq1d', '( ( Re ` %s ) - 1 ) = ( 2 - 1 )' % C0)
    r2 = s([s([r1, s([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')], 'eqtrd', '( ( Re ` %s ) - 1 ) = 1' % C0)], 'oveq2d', '( 1 / ( ( Re ` %s ) - 1 ) ) = ( 1 / 1 )' % C0)
    r3 = s([r2, s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')], 'eqtrd', '( 1 / ( ( Re ` %s ) - 1 ) ) = 1' % C0)
    r4 = s([s([r3], 'oveq2d', '( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) = ( 1 + 1 )' % C0), s([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2')], 'eqtrd',
           '( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) = 2' % C0)
    r5 = s([s([r4], 'oveq2d', '%s = ( 1 x. 2 )' % RHS), s([s([], '2cnd', '2 e. CC')], 'mullidd', '( 1 x. 2 ) = 2')], 'eqtrd', '%s = 2' % RHS)
    mb0 = s([s([se], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (SMA, MS)), db], 'eqbrtrrd', '( abs ` %s ) <_ %s' % (MS, RHS))
    mb = s([mb0, r5], 'breqtrd', '( abs ` %s ) <_ 2' % MS)
    # abs MU x. abs DS = 1
    msc = s([s([cf, z1], 'jca', dba), w.inst('dsercl')], 'syl', '%s e. CC' % SMA)
    msc = s([s([se], 'eqcomd', '%s = %s' % (MS, SMA)), msc], 'eqeltrd', '%s e. CC' % MS)
    ne0 = tsub(stmt('lchrne0'), {'Z': C0})
    nea, nec = ante_of(ne0)
    dne = s([s([nx, z1], 'jca', nea), w.inst('lchrne0')], 'syl', nec)
    from c9_h import lf_hol
    hol = lf_hol(w, A0, chi)
    lfc = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), c0h], 'ffvelcdmd',
            '( %s ` %s ) e. CC' % (LFN, C0))
    dsc = s([lds, lfc], 'eqeltrrd', '%s e. CC' % DS)
    am = s([msc, dsc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (MS, DS, MS, DS))
    a1 = s([s([mu], 'fveq2d', '( abs ` ( %s x. %s ) ) = ( abs ` 1 )' % (MS, DS)), s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')], 'eqtrd',
           '( abs ` ( %s x. %s ) ) = 1' % (MS, DS))
    one = s([a1, am], 'eqtr3d', '1 = ( ( abs ` %s ) x. ( abs ` %s ) )' % (MS, DS))
    ADS = '( abs ` %s )' % DS
    adr = s([dsc], 'abscld', '%s e. RR' % ADS)
    le = s([s([msc], 'abscld', '( abs ` %s ) e. RR' % MS), s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), adr, s([dsc], 'absge0d', '0 <_ %s' % ADS), mb], 'lemul1ad',
           '( ( abs ` %s ) x. %s ) <_ ( 2 x. %s )' % (MS, ADS, ADS))
    le1 = s([one, le], 'eqbrtrd', '1 <_ ( 2 x. %s )' % ADS)
    h = lin8(w, A0, [le1], '( 1 / 2 ) <_ %s' % ADS, {ADS: adr})
    goal = '( %s -> ( 1 / 2 ) <_ ( abs ` ( %s ` %s ) ) )' % (A0, LFN, C0)
    assert goal == FS['lchrctr']
    w.qed([h, s([lds], 'fveq2d', '( abs ` ( %s ` %s ) ) = %s' % (LFN, C0, ADS))], 'breqtrrd', goal)
    return run8(w)


if __name__ == '__main__':
    gen_lchrctr()
