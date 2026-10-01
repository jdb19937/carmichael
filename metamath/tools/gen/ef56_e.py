"""Sortie EF56: the zeta right edge (ef6rm: the middle is minus the Perron sum)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from cl import lift, Closure
import congr as _cg
from c8_o import numst
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_b import LD0F, abs_ne0
import ef1lib as _ef1


def hd_cont(w, A0, yp, Aa, Bb, ac, bc, seg):
    """( A0 -> HD e. ( D2 -cn-> CC ) ) and the lint difference, via ef6ldf; seg : ( A0 -> ( Aa cseg Bb ) C_ D2 )"""
    c = Ctx(w, A0)
    he = c([hol_eta(w, A0), yp, w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (HE, LD0E))
    hg = c([hol_gf(w, A0), yp, w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (HG, LD0G))
    LF = tsub(stmt('ef6ldf'), {'A': Aa, 'B': Bb, 'F': HE, 'G': HG, 'D': LD0E, 'E': LD0G})
    la, lc_ = ante_of(LF)
    st = c([c([c([ac, bc], 'jca', top_and(la)[0]), c([he, hg], 'jca', top_and(la)[1]), seg], '3jca', la), w.inst('ef6ldf')], 'syl', lc_)
    cn = c([st, w.inst('simpl')], 'syl', top_and(lc_)[0])
    df = c([st, w.inst('simpr')], 'syl', top_and(lc_)[1])
    return cn, df, he, hg


def gen_rm():
    w = W('ef6rm', 'The middle of the zeta right edge (Lean ` contour_zeta ` , ` hJmid ` ): on ` Re = C > 1 ` the difference of the strip integrands of ` eta ` and ` g ` is minus the Perron integrand of the character mod 1 ( ~ ef6pt ), so its line integral from ` C - i T ` to ` C + i T ` is minus the Perron sum ( ~ ef1redge ).')
    A0, G = ante_of(S['ef6rm'])
    c = Ctx(w, A0)
    yp = c.g('Y e. RR+'); cr = c.g('C e. RR'); c1_ = c.g('1 < C'); tr = c.g('T e. RR')
    Aa, Bb = _ef1.LO('C', 'T'), _ef1.HI('C', 'T')
    ntr = c([tr], 'renegcld', '-u T e. RR')
    ac, bc = ptc(c, 'C', '-u T', cr, ntr), ptc(c, 'C', 'T', cr, tr)
    PT_ = '( %s + ( t x. ( %s - %s ) ) )' % (Aa, Bb, Aa)
    M = '( -u T + ( t x. ( T - -u T ) ) )'
    A1 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A0
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    tr1 = c1([c1([], 'simpr', 't e. ( 0 [,] 1 )'), w.inst('elunitrn')], 'syl', 't e. RR')
    cl = Closure(w, A1, {'C': ('RR', L1(cr)), 'T': ('RR', L1(tr)), 't': ('RR', tr1), '_i': ('CC', ic_(c1))})
    for k in ('C', 'T', 't', '_i'):
        cl.atom(k)
    e1 = ringeq(w, A1, PT_, PTL('C', M), cl)
    mr = cl.mem(M, 'RR')
    z = PTL('C', M)
    zc = ptc(c1, 'C', M, L1(cr), mr)
    rz = c1([L1(cr), mr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = C' % z)
    ptc_ = c1([e1, zc], 'eqeltrd', '%s e. CC' % PT_)
    rp = c1([c1([e1], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (PT_, z)), rz], 'eqtrd', '( Re ` %s ) = C' % PT_)
    r1p = c1([L1(c1_), c1([rp], 'eqcomd', 'C = ( Re ` %s )' % PT_)], 'breqtrd', '1 < ( Re ` %s )' % PT_)
    PTS = tsub(S['ef6pt'], {'Z': PT_})
    pa, pc = ante_of(PTS)
    pt = c1([c1([L1(yp), c1([ptc_, r1p], 'jca', top_and(pa)[1])], 'jca', pa), w.inst('ef6pt')], 'syl', pc)
    mem1 = c1([pt, w.inst('simpl')], 'syl', '%s e. %s' % (PT_, D2))
    hv1 = c1([pt, w.inst('simpr')], 'syl', top_and(pc)[1])
    seg = seg_sub(w, A0, Aa, Bb, ac, bc, D2, lambda A: mem1)
    hcn, _, _, _ = hd_cont(w, A0, yp, Aa, Bb, ac, bc, seg)
    DF = '( %s - %s )' % (Bb, Aa)
    HINT = '( ( %s ` %s ) x. %s )' % (HD, PT_, DF)
    RINT = '( ( %s ` %s ) x. %s )' % (RHZ, PT_, DF)
    ibl = c([c([c([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (Aa, Bb)), c([hcn, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (HD, D2, Aa, Bb, D2))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (Aa, Bb, HD, D2, Aa, Bb, D2)), w.inst('lintibl')], 'syl',
            '( t e. ( 0 (,) 1 ) |-> %s ) e. L^1' % HINT)
    # pointwise: RINT = -u HINT
    YQ = '( ( Y ^c %s ) / %s )' % (PT_, PT_)
    DZ = DLVZ(PT_)
    rpr = c1([ptc_], 'recld', '( Re ` %s ) e. RR' % PT_)
    r0p = lin8(w, A1, [r1p], '0 < ( Re ` %s )' % PT_, {'( Re ` %s )' % PT_: rpr})
    pne = ne0_re(c1, PT_, ptc_, r0p)
    pd = c1([ptc_, pne], 'eldifsnd', '%s e. ( CC \\ { 0 } )' % PT_)
    rv, _ = _cg.mptval(w, A1, 'z', '( CC \\ { 0 } )', '( %s x. ( ( Y ^c z ) / z ) )' % DLVZ('z'), PT_, pd, gen=w.g)
    dfc = c1([L1(bc), L1(ac)], 'subcld', '%s e. CC' % DF)
    dzc = dlvz_cc(w, A1, PT_, ptc_, r1p)
    yqc = c1([c1([c1([L1(yp)], 'rpcnd', 'Y e. CC'), ptc_], 'cxpcld', '( Y ^c %s ) e. CC' % PT_), ptc_, pne], 'divcld', '%s e. CC' % YQ)
    RV = '( %s x. %s )' % (DZ, YQ)
    rvc = c1([dzc, yqc], 'mulcld', '%s e. CC' % RV)
    hi = c1([c1([hv1], 'oveq1d', '%s = ( -u %s x. %s )' % (HINT, RV, DF)), c1([rvc, dfc], 'mulneg1d', '( -u %s x. %s ) = -u ( %s x. %s )' % (RV, DF, RV, DF))], 'eqtrd', '%s = -u ( %s x. %s )' % (HINT, RV, DF))
    ri = c1([rv], 'oveq1d', '%s = ( %s x. %s )' % (RINT, RV, DF))
    hi2 = c1([hi, c1([ri], 'negeqd', '-u %s = -u ( %s x. %s )' % (RINT, RV, DF))], 'eqtr4d', '%s = -u %s' % (HINT, RINT))
    rc = c1([ri, c1([rvc, dfc], 'mulcld', '( %s x. %s ) e. CC' % (RV, DF))], 'eqeltrd', '%s e. CC' % RINT)
    hic = c1([hi2, c1([rc], 'negcld', '-u %s e. CC' % RINT)], 'eqeltrd', '%s e. CC' % HINT)
    rneg = c1([c1([c1([hi2], 'negeqd', '-u %s = -u -u %s' % (HINT, RINT)), c1([rc], 'negnegd', '-u -u %s = %s' % (RINT, RINT))], 'eqtrd', '-u %s = %s' % (HINT, RINT))], 'eqcomd', '%s = -u %s' % (RINT, HINT))
    rneg_o = open_to_closed(w, A0, rneg)
    hic_o = open_to_closed(w, A0, hic)
    X = '( 0 (,) 1 )'
    ieq = c([rneg_o], 'itgeq2dv', 'S. %s %s _d t = S. %s -u %s _d t' % (X, RINT, X, HINT))
    ing = c([hic_o, ibl], 'itgneg', '-u S. %s %s _d t = S. %s -u %s _d t' % (X, HINT, X, HINT))
    RHL = '( %s lint <. %s , %s >. )' % (RHZ, Aa, Bb)
    HDL = '( %s lint <. %s , %s >. )' % (HD, Aa, Bb)
    lvr = c([c.a1(w.s([], 'mptex', '%s e. _V' % RHZ), '%s e. _V' % RHZ), ac, bc, w.inst('lintval')], 'syl3anc', '%s = S. %s %s _d t' % (RHL, X, RINT))
    lvh = c([c([hcn], 'elexd', '%s e. _V' % HD), ac, bc, w.inst('lintval')], 'syl3anc', '%s = S. %s %s _d t' % (HDL, X, HINT))
    e2 = c([c([lvr, ieq], 'eqtrd', '%s = S. %s -u %s _d t' % (RHL, X, HINT)), c([c([ing], 'eqcomd', 'S. %s -u %s _d t = -u S. %s %s _d t' % (X, HINT, X, HINT)),
                                                                                    c([lvh], 'negeqd', '-u %s = -u S. %s %s _d t' % (HDL, X, HINT))], 'eqtr4d', 'S. %s -u %s _d t = -u %s' % (X, HINT, HDL))], 'eqtrd', '%s = -u %s' % (RHL, HDL))
    RE = tsub(stmt('ef1redge'), Z1S)
    rea, rec_ = ante_of(RE)
    red = c([c([nx1(w, A0), c([c([yp, cr, c1_], '3jca', '( Y e. RR+ /\\ C e. RR /\\ 1 < C )'), tr], 'jca', top_and(rea)[1])], 'jca', rea), w.inst('ef1redge')], 'syl', rec_)
    ps = c([red, w.inst('simpr')], 'syl', top_and(rec_)[1])
    e3 = c([ps, e2], 'eqtrd', '%s = -u %s' % (PSZ('C'), HDL))
    hlc = c([c([c([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (Aa, Bb)), c([hcn, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (HD, D2, Aa, Bb, D2))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (Aa, Bb, HD, D2, Aa, Bb, D2)), w.inst('lintcl')], 'syl', '%s e. CC' % HDL)
    e4 = c([c([e3], 'negeqd', '-u %s = -u -u %s' % (PSZ('C'), HDL)), c([hlc], 'negnegd', '-u -u %s = %s' % (HDL, HDL))], 'eqtrd', '-u %s = %s' % (PSZ('C'), HDL))
    w.qed([e4], 'eqcomd', S['ef6rm'])
    return run8(w)


def gen_rx():
    w = W('ef6rx', 'Lean ` right_extra_le ` at the character mod 1 (zeta, through ` eta ` and ` g ` ): on a piece of ` Re = c ` of length at most 1 where ` T <_ abs t ` , the difference of the strip integrands of ` eta ` and ` g ` has line integral at most ` 8 Y log Y / T ` ( ~ ef6pt , ~ lvmabs , ~ vmsharp ; Lean ` 18 Y log ^ 2 Y / T ` ).')
    A00, G = ante_of(S['ef6rx'])
    pa = top_and(A00)
    A0 = '( %s /\\ %s /\\ A. y e. ( U [,] V ) T <_ ( abs ` y ) )' % (pa[0], pa[1])
    c = Ctx(w, A0)
    yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t0 = c.g('0 < T')
    ur = c.g('U e. RR'); vr = c.g('V e. RR'); uv = c.g('U <_ V'); vu1 = c.g('( V - U ) <_ 1')
    aly = c.g('A. y e. ( U [,] V ) T <_ ( abs ` y )')
    l4 = c([c([yr, y100], 'jca', '( Y e. RR /\\ ; ; 1 0 0 <_ Y )'), w.inst('ef1l4')], 'syl', '4 <_ ( log ` Y )')
    y1 = lin8(w, A0, [y100], '1 < Y', {'Y': yr})
    yp = c([yr, lin8(w, A0, [y100], '0 < Y', {'Y': yr})], 'elrpd', 'Y e. RR+')
    L = '( log ` Y )'
    lr = c([c([yr, y1], 'rplogcld', '%s e. RR+' % L)], 'rpred', '%s e. RR' % L)
    lp = c([yr, y1], 'rplogcld', '%s e. RR+' % L)
    UP = '( 1 / %s )' % L
    upp = c([lp], 'rpreccld', '%s e. RR+' % UP)
    C1_ = C1
    c1r = c([c.a1(w.s([], '1re', '1 e. RR'), '1 e. RR'), c([upp], 'rpred', '%s e. RR' % UP)], 'readdcld', '%s e. RR' % C1_)
    c1g = lin8(w, A0, [c([upp], 'rpgt0d', '0 < %s' % UP)], '1 < %s' % C1_, {UP: c([upp], 'rpred', '%s e. RR' % UP)})
    # 1 / log Y <_ 1 / 4 <_ 1
    lg1 = lin8(w, A0, [l4], '1 <_ %s' % L, {L: lr})
    up1 = c([c([lg1, c([c.a1(w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), lp], 'lerecd', '( 1 <_ %s <-> ( 1 / %s ) <_ ( 1 / 1 ) )' % (L, L))], 'mpbid', '( 1 / %s ) <_ ( 1 / 1 )' % L), c.a1(w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')], 'breqtrd', '%s <_ 1' % UP)
    yc = c([c([yr, y1], 'jca', '( Y e. RR /\\ 1 < Y )'), w.inst('ef1yc')], 'syl', ante_of(stmt('ef1yc'))[1])
    yc3 = c([yc, w.inst('simpr')], 'syl', '( Y ^c %s ) <_ ( 3 x. Y )' % C1_)
    ldc = hd_cn(w, A0, yp)
    BB = '( 8 x. ( ( Y x. %s ) / T ) )' % L
    tp = c([tr, t0], 'elrpd', 'T e. RR+')
    bbr = c([numst(w, A0, '8', 'RR'), c([c([yr, lr], 'remulcld', '( Y x. %s ) e. RR' % L), tp], 'rerpdivcld', '( ( Y x. %s ) / T ) e. RR' % L)], 'remulcld', '%s e. RR' % BB)
    # pointwise on t e. [U, V]
    A1 = '( %s /\\ t e. ( U [,] V ) )' % A0
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    tin = c1([], 'simpr', 't e. ( U [,] V )')
    tr1, _, _ = icc_out(c1, 't', 'U', 'V', tin, L1(ur), L1(vr))
    z = PTL(C1_, 't')
    zc = ptc(c1, C1_, 't', L1(c1r), tr1)
    rzs = c1([L1(c1r), tr1, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (z, C1_))
    d = {'rz': rzs}
    r1 = c1([L1(c1g), c1([rzs], 'eqcomd', '%s = ( Re ` %s )' % (C1_, z))], 'breqtrd', '1 < ( Re ` %s )' % z)
    PTS = tsub(S['ef6pt'], {'Z': z})
    pa_, pc_ = ante_of(PTS)
    ptst = c1([c1([L1(yp), c1([zc, r1], 'jca', top_and(pa_)[1])], 'jca', pa_), w.inst('ef6pt')], 'syl', pc_)
    zin = c1([ptst, w.inst('simpl')], 'syl', '%s e. %s' % (z, D2))
    hv = c1([ptst, w.inst('simpr')], 'syl', top_and(pc_)[1])
    Q = DLVZ(z)
    qc = dlvz_cc(w, A1, z, zc, r1)
    LVA = tsub(stmt('lvmabs'), {'N': '1', 'X': U1, 'Z': z})
    lvaa, lvac = ante_of(LVA)
    lva = c1([c1([nx1(w, A1), c1([zc, r1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (z, z))], 'jca', lvaa), w.inst('lvmabs')], 'syl', lvac)
    RVS = lvac.split(' <_ ', 1)[1]
    VM = 'sum_ k e. NN ( ( Lam ` k ) x. ( k ^c -u %s ) )' % C1_
    rvs = c1([c1([c1([c1([rzs], 'negeqd', '-u ( Re ` %s ) = -u %s' % (z, C1_))], 'oveq2d', '( k ^c -u ( Re ` %s ) ) = ( k ^c -u %s )' % (z, C1_))], 'oveq2d',
                 '( ( Lam ` k ) x. ( k ^c -u ( Re ` %s ) ) ) = ( ( Lam ` k ) x. ( k ^c -u %s ) )' % (z, C1_))], 'sumeq2sdv', '%s = %s' % (RVS, VM))
    b1 = c1([lva, rvs], 'breqtrd', '( abs ` %s ) <_ %s' % (Q, VM))
    F54 = '( 5 / 4 )'
    GB = '( ( %s / %s ) + 5 )' % (F54, UP)
    vmr = c1([c1([L1(upp), L1(up1)], 'jca', '( %s e. RR+ /\\ %s <_ 1 )' % (UP, UP)), w.inst('vmsharp')], 'syl', '%s <_ %s' % (VM, GB))
    lx = w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')
    b2x = c1([c1([vmr, w.s([lx], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (VM, GB, VM, GB))], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (VM, GB)), w.inst('simpl')], 'syl', '%s e. RR*' % VM)
    gbr = c1([c1([numst(w, A1, F54, 'RR'), L1(upp)], 'rerpdivcld', '( %s / %s ) e. RR' % (F54, UP)), numst(w, A1, '5', 'RR')], 'readdcld', '%s e. RR' % GB)
    lq = c1([c1([c1([qc], 'abscld', '( abs ` %s ) e. RR' % Q)], 'rexrd', '( abs ` %s ) e. RR*' % Q), b2x, c1([gbr], 'rexrd', '%s e. RR*' % GB), b1, vmr], 'xrletrd', '( abs ` %s ) <_ %s' % (Q, GB))
    rr = c1([c1([numst(w, A1, F54, 'CC'), c1([L1(upp)], 'rpcnd', '%s e. CC' % UP), c1([L1(upp)], 'rpne0d', '%s =/= 0' % UP)], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (F54, UP, F54, UP)),
             c1([c1([c1([L1(lp)], 'rpcnd', '%s e. CC' % L), c1([L1(lp)], 'rpne0d', '%s =/= 0' % L)], 'recrecd', '( 1 / %s ) = %s' % (UP, L))], 'oveq2d', '( %s x. ( 1 / %s ) ) = ( %s x. %s )' % (F54, UP, F54, L))],
            'eqtrd', '( %s / %s ) = ( %s x. %s )' % (F54, UP, F54, L))
    lq2 = c1([lq, c1([rr], 'oveq1d', '( ( %s / %s ) + 5 ) = ( ( %s x. %s ) + 5 )' % (F54, UP, F54, L))], 'breqtrd', '( abs ` %s ) <_ ( ( %s x. %s ) + 5 )' % (Q, F54, L))
    aq = c1([qc], 'abscld', '( abs ` %s ) e. RR' % Q)
    A52 = '( ( 5 / 2 ) x. %s )' % L
    lq3 = lin8(w, A1, [lq2, L1(l4)], '( abs ` %s ) <_ %s' % (Q, A52), {'( abs ` %s )' % Q: aq, L: L1(lr)})
    # abs ( Y ^ z / z ) <_ 3 ( Y / T )
    YZ = '( Y ^c %s )' % z
    yzc = c1([c1([L1(yp)], 'rpcnd', 'Y e. CC'), zc], 'cxpcld', '%s e. CC' % YZ)
    iz = c1([L1(c1r), tr1, w.inst('crim')], 'syl2anc', '( Im ` %s ) = t' % z)
    azr = c1([zc], 'abscld', '( abs ` %s ) e. RR' % z)
    aim = c1([c1([c1([zc], 'imcld', '( Im ` %s ) e. RR' % z)], 'recnd', '( Im ` %s ) e. CC' % z)], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % z)
    tt, _ = ral_at(w, A1, L1(aly), 'y', 't', 'T <_ ( abs ` y )', tin)
    le1 = c1([tt, c1([c1([iz], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` t )' % z)], 'eqcomd', '( abs ` t ) = ( abs ` ( Im ` %s ) )' % z)], 'breqtrd', 'T <_ ( abs ` ( Im ` %s ) )' % z)
    le2 = c1([zc, w.inst('absimle')], 'syl', '( abs ` ( Im ` %s ) ) <_ ( abs ` %s )' % (z, z))
    tle = lin8(w, A1, [le1, le2], 'T <_ ( abs ` %s )' % z, {'T': L1(tr), '( abs ` ( Im ` %s ) )' % z: aim, '( abs ` %s )' % z: azr})
    azp = c1([azr, lin8(w, A1, [L1(t0), tle], '0 < ( abs ` %s )' % z, {'T': L1(tr), '( abs ` %s )' % z: azr})], 'elrpd', '( abs ` %s ) e. RR+' % z)
    zne = abs_ne0(c1, z, zc, azp)
    YQ = '( %s / %s )' % (YZ, z)
    ay = c1([c1([yzc, zc, zne], 'absdivd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (YQ, YZ, z)),
             c1([c1([c1([L1(yp), zc, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( Y ^c ( Re ` %s ) )' % (YZ, z)), c1([d['rz']], 'oveq2d', '( Y ^c ( Re ` %s ) ) = ( Y ^c %s )' % (z, C1_))], 'eqtrd',
                   '( abs ` %s ) = ( Y ^c %s )' % (YZ, C1_))], 'oveq1d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( Y ^c %s ) / ( abs ` %s ) )' % (YZ, z, C1_, z))], 'eqtrd',
            '( abs ` %s ) = ( ( Y ^c %s ) / ( abs ` %s ) )' % (YQ, C1_, z))
    ycr = c1([c1([L1(yp), L1(c1r)], 'rpcxpcld', '( Y ^c %s ) e. RR+' % C1_)], 'rpred', '( Y ^c %s ) e. RR' % C1_)
    y3r = c1([numst(w, A1, '3', 'RR'), L1(yr)], 'remulcld', '( 3 x. Y ) e. RR')
    b1 = c1([ycr, y3r, azp, L1(yc3)], 'lediv1dd', '( ( Y ^c %s ) / ( abs ` %s ) ) <_ ( ( 3 x. Y ) / ( abs ` %s ) )' % (C1_, z, z))
    y30 = lin8(w, A1, [L1(y100)], '0 <_ ( 3 x. Y )', {'Y': L1(yr)})
    b2 = c1([L1(tp), azp, y3r, y30, tle], 'lediv2ad', '( ( 3 x. Y ) / ( abs ` %s ) ) <_ ( ( 3 x. Y ) / T )' % z)
    b3 = c1([numst(w, A1, '3', 'CC'), c1([L1(yr)], 'recnd', 'Y e. CC'), c1([L1(tp)], 'rpcnd', 'T e. CC'), c1([L1(tp)], 'rpne0d', 'T =/= 0')], 'divassd', '( ( 3 x. Y ) / T ) = ( 3 x. ( Y / T ) )')
    YT_ = '( Y / T )'
    ytr = c1([L1(yr), L1(tp)], 'rerpdivcld', '%s e. RR' % YT_)
    bq = le_tr(w, A1, c1([ay, b1], 'eqbrtrd', '( abs ` %s ) <_ ( ( 3 x. Y ) / ( abs ` %s ) )' % (YQ, z)), '( abs ` %s )' % YQ, '( ( 3 x. Y ) / ( abs ` %s ) )' % z, c1([b2, b3], 'breqtrd', '( ( 3 x. Y ) / ( abs ` %s ) ) <_ ( 3 x. %s )' % (z, YT_)), '( 3 x. %s )' % YT_)
    yqc = c1([yzc, zc, zne], 'divcld', '%s e. CC' % YQ)
    HZ = '( %s ` %s )' % (HD, z)
    a1 = c1([c1([c1([hv], 'fveq2d', '( abs ` %s ) = ( abs ` -u ( %s x. %s ) )' % (HZ, Q, YQ)), c1([c1([qc, yqc], 'mulcld', '( %s x. %s ) e. CC' % (Q, YQ))], 'absnegd', '( abs ` -u ( %s x. %s ) ) = ( abs ` ( %s x. %s ) )' % (Q, YQ, Q, YQ))], 'eqtrd', '( abs ` %s ) = ( abs ` ( %s x. %s ) )' % (HZ, Q, YQ)),
             c1([qc, yqc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (Q, YQ, Q, YQ))], 'eqtrd',
            '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (HZ, Q, YQ))
    m = c1([aq, c1([numst(w, A1, '( 5 / 2 )', 'RR'), L1(lr)], 'remulcld', '%s e. RR' % A52), c1([yqc], 'abscld', '( abs ` %s ) e. RR' % YQ),
            c1([numst(w, A1, '3', 'RR'), ytr], 'remulcld', '( 3 x. %s ) e. RR' % YT_), c1([qc], 'absge0d', '0 <_ ( abs ` %s )' % Q), c1([yqc], 'absge0d', '0 <_ ( abs ` %s )' % YQ), lq3, bq], 'lemul12ad',
           '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( %s x. ( 3 x. %s ) )' % (Q, YQ, A52, YT_))
    W1 = '( %s x. %s )' % (YT_, L)
    cl = Closure(w, A1, {YT_: ('RR', ytr), L: ('RR', L1(lr))}); cl.atom(YT_); cl.atom(L)
    e1 = ringeq(w, A1, '( %s x. ( 3 x. %s ) )' % (A52, YT_), '( ( ; 1 5 / 2 ) x. %s )' % W1, cl)
    w1r = cl.mem(W1, 'RR')
    yt0 = c1([L1(yr), L1(tp), lin8(w, A1, [L1(y100)], '0 <_ Y', {'Y': L1(yr)})], 'divge0d', '0 <_ %s' % YT_)
    w10 = c1([ytr, L1(lr), yt0, lin8(w, A1, [L1(l4)], '0 <_ %s' % L, {L: L1(lr)})], 'mulge0d', '0 <_ %s' % W1)
    e2 = lin8(w, A1, [w10], '( ( ; 1 5 / 2 ) x. %s ) <_ ( 8 x. %s )' % (W1, W1), {W1: w1r})
    dv = c1([c1([L1(yr)], 'recnd', 'Y e. CC'), c1([L1(lr)], 'recnd', '%s e. CC' % L), c1([L1(tp)], 'rpcnd', 'T e. CC'), c1([L1(tp)], 'rpne0d', 'T =/= 0')], 'div23d', '( ( Y x. %s ) / T ) = ( ( Y / T ) x. %s )' % (L, L))
    e3 = c1([e2, c1([c1([dv], 'eqcomd', '%s = ( ( Y x. %s ) / T )' % (W1, L))], 'oveq2d', '( 8 x. %s ) = %s' % (W1, BB))], 'breqtrd', '( ( ; 1 5 / 2 ) x. %s ) <_ %s' % (W1, BB))
    f1 = c1([c1([a1, m], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( 3 x. %s ) )' % (HZ, A52, YT_)), e1], 'breqtrd', '( abs ` %s ) <_ ( ( ; 1 5 / 2 ) x. %s )' % (HZ, W1))
    f2 = le_tr(w, A1, f1, '( abs ` %s )' % HZ, '( ( ; 1 5 / 2 ) x. %s )' % W1, e3, BB)
    pt = c1([zin, f2], 'jca', '( %s e. %s /\\ ( abs ` %s ) <_ %s )' % (z, D2, HZ, BB))
    PC_ = PTL(C1_, 't')
    alv = c([pt], 'ralrimiva', 'A. t e. ( U [,] V ) ( %s e. %s /\\ ( abs ` ( %s ` %s ) ) <_ %s )' % (PC_, D2, HD, PC_, BB))
    VZ = tsub(stmt('ef4vz'), {'G': HD, 'D': D2, 'C': C1_, 'B': BB})
    va, vcn = ante_of(VZ)
    vz = c([conj(w, A0, va, {'%s e. ( %s -cn-> CC )' % (HD, D2): ldc, '%s e. RR' % C1_: c1r, 'U e. RR': ur, 'V e. RR': vr, 'U <_ V': uv, '%s e. RR' % BB: bbr, top_and(va)[2]: alv}), w.inst('ef4vz')], 'syl', vcn)
    ylr = c([yr, lr], 'remulcld', '( Y x. %s ) e. RR' % L)
    yl0 = c([yr, lr, lin8(w, A0, [y100], '0 <_ Y', {'Y': yr}), lin8(w, A0, [l4], '0 <_ %s' % L, {L: lr})], 'mulge0d', '0 <_ ( Y x. %s )' % L)
    ylt = c([ylr, tp], 'rerpdivcld', '( ( Y x. %s ) / T ) e. RR' % L)
    ylt0 = c([ylr, tp, yl0], 'divge0d', '0 <_ ( ( Y x. %s ) / T )' % L)
    bb0 = lin8(w, A0, [ylt0], '0 <_ %s' % BB, {'( ( Y x. %s ) / T )' % L: ylt})
    vur = c([vr, ur], 'resubcld', '( V - U ) e. RR')
    g1 = c([vur, numst(w, A0, '1', 'RR'), bbr, bb0, vu1], 'lemul2ad', '( %s x. ( V - U ) ) <_ ( %s x. 1 )' % (BB, BB))
    g2 = c([g1, c([c([bbr], 'recnd', '%s e. CC' % BB)], 'mulridd', '( %s x. 1 ) = %s' % (BB, BB))], 'breqtrd', '( %s x. ( V - U ) ) <_ %s' % (BB, BB))
    a_ = G.split(' <_ ')[0]
    fin = le_tr(w, A0, vz, a_, '( %s x. ( V - U ) )' % BB, g2, BB)
    c0 = Ctx(w, A00)
    cb, _ = cbvral(w, '( U [,] V )', 't', 'y', 'T <_ ( abs ` t )')
    aly0 = c0([c0.g(pa[2]), c0.a1(cb, '( %s <-> A. y e. ( U [,] V ) T <_ ( abs ` y ) )' % pa[2])], 'mpbid', 'A. y e. ( U [,] V ) T <_ ( abs ` y )')
    w.qed([c0([c0.g(pa[0]), c0.g(pa[1]), aly0], '3jca', A0), fin], 'syl', S['ef6rx'])
    return run8(w)




GENS = {'ef6rm': gen_rm, 'ef6rx': gen_rx}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
