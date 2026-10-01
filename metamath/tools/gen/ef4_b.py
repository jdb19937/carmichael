"""Sortie EF4: the strip integrand on edges (ef4hed: Lean horiz_edge_le for LDI; ef4lfd, ef4rm, ef4rx: the right edge)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
import ef1lib as _ef1
from c8_o import numst
import congr as _cg
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out, unit_t, const_ibl


def LD0F(F):
    return '{ v e. %s | ( %s ` v ) =/= 0 }' % (HP0, F)


def LDB(F, z, Y='Y'):
    return '( ( ( ( CC _D %s ) ` %s ) / ( %s ` %s ) ) x. ( ( %s ^c %s ) / %s ) )' % (F, z, F, z, Y, z, z)


def ld0_mem(w, A, F, z, zhp, fnz):
    """( A -> z e. LD0(F) ) from z e. HP0 and F z =/= 0"""
    e = w.s([w.s([], 'fveq2', '( v = %s -> ( %s ` v ) = ( %s ` %s ) )' % (z, F, F, z))], 'neeq1d', '( v = %s -> ( ( %s ` v ) =/= 0 <-> ( %s ` %s ) =/= 0 ) )' % (z, F, F, z))
    return w.s([e, zhp, fnz], 'elrabd', '( %s -> %s e. %s )' % (A, z, LD0F(F)))


def hp0_mem(c, z, zc, rz, r0):
    """( A -> z e. HP0 ) from z e. CC, rz : ( Re ` z ) = x (or None), r0 : 0 < ( Re ` z ) (or 0 < x)"""
    w = c.w
    e = c([c.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (z, HP0, z, z))
    if rz is not None:
        r0 = c([r0, c([rz], 'eqcomd', '%s = ( Re ` %s )' % (body_of(w, rz).split(' = ', 1)[1], z))], 'breqtrd', '0 < ( Re ` %s )' % z)
    return c([c([zc, r0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (z, z)), e], 'mpbird', '%s e. %s' % (z, HP0))


def ldi_val(w, A, F, z, zin, Y='Y'):
    """( A -> ( LDI ` z ) = body ) for LDI of F"""
    st, val = _cg.mptval(w, A, 'u', LD0F(F), LDB(F, 'u', Y), z, zin, gen=w.g)
    return st


def ldi_abs(c, F, z, zc, zhp, fnz, yp, Y='Y'):
    """( A -> ( abs ` ( LDI ` z ) ) = ( ( abs ` Q ) x. ( ( Y ^c ( Re ` z ) ) / ( abs ` z ) ) ) ), Q = F'(z)/F(z); returns (step, qcc)"""
    w = c.w
    zin = ld0_mem(w, c.A, F, z, zhp, fnz)
    v = ldi_val(w, c.A, F, z, zin, Y)
    LDIF = LDI(F, Y)
    DZ = '( ( CC _D %s ) ` %s )' % (F, z)
    return v, zin


def gen_hed():
    w = W('ef4hed', 'Lean ` horiz_edge_le ` : on a horizontal segment at height ` H ` , ` T <_ abs H ` , where ` F =/= 0 ` and ` abs ( F \' / F ) <_ K ` , the strip integrand satisfies ` abs ( LDI lint ) <_ ( K / T ) ( Y ^ C / log Y ) ` ( ~ ef4hz ).')
    A00, G = ante_of(S['ef4hed'])
    PH0 = PTL('x', 'H')
    BODY0 = '( ( F ` %s ) =/= 0 /\\ ( abs ` %s ) <_ K )' % (PH0, LD(PH0))
    PY = PTL('y', 'H')
    BODYY = '( ( F ` %s ) =/= 0 /\\ ( abs ` %s ) <_ K )' % (PY, LD(PY))
    pa = top_and(A00)
    A0 = '( %s /\\ %s /\\ A. y e. ( S [,] C ) %s )' % (pa[0], pa[1], BODYY)
    c = Ctx(w, A0)
    hol = c.g(HOLF('F', HP0)); yr = c.g('Y e. RR'); y1 = c.g('1 < Y'); sr = c.g('S e. RR'); cr = c.g('C e. RR'); s0 = c.g('0 < S'); sc = c.g('S <_ C')
    tr = c.g('T e. RR'); t0 = c.g('0 < T'); hr = c.g('H e. RR'); th = c.g('T <_ ( abs ` H )'); kr = c.g('K e. RR')
    PH = PTL('x', 'H')
    BODY = '( ( F ` %s ) =/= 0 /\\ ( abs ` %s ) <_ K )' % (PH, LD(PH))
    alx = c.g('A. y e. ( S [,] C ) %s' % BODYY)
    yp = c([yr, lin8(w, A0, [y1], '0 < Y', {'Y': yr})], 'elrpd', 'Y e. RR+')
    yn1 = c([c.a1(w.s([], '1re', '1 e. RR'), '1 e. RR'), y1], 'gtned', 'Y =/= 1')
    tp = c([tr, t0], 'elrpd', 'T e. RR+')
    ldc = c([hol, yp, w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (LDI(), LD0F('F')))
    B = '( K / T )'
    br = c([kr, tp], 'rerpdivcld', '%s e. RR' % B)
    # pointwise
    A1 = '( %s /\\ x e. ( S [,] C ) )' % A0
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    xin = c1([], 'simpr', 'x e. ( S [,] C )')
    xr, sx, xc = icc_out(c1, 'x', 'S', 'C', xin, L1(sr), L1(cr))
    alx1 = L1(alx)
    # instantiate the quantifier at x itself
    pv, _ = ral_at(w, A1, L1(alx), 'y', 'x', BODYY, xin)
    fnz = c1([pv, w.inst('simpl')], 'syl', '( F ` %s ) =/= 0' % PH)
    qb = c1([pv, w.inst('simpr')], 'syl', '( abs ` %s ) <_ K' % LD(PH))
    zc = ptc(c1, 'x', 'H', xr, L1(hr))
    rz = c1([xr, L1(hr), w.inst('crre')], 'syl2anc', '( Re ` %s ) = x' % PH)
    iz = c1([xr, L1(hr), w.inst('crim')], 'syl2anc', '( Im ` %s ) = H' % PH)
    x0 = lin8(w, A1, [L1(s0), sx], '0 < x', {'S': L1(sr), 'x': xr})
    zhp = hp0_mem(c1, PH, zc, rz, x0)
    zin = ld0_mem(w, A1, 'F', PH, zhp, fnz)
    v = ldi_val(w, A1, 'F', PH, zin)
    Q = LD(PH)
    DZ = '( ( CC _D F ) ` %s )' % PH
    dom = c1([L1(hol), w.inst('simpr')], 'syl', '%s C_ dom ( CC _D F )' % HP0)
    dzc = c1([c1.a1(w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), '( CC _D F ) : dom ( CC _D F ) --> CC'), c1([dom, zhp], 'sseldd', '%s e. dom ( CC _D F )' % PH)], 'ffvelcdmd', '%s e. CC' % DZ)
    fc = c1([c1([c1([L1(hol), w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), zhp], 'ffvelcdmd', '( F ` %s ) e. CC' % PH)
    qc = c1([dzc, fc, fnz], 'divcld', '%s e. CC' % Q)
    YZ = '( Y ^c %s )' % PH
    yzc = c1([c1([L1(yp)], 'rpcnd', 'Y e. CC'), zc], 'cxpcld', '%s e. CC' % YZ)
    # abs z >_ abs Im z = abs H >_ T > 0
    aiz = c1([c1([iz], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` H )' % PH)], 'eqcomd', '( abs ` H ) = ( abs ` ( Im ` %s ) )' % PH)
    azr = c1([zc], 'abscld', '( abs ` %s ) e. RR' % PH)
    aimr = c1([c1([zc], 'imcld', '( Im ` %s ) e. RR' % PH)], 'recnd', '( Im ` %s ) e. CC' % PH)
    aim = c1([aimr], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % PH)
    ahr = c1([c1([L1(hr)], 'recnd', 'H e. CC')], 'abscld', '( abs ` H ) e. RR')
    le1 = c1([L1(th), aiz], 'breqtrd', 'T <_ ( abs ` ( Im ` %s ) )' % PH)
    le2 = c1([zc, w.inst('absimle')], 'syl', '( abs ` ( Im ` %s ) ) <_ ( abs ` %s )' % (PH, PH))
    tle = lin8(w, A1, [le1, le2], 'T <_ ( abs ` %s )' % PH, {'T': L1(tr), '( abs ` ( Im ` %s ) )' % PH: aim, '( abs ` %s )' % PH: azr})
    azp = c1([azr, lin8(w, A1, [L1(t0), tle], '0 < ( abs ` %s )' % PH, {'T': L1(tr), '( abs ` %s )' % PH: azr})], 'elrpd', '( abs ` %s ) e. RR+' % PH)
    zne = abs_ne0(c1, PH, zc, azp)
    # abs of the value
    YQ = '( %s / %s )' % (YZ, PH)
    a1 = c1([c1([v], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` ( %s x. %s ) )' % (LDI(), PH, Q, YQ)),
             c1([qc, c1([yzc, zc, zne], 'divcld', '%s e. CC' % YQ)], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (Q, YQ, Q, YQ))], 'eqtrd',
            '( abs ` ( %s ` %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (LDI(), PH, Q, YQ))
    YXX = '( Y ^c x )'
    ay = c1([c1([yzc, zc, zne], 'absdivd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (YQ, YZ, PH)),
             c1([c1([c1([L1(yp), zc, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( Y ^c ( Re ` %s ) )' % (YZ, PH)), c1([rz], 'oveq2d', '( Y ^c ( Re ` %s ) ) = %s' % (PH, YXX))], 'eqtrd',
                   '( abs ` %s ) = %s' % (YZ, YXX))], 'oveq1d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( %s / ( abs ` %s ) )' % (YZ, PH, YXX, PH))], 'eqtrd',
            '( abs ` %s ) = ( %s / ( abs ` %s ) )' % (YQ, YXX, PH))
    yxp = c1([L1(yp), xr], 'rpcxpcld', '%s e. RR+' % YXX)
    yxr = c1([yxp], 'rpred', '%s e. RR' % YXX)
    d2 = c1([L1(tp), azp, yxr, c1([yxp], 'rpge0d', '0 <_ %s' % YXX), tle], 'lediv2ad', '( %s / ( abs ` %s ) ) <_ ( %s / T )' % (YXX, PH, YXX))
    qr_ = c1([qc], 'abscld', '( abs ` %s ) e. RR' % Q)
    m = c1([qr_, L1(kr), c1([yxr, azp], 'rerpdivcld', '( %s / ( abs ` %s ) ) e. RR' % (YXX, PH)), c1([yxr, L1(tp)], 'rerpdivcld', '( %s / T ) e. RR' % YXX),
            c1([qc], 'absge0d', '0 <_ ( abs ` %s )' % Q), c1([c1([yxp, azp], 'rpdivcld', '( %s / ( abs ` %s ) ) e. RR+' % (YXX, PH))], 'rpge0d', '0 <_ ( %s / ( abs ` %s ) )' % (YXX, PH)),
            qb, d2], 'lemul12ad', '( ( abs ` %s ) x. ( %s / ( abs ` %s ) ) ) <_ ( K x. ( %s / T ) )' % (Q, YXX, PH, YXX))
    e3 = c1([c1([a1, c1([ay], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. ( %s / ( abs ` %s ) ) )' % (Q, YQ, Q, YXX, PH))], 'eqtrd',
                '( abs ` ( %s ` %s ) ) = ( ( abs ` %s ) x. ( %s / ( abs ` %s ) ) )' % (LDI(), PH, Q, YXX, PH)), m], 'eqbrtrd', '( abs ` ( %s ` %s ) ) <_ ( K x. ( %s / T ) )' % (LDI(), PH, YXX))
    e4 = c1([c1([L1(kr)], 'recnd', 'K e. CC'), c1([L1(tp)], 'rpcnd', 'T e. CC'), c1([yxr], 'recnd', '%s e. CC' % YXX), c1([L1(tp)], 'rpne0d', 'T =/= 0')], 'div32d',
            '( ( K / T ) x. %s ) = ( K x. ( %s / T ) )' % (YXX, YXX))
    e5 = c1([e3, c1([e4], 'eqcomd', '( K x. ( %s / T ) ) = ( ( K / T ) x. %s )' % (YXX, YXX))], 'breqtrd', '( abs ` ( %s ` %s ) ) <_ ( ( K / T ) x. %s )' % (LDI(), PH, YXX))
    pt = c1([zin, e5], 'jca', '( %s e. %s /\\ ( abs ` ( %s ` %s ) ) <_ ( ( K / T ) x. %s ) )' % (PH, LD0F('F'), LDI(), PH, YXX))
    alv = c([pt], 'ralrimiva', 'A. x e. ( S [,] C ) ( %s e. %s /\\ ( abs ` ( %s ` %s ) ) <_ ( ( K / T ) x. %s ) )' % (PH, LD0F('F'), LDI(), PH, YXX))
    HZ = tsub(stmt('ef4hz'), {'G': LDI(), 'D': LD0F('F'), 'P': 'S', 'Q': 'C', 'S': 'H', 'B': B})
    ha, hcn = ante_of(HZ)
    hz = c([conj(w, A0, ha, {'%s e. ( %s -cn-> CC )' % (LDI(), LD0F('F')): ldc, 'Y e. RR+': yp, 'Y =/= 1': yn1, 'S e. RR': sr, 'C e. RR': cr, 'S <_ C': sc, 'H e. RR': hr, '%s e. RR' % B: br,
                                   top_and(ha)[2]: alv}), w.inst('ef4hz')], 'syl', hcn)
    # ( K / T ) ( ( Y ^ C - Y ^ S ) / log Y ) <_ ( K / T ) ( Y ^ C / log Y )
    lg = c([yr, y1], 'rplogcld', '( log ` Y ) e. RR+')
    ycp = c([yp, cr], 'rpcxpcld', '( Y ^c C ) e. RR+'); ysp = c([yp, sr], 'rpcxpcld', '( Y ^c S ) e. RR+')
    ycr, ysr = c([ycp], 'rpred', '( Y ^c C ) e. RR'), c([ysp], 'rpred', '( Y ^c S ) e. RR')
    dl = lin8(w, A0, [c([ysp], 'rpge0d', '0 <_ ( Y ^c S )')], '( ( Y ^c C ) - ( Y ^c S ) ) <_ ( Y ^c C )', {'( Y ^c C )': ycr, '( Y ^c S )': ysr})
    dv = c([c([ycr, ysr], 'resubcld', '( ( Y ^c C ) - ( Y ^c S ) ) e. RR'), ycr, lg, dl], 'lediv1dd', '( ( ( Y ^c C ) - ( Y ^c S ) ) / ( log ` Y ) ) <_ ( ( Y ^c C ) / ( log ` Y ) )')
    # K >_ 0 from the bound at x = S
    sxin = icc_in(c, 'S', 'S', 'C', sr, sr, cr, c([sr], 'leidd', 'S <_ S'), sc)
    ps, _ = ral_at(w, A0, alx, 'y', 'S', BODYY, sxin)
    QS = LD(PTL('S', 'H'))
    zS = ptc(c, 'S', 'H', sr, hr)
    fS = c([ps, w.inst('simpl')], 'syl', '( F ` %s ) =/= 0' % PTL('S', 'H'))
    # abs QS >_ 0: QS is a complex number (quotient of values)
    sh = hp0_mem(c, PTL('S', 'H'), zS, c([sr, hr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = S' % PTL('S', 'H')), s0)
    domS = c([c([hol, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D F )' % HP0), sh], 'sseldd', '%s e. dom ( CC _D F )' % PTL('S', 'H'))
    dSc = c([c.a1(w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), '( CC _D F ) : dom ( CC _D F ) --> CC'), domS], 'ffvelcdmd', '( ( CC _D F ) ` %s ) e. CC' % PTL('S', 'H'))
    fSc = c([c([c([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), sh], 'ffvelcdmd', '( F ` %s ) e. CC' % PTL('S', 'H'))
    qS = c([dSc, fSc, fS], 'divcld', '%s e. CC' % QS)
    k0 = lin8(w, A0, [c([qS], 'absge0d', '0 <_ ( abs ` %s )' % QS), c([ps, w.inst('simpr')], 'syl', '( abs ` %s ) <_ K' % QS)], '0 <_ K', {'K': kr, '( abs ` %s )' % QS: c([qS], 'abscld', '( abs ` %s ) e. RR' % QS)})
    b0 = c([kr, tp, k0], 'divge0d', '0 <_ %s' % B)
    RR1 = '( ( ( Y ^c C ) - ( Y ^c S ) ) / ( log ` Y ) )'
    RR2 = '( ( Y ^c C ) / ( log ` Y ) )'
    fin = c([c([c([ycr, ysr], 'resubcld', '( ( Y ^c C ) - ( Y ^c S ) ) e. RR'), lg], 'rerpdivcld', '%s e. RR' % RR1), c([ycr, lg], 'rerpdivcld', '%s e. RR' % RR2), br, b0, dv], 'lemul2ad',
            '( %s x. %s ) <_ ( %s x. %s )' % (B, RR1, B, RR2))
    a_ = G.split(' <_ ')[0]
    fin2 = le_tr(w, A0, hz, a_, '( %s x. %s )' % (B, RR1), fin, '( %s x. %s )' % (B, RR2))
    cb, _ = cbvral(w, '( S [,] C )', 'x', 'y', BODY0)
    c0 = Ctx(w, A00)
    aly0 = c0([c0.g(pa[2]), c0.a1(cb, '( %s <-> A. y e. ( S [,] C ) %s )' % (pa[2], BODYY))], 'mpbid', 'A. y e. ( S [,] C ) %s' % BODYY)
    w.qed([c0([c0.g(pa[0]), c0.g(pa[1]), aly0], '3jca', A0), fin2], 'syl', S['ef4hed'])
    return run8(w)



import c9_h
patch(c9_h)
from c9_h import lf_hol
UT = 'UU'


def gen_lfd():
    w = W('ef4lfd', 'On ` Re S > 1 ` the logarithmic derivative of ` L ( s , chi ) ` ( ` chi ` nonprincipal) is minus the Dirichlet series of ` chi Lam ` (Lean ` LSeries_twist_vonMangoldt_eq ` in ` norm_logDeriv_LFunction_le ` ; ~ lchragr , ~ dvres , ~ lchrlogdv ).')
    A0 = ante_of(S['ef4lfd'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    sc = s([], 'simprl', 'S e. CC'); s1_ = s([], 'simprr', '1 < ( Re ` S )')
    rsr0 = s([sc], 'recld', '( Re ` S ) e. RR')
    ur = s([rsr0, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', 'UU e. RR')
    rs = s([s([s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), s([rsr0], 'recnd', '( Re ` S ) e. CC')], 'pncan3d', '( 1 + UU ) = ( Re ` S )')], 'eqcomd', '( Re ` S ) = ( 1 + UU )')
    up = s([ur, lin8(w, A0, [s1_, rs], '0 < UU', {'( Re ` S )': rsr0, 'UU': ur})], 'elrpd', 'UU e. RR+')
    nx = s([chi, w.inst('simpl')], 'syl', NX)
    T = '( 1 + ( UU / 2 ) )'
    tr = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), s([s([up, w.inst('rphalfcld')], 'syl', '( UU / 2 ) e. RR+')], 'rpred', '( UU / 2 ) e. RR')], 'readdcld', '%s e. RR' % T)
    lvu = {UT: ur}
    t1 = lin8(w, A0, [s([up], 'rpgt0d', '0 < UU')], '1 < %s' % T, lvu)
    Wd = "( `' Re \" ( %s (,) +oo ) )" % T
    rsr = s([sc], 'recld', '( Re ` S ) e. RR')
    sw = s([s([sc, lin8(w, A0, [rs, s([up], 'rpgt0d', '0 < UU')], '%s < ( Re ` S )' % T, {UT: ur, '( Re ` S )': rsr})], 'jca', '( S e. CC /\\ %s < ( Re ` S ) )' % T),
            s([tr, w.inst('elhp2')], 'syl', '( S e. %s <-> ( S e. CC /\\ %s < ( Re ` S ) ) )' % (Wd, T))], 'mpbird', 'S e. %s' % Wd)
    # W C_ HP0
    Az = '( %s /\\ z e. %s )' % (A0, Wd)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zz = sz([sz([], 'simpr', 'z e. %s' % Wd), sz([lift(w, tr, Az), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ %s < ( Re ` z ) ) )' % (Wd, T))], 'mpbid', '( z e. CC /\\ %s < ( Re ` z ) )' % T)
    zc = sz([zz, w.inst('simpl')], 'syl', 'z e. CC'); zt = sz([zz, w.inst('simpr')], 'syl', '%s < ( Re ` z )' % T)
    rzr = sz([zc], 'recld', '( Re ` z ) e. RR')
    z0 = lin8(w, Az, [zt, lift(w, t1, Az)], '0 < ( Re ` z )', {UT: lift(w, ur, Az), '( Re ` z )': rzr})
    z1 = lin8(w, Az, [zt, lift(w, t1, Az)], '1 < ( Re ` z )', {UT: lift(w, ur, Az), '( Re ` z )': rzr})
    zh = sz([sz([zc, z0], 'jca', '( z e. CC /\\ 0 < ( Re ` z ) )'), sz([sz([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % HP0)],
            'mpbird', 'z e. %s' % HP0)
    wss = s([w.s([zh], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (A0, Wd, HP0))], 'ssrdv', '%s C_ %s' % (Wd, HP0))
    DSX = lambda z: 'sum_ k e. NN ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u %s ) )' % z
    DSM = '( z e. %s |-> %s )' % (Wd, DSX('z'))
    LSW = '( s e. %s |-> %s )' % (Wd, LSs('s'))
    rm = s([wss, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (LFN, Wd, LSW))
    As = '( %s /\\ s e. %s )' % (A0, Wd)
    ss_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (As, f))
    szz = ss_([ss_([], 'simpr', 's e. %s' % Wd), ss_([lift(w, tr, As), w.inst('elhp2')], 'syl', '( s e. %s <-> ( s e. CC /\\ %s < ( Re ` s ) ) )' % (Wd, T))], 'mpbid', '( s e. CC /\\ %s < ( Re ` s ) )' % T)
    s1 = lin8(w, As, [ss_([szz, w.inst('simpr')], 'syl', '%s < ( Re ` s )' % T), lift(w, t1, As)], '1 < ( Re ` s )', {UT: lift(w, ur, As), '( Re ` s )': ss_([ss_([szz, w.inst('simpl')], 'syl', 's e. CC')], 'recld', '( Re ` s ) e. RR')})
    ag = ss_([ss_([lift(w, chi, As), ss_([ss_([szz, w.inst('simpl')], 'syl', 's e. CC'), s1], 'jca', '( s e. CC /\\ 1 < ( Re ` s ) )')], 'jca', '( %s /\\ ( s e. CC /\\ 1 < ( Re ` s ) ) )' % CHI), w.inst('lchragr')],
             'syl', '%s = %s' % (LSs('s'), DSX('s')))
    me = s([ag], 'mpteq2dva', '%s = ( s e. %s |-> %s )' % (LSW, Wd, DSX('s')))
    cb = s([w.s([w.s([w.s([w.s([w.s([], 'negeq', '( s = z -> -u s = -u z )')], 'oveq2d', '( s = z -> ( k ^c -u s ) = ( k ^c -u z ) )')], 'oveq2d',
                                  '( s = z -> ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u s ) ) = ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u z ) ) )')], 'sumeq2sdv',
                           '( s = z -> %s = %s )' % (DSX('s'), DSX('z')))], 'cbvmptv', '( s e. %s |-> %s ) = %s' % (Wd, DSX('s'), DSM))], 'a1i', '( s e. %s |-> %s ) = %s' % (Wd, DSX('s'), DSM))
    resq = s([s([rm, me], 'eqtrd', '( %s |` %s ) = ( s e. %s |-> %s )' % (LFN, Wd, Wd, DSX('s'))), cb], 'eqtrd', '( %s |` %s ) = %s' % (LFN, Wd, DSM))
    hol = lf_hol(w, A0, chi)
    lff = s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0))
    hpc = s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncfrss')], 'syl', '%s C_ CC' % HP0)
    wcc = s([wss, hpc], 'sstrd', '%s C_ CC' % Wd)
    K = '( TopOpen ` CCfld )'
    k_ = w.s([], 'eqid', '%s = %s' % (K, K))
    tk = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (K, K))], 'eqcomi', '%s = ( %s |`t CC )' % (K, K))
    dv = s([s([s([s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), lff], 'jca', '( CC C_ CC /\\ %s : %s --> CC )' % (LFN, HP0)), s([hpc, wcc], 'jca', '( %s C_ CC /\\ %s C_ CC )' % (HP0, Wd))], 'jca',
               '( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) )' % (LFN, HP0, HP0, Wd)), w.s([k_, tk], 'dvres', '( ( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (LFN, HP0, HP0, Wd, LFN, Wd, LFN, K, Wd))],
           'syl', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) )' % (LFN, Wd, LFN, K, Wd))
    iw = s([s([w.s([w.s([], 'eqid', '%s = %s' % (K, K))], 'cnfldtop', '%s e. Top' % K)], 'a1i', '%s e. Top' % K), s([w.s([], 'hpopn', '%s e. %s' % (Wd, K))], 'a1i', '%s e. %s' % (Wd, K)), w.inst('isopn3i')],
           'syl2anc', '( ( int ` %s ) ` %s ) = %s' % (K, Wd, Wd))
    dv2 = s([dv, s([iw], 'reseq2d', '( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) = ( ( CC _D %s ) |` %s )' % (LFN, K, Wd, LFN, Wd))], 'eqtrd', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s )' % (LFN, Wd, LFN, Wd))
    dv3 = s([s([s([resq], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D %s )' % (LFN, Wd, DSM))], 'eqcomd', '( CC _D %s ) = ( CC _D ( %s |` %s ) )' % (DSM, LFN, Wd)), dv2], 'eqtrd',
            '( CC _D %s ) = ( ( CC _D %s ) |` %s )' % (DSM, LFN, Wd))
    dS = s([s([dv3], 'fveq1d', '( ( CC _D %s ) ` S ) = ( ( ( CC _D %s ) |` %s ) ` S )' % (DSM, LFN, Wd)), s([sw, w.inst('fvres')], 'syl', '( ( ( CC _D %s ) |` %s ) ` S ) = ( ( CC _D %s ) ` S )' % (LFN, Wd, LFN))],
           'eqtrd', '( ( CC _D %s ) ` S ) = ( ( CC _D %s ) ` S )' % (DSM, LFN))
    # value of L at S
    shp = s([wss, sw], 'sseldd', 'S e. %s' % HP0)
    lv, _ = _cg.mptval(w, A0, 's', HP0, LSs('s'), 'S', shp, exs=s([w.s([], 'sumex', '%s e. _V' % LSs('S'))], 'a1i', '%s e. _V' % LSs('S')), gen=w.g)
    s1S = lin8(w, A0, [rs, s([up], 'rpgt0d', '0 < UU')], '1 < ( Re ` S )', {UT: ur, '( Re ` S )': rsr})
    agS = s([s([chi, s([sc, s1S], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', '( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % CHI), w.inst('lchragr')], 'syl', '%s = %s' % (LSs('S'), DSX('S')))
    lS = s([lv, agS], 'eqtrd', '( %s ` S ) = %s' % (LFN, DSX('S')))
    LD = tsub(stmt('lchrlogdv'), {'T': T, 'Z': 'S'})
    lda, ldc = ante_of(LD)
    ld = s([s([nx, s([s([tr, t1], 'jca', '( %s e. RR /\\ 1 < %s )' % (T, T)), sw], 'jca', top_and(lda)[1])], 'jca', lda), w.inst('lchrlogdv')], 'syl', ldc)
    VS = ldc.rsplit(' = -u ', 1)[1]
    lSr = s([lS], 'eqcomd', '%s = ( %s ` S )' % (DSX('S'), LFN))
    rat = s([s([dS, lSr], 'oveq12d', '( ( ( CC _D %s ) ` S ) / %s ) = ( ( ( CC _D %s ) ` S ) / ( %s ` S ) )' % (DSM, DSX('S'), LFN, LFN))], 'eqcomd',
            '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( ( ( CC _D %s ) ` S ) / %s )' % (LFN, LFN, DSM, DSX('S')))
    rat2 = s([rat, ld], 'eqtrd', '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = -u %s' % (LFN, LFN, VS))
    w.qed([rat2], 'idi', S['ef4lfd'])
    w.lines = [l.replace(' UU ', ' ( ( Re ` S ) - 1 ) ') for l in w.lines]
    return run8(w)



def lfn_pt(w, A1, cc, C, M, cr, mr, c1_, nz):
    """under A1: the point z = C + i M (M real) with 1 < C: z e. CC, Re z = C, z e. HP0, LFN z =/= 0, z e. LD0, 0 < Re z"""
    c = Ctx(w, A1)
    z = PTL(C, M)
    zc = ptc(c, C, M, cr, mr)
    rz = c([cr, mr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (z, C))
    r1 = c([c1_, c([rz], 'eqcomd', '%s = ( Re ` %s )' % (C, z))], 'breqtrd', '1 < ( Re ` %s )' % z)
    rzr = c([zc], 'recld', '( Re ` %s ) e. RR' % z)
    r0 = lin8(w, A1, [r1], '0 < ( Re ` %s )' % z, {'( Re ` %s )' % z: rzr})
    zhp = hp0_mem(c, z, zc, None, r0)
    nzb, _ = ral_at(w, A1, nz, 'w', z, '( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN, zhp)
    fnz = c([r1, nzb], 'mpd', '( %s ` %s ) =/= 0' % (LFN, z))
    zin = ld0_mem(w, A1, LFN, z, zhp, fnz)
    return dict(z=z, zc=zc, rz=rz, r1=r1, r0=r0, zhp=zhp, fnz=fnz, zin=zin)


def gen_rm():
    w = W('ef4rm', 'The middle of the right edge (Lean ` integral_right_edge ` in ` contour_ne_one ` , ` hJmid ` ): on ` Re = C > 1 ` the strip integrand of ` L ` is ` - ( chi Lam series ) Y ^ z / z ` ( ~ ef4lfd ), so its line integral from ` C - i T ` to ` C + i T ` is minus the Perron sum ( ~ ef1redge ).')
    A0, G = ante_of(S['ef4rm'])
    c = Ctx(w, A0)
    chi = c.g(CHI); yp = c.g('Y e. RR+'); cr = c.g('C e. RR'); c1_ = c.g('1 < C'); tr = c.g('T e. RR')
    nx = c([chi, w.inst('simpl')], 'syl', NX)
    dd = c([chi, w.inst('ef2ddl')], 'syl', DD(LFN, 'N'))
    hol, _, _, _, nz = dd_parts(w, A0, dd, LFN, 'N')
    Aa, Bb = LO('C', 'T'), HI('C', 'T')
    ntr = c([tr], 'renegcld', '-u T e. RR')
    ac, bc = ptc(c, 'C', '-u T', cr, ntr), ptc(c, 'C', 'T', cr, tr)
    D0 = LD0F(LFN)
    PT_ = '( %s + ( t x. ( %s - %s ) ) )' % (Aa, Bb, Aa)
    M = '( -u T + ( t x. ( T - -u T ) ) )'

    def pt_facts(A1):
        c1 = Ctx(w, A1)
        L1 = lambda st: lift(w, st, A1)
        tr1 = c1([c1([], 'simpr', 't e. ( 0 [,] 1 )'), w.inst('elunitrn')], 'syl', 't e. RR')
        cl = Closure(w, A1, {'C': ('RR', L1(cr)), 'T': ('RR', L1(tr)), 't': ('RR', tr1), '_i': ('CC', ic_(c1))})
        for k in ('C', 'T', 't', '_i'):
            cl.atom(k)
        e1 = ringeq(w, A1, PT_, PTL('C', M), cl)
        mr = cl.mem(M, 'RR')
        d = lfn_pt(w, A1, None, 'C', M, L1(cr), mr, L1(c1_), L1(nz))
        d['e1'] = e1
        d['cl'] = cl
        return d
    A1 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A0
    d1 = pt_facts(A1)
    c1 = Ctx(w, A1)
    mem1 = c1([d1['e1'], d1['zin']], 'eqeltrd', '%s e. %s' % (PT_, D0))
    seg = seg_sub(w, A0, Aa, Bb, ac, bc, D0, lambda A: mem1)
    ldc = c([hol, yp, w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (LDL, D0))
    DF = '( %s - %s )' % (Bb, Aa)
    LDINT = '( ( %s ` %s ) x. %s )' % (LDL, PT_, DF)
    RHF = _ef1.RHF
    RHINT = '( ( %s ` %s ) x. %s )' % (RHF, PT_, DF)
    ibl = c([c([c([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (Aa, Bb)), c([ldc, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (LDL, D0, Aa, Bb, D0))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (Aa, Bb, LDL, D0, Aa, Bb, D0)), w.inst('lintibl')], 'syl',
            '( t e. ( 0 (,) 1 ) |-> %s ) e. L^1' % LDINT)
    # pointwise: LDINT = -u RHINT and LDINT e. CC, on the closed interval then the open one
    z = d1['z']
    lv = ldi_val(w, A1, LFN, PT_, mem1)
    DL = _ef1.DLV(PT_)
    LF = tsub(stmt('ef4lfd'), {'S': PT_})
    lfa, lfc = ante_of(LF)
    ptc_ = c1([d1['e1'], d1['zc']], 'eqeltrd', '%s e. CC' % PT_)
    r1p = c1([d1['r1'], c1([c1([d1['e1']], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (PT_, z))], 'eqcomd', '( Re ` %s ) = ( Re ` %s )' % (z, PT_))], 'breqtrd', '1 < ( Re ` %s )' % PT_)
    lf = c1([c1([lift(w, chi, A1), c1([ptc_, r1p], 'jca', top_and(lfa)[1])], 'jca', lfa), w.inst('ef4lfd')], 'syl', lfc)
    YQ = '( ( Y ^c %s ) / %s )' % (PT_, PT_)
    Q = LD(PT_, LFN)
    lv2 = c1([lv, c1([lf], 'oveq1d', '( %s x. %s ) = ( -u %s x. %s )' % (Q, YQ, DL, YQ))], 'eqtrd', '( %s ` %s ) = ( -u %s x. %s )' % (LDL, PT_, DL, YQ))
    r0p = c1([d1['r0'], c1([c1([d1['e1']], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (PT_, z))], 'eqcomd', '( Re ` %s ) = ( Re ` %s )' % (z, PT_))], 'breqtrd', '0 < ( Re ` %s )' % PT_)
    pne = ne0_re(c1, PT_, ptc_, r0p)
    pd = c1([ptc_, pne], 'eldifsnd', '%s e. ( CC \\ { 0 } )' % PT_)
    rv, _ = _cg.mptval(w, A1, 'z', '( CC \\ { 0 } )', '( %s x. ( ( Y ^c z ) / z ) )' % _ef1.DLV('z'), PT_, pd, gen=w.g)
    # DL e. CC: the value LFN'/LFN is a complex number and equals -u DL
    hol1 = lift(w, hol, A1)
    zhp = c1([d1['e1'], d1['zhp']], 'eqeltrd', '%s e. %s' % (PT_, HP0))
    fz = c1([d1['e1']], 'fveq2d', '( %s ` %s ) = ( %s ` %s )' % (LFN, PT_, LFN, z))
    fnz = c1([d1['fnz'], c1([fz], 'neeq1d', '( ( %s ` %s ) =/= 0 <-> ( %s ` %s ) =/= 0 )' % (LFN, PT_, LFN, z))], 'mpbird', '( %s ` %s ) =/= 0' % (LFN, PT_))
    dom = c1([hol1, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D %s )' % (HP0, LFN))
    dzc = c1([c1.a1(w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (LFN, LFN)), '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (LFN, LFN)), c1([dom, zhp], 'sseldd', '%s e. dom ( CC _D %s )' % (PT_, LFN))], 'ffvelcdmd', '( ( CC _D %s ) ` %s ) e. CC' % (LFN, PT_))
    fc = c1([c1([c1([hol1, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), zhp], 'ffvelcdmd', '( %s ` %s ) e. CC' % (LFN, PT_))
    qc = c1([dzc, fc, fnz], 'divcld', '%s e. CC' % Q)
    ndl = c1([lf, qc], 'eqeltrrd', '-u %s e. CC' % DL)
    dlc = dlv_cc(w, A1, lift(w, nx, A1), PT_, ptc_, r1p)
    yqc = c1([c1([c1([lift(w, yp, A1)], 'rpcnd', 'Y e. CC'), ptc_], 'cxpcld', '( Y ^c %s ) e. CC' % PT_), ptc_, pne], 'divcld', '%s e. CC' % YQ)
    dfc = c1([lift(w, bc, A1), lift(w, ac, A1)], 'subcld', '%s e. CC' % DF)
    RHV = '( %s x. %s )' % (DL, YQ)
    li = c1([lv2], 'oveq1d', '%s = ( ( -u %s x. %s ) x. %s )' % (LDINT, DL, YQ, DF))
    m1 = c1([dlc, yqc], 'mulneg1d', '( -u %s x. %s ) = -u %s' % (DL, YQ, RHV))
    m2 = c1([c1([m1], 'oveq1d', '( ( -u %s x. %s ) x. %s ) = ( -u %s x. %s )' % (DL, YQ, DF, RHV, DF)), c1([c1([dlc, yqc], 'mulcld', '%s e. CC' % RHV), dfc], 'mulneg1d', '( -u %s x. %s ) = -u ( %s x. %s )' % (RHV, DF, RHV, DF))], 'eqtrd',
            '( ( -u %s x. %s ) x. %s ) = -u ( %s x. %s )' % (DL, YQ, DF, RHV, DF))
    ri = c1([rv], 'oveq1d', '%s = ( %s x. %s )' % (RHINT, RHV, DF))
    ri2 = c1([ri], 'negeqd', '-u %s = -u ( %s x. %s )' % (RHINT, RHV, DF))
    pwc = c1([c1([li, m2], 'eqtrd', '%s = -u ( %s x. %s )' % (LDINT, RHV, DF)), ri2], 'eqtr4d', '%s = -u %s' % (LDINT, RHINT))
    ldic = c1([c1([lift(w, ldc, A1), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LDL, D0)), mem1], 'ffvelcdmd', '( %s ` %s ) e. CC' % (LDL, PT_))
    ldintc = c1([ldic, dfc], 'mulcld', '%s e. CC' % LDINT)
    nrh = c1([pwc, ldintc], 'eqeltrrd', '-u %s e. CC' % RHINT)
    rhc = c1([ri, c1([c1([dlc, yqc], 'mulcld', '%s e. CC' % RHV), dfc], 'mulcld', '( %s x. %s ) e. CC' % (RHV, DF))], 'eqeltrd', '%s e. CC' % RHINT)
    rneg = c1([c1([c1([pwc], 'negeqd', '-u %s = -u -u %s' % (LDINT, RHINT)), c1([rhc], 'negnegd', '-u -u %s = %s' % (RHINT, RHINT))], 'eqtrd', '-u %s = %s' % (LDINT, RHINT))], 'eqcomd', '%s = -u %s' % (RHINT, LDINT))
    Ao = '( %s /\\ t e. ( 0 (,) 1 ) )' % A0
    rneg_o = open_to_closed(w, A0, rneg)
    ldc_o = open_to_closed(w, A0, ldintc)
    X = '( 0 (,) 1 )'
    ieq = c([rneg_o], 'itgeq2dv', 'S. %s %s _d t = S. %s -u %s _d t' % (X, RHINT, X, LDINT))
    ing = c([ldc_o, ibl], 'itgneg', '-u S. %s %s _d t = S. %s -u %s _d t' % (X, LDINT, X, LDINT))
    RHL = '( %s lint <. %s , %s >. )' % (RHF, Aa, Bb)
    LDLL = '( %s lint <. %s , %s >. )' % (LDL, Aa, Bb)
    lvr = c([c.a1(w.s([], 'mptex', '%s e. _V' % RHF), '%s e. _V' % RHF), ac, bc, w.inst('lintval')], 'syl3anc',
            '%s = S. %s %s _d t' % (RHL, X, RHINT))
    lvl = c([c([ldc], 'elexd', '%s e. _V' % LDL), ac, bc, w.inst('lintval')], 'syl3anc', '%s = S. %s %s _d t' % (LDLL, X, LDINT))
    e2 = c([c([lvr, ieq], 'eqtrd', '%s = S. %s -u %s _d t' % (RHL, X, LDINT)), c([c([ing], 'eqcomd', 'S. %s -u %s _d t = -u S. %s %s _d t' % (X, LDINT, X, LDINT)),
                                                                                      c([lvl], 'negeqd', '-u %s = -u S. %s %s _d t' % (LDLL, X, LDINT))], 'eqtr4d', 'S. %s -u %s _d t = -u %s' % (X, LDINT, LDLL))], 'eqtrd', '%s = -u %s' % (RHL, LDLL))
    RE = tsub(stmt('ef1redge'), {})
    rea, rec_ = ante_of(RE)
    red = c([c([nx, c([c([yp, cr, c1_], '3jca', '( Y e. RR+ /\\ C e. RR /\\ 1 < C )'), tr], 'jca', top_and(rea)[1])], 'jca', rea), w.inst('ef1redge')], 'syl', rec_)
    PSEQ = top_and(rec_)[1]
    ps = c([red, w.inst('simpr')], 'syl', PSEQ)
    PSC_ = PSC('C')
    e3 = c([ps, e2], 'eqtrd', '%s = -u %s' % (PSC_, LDLL))
    llc = c([c([c([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (Aa, Bb)), c([ldc, seg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (LDL, D0, Aa, Bb, D0))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (Aa, Bb, LDL, D0, Aa, Bb, D0)), w.inst('lintcl')], 'syl', '%s e. CC' % LDLL)
    e4 = c([c([e3], 'negeqd', '-u %s = -u -u %s' % (PSC_, LDLL)), c([llc], 'negnegd', '-u -u %s = %s' % (LDLL, LDLL))], 'eqtrd', '-u %s = %s' % (PSC_, LDLL))
    w.qed([e4], 'eqcomd', S['ef4rm'])
    return run8(w)



def gen_rx():
    w = W('ef4rx', 'Lean ` right_extra_le ` (nonprincipal ` chi ` ): on a piece of ` Re = c ` of length at most 1 where ` T <_ abs t ` , the strip integrand of ` L ` has line integral at most ` 8 Y log Y / T ` ( ~ lchrldre gives ` abs L \' / L <_ ( 5 / 4 ) log Y + 5 ` there; Lean ` 18 Y log ^ 2 Y / T ` ).')
    A00, G = ante_of(S['ef4rx'])
    pa = top_and(A00)
    A0 = '( %s /\\ %s /\\ A. y e. ( U [,] V ) T <_ ( abs ` y ) )' % (pa[0], pa[1])
    c = Ctx(w, A0)
    chi = c.g(CHI); yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t0 = c.g('0 < T')
    ur = c.g('U e. RR'); vr = c.g('V e. RR'); uv = c.g('U <_ V'); vu1 = c.g('( V - U ) <_ 1')
    aly = c.g('A. y e. ( U [,] V ) T <_ ( abs ` y )')
    nx = c([chi, w.inst('simpl')], 'syl', NX)
    dd = c([chi, w.inst('ef2ddl')], 'syl', DD(LFN, 'N'))
    hol, _, _, _, nz = dd_parts(w, A0, dd, LFN, 'N')
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
    ldc = c([hol, yp, w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (LDL, LD0F(LFN)))
    BB = '( 8 x. ( ( Y x. %s ) / T ) )' % L
    tp = c([tr, t0], 'elrpd', 'T e. RR+')
    bbr = c([numst(w, A0, '8', 'RR'), c([c([yr, lr], 'remulcld', '( Y x. %s ) e. RR' % L), tp], 'rerpdivcld', '( ( Y x. %s ) / T ) e. RR' % L)], 'remulcld', '%s e. RR' % BB)
    # pointwise on t e. [U, V]
    A1 = '( %s /\\ t e. ( U [,] V ) )' % A0
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    tin = c1([], 'simpr', 't e. ( U [,] V )')
    tr1, _, _ = icc_out(c1, 't', 'U', 'V', tin, L1(ur), L1(vr))
    d = lfn_pt(w, A1, None, C1_, 't', L1(c1r), tr1, L1(c1g), L1(nz))
    z = d['z']
    zhp, zc, fnz, zin = d['zhp'], d['zc'], d['fnz'], d['zin']
    v = ldi_val(w, A1, LFN, z, zin)
    Q = LD(z, LFN)
    hol1 = L1(hol)
    dom = c1([hol1, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D %s )' % (HP0, LFN))
    dzc = c1([c1.a1(w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (LFN, LFN)), '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (LFN, LFN)), c1([dom, zhp], 'sseldd', '%s e. dom ( CC _D %s )' % (z, LFN))], 'ffvelcdmd', '( ( CC _D %s ) ` %s ) e. CC' % (LFN, z))
    fc = c1([c1([c1([hol1, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), zhp], 'ffvelcdmd', '( %s ` %s ) e. CC' % (LFN, z))
    qc = c1([dzc, fc, fnz], 'divcld', '%s e. CC' % Q)
    # abs Q <_ ( 5 / 2 ) log Y
    LR = tsub(stmt('lchrldre'), {'U': UP, 'S': z})
    lra, lrc = ante_of(LR)
    lq = c1([c1([L1(chi), c1([c1([L1(upp), L1(up1)], 'jca', '( %s e. RR+ /\\ %s <_ 1 )' % (UP, UP)), c1([zc, d['rz']], 'jca', '( %s e. CC /\\ ( Re ` %s ) = %s )' % (z, z, C1_))], 'jca', top_and(lra)[1])], 'jca', lra), w.inst('lchrldre')], 'syl', lrc)
    F54 = '( 5 / 4 )'
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
    a1 = c1([c1([v], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` ( %s x. %s ) )' % (LDL, z, Q, YQ)),
             c1([qc, yqc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (Q, YQ, Q, YQ))], 'eqtrd',
            '( abs ` ( %s ` %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (LDL, z, Q, YQ))
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
    f1 = c1([c1([a1, m], 'eqbrtrd', '( abs ` ( %s ` %s ) ) <_ ( %s x. ( 3 x. %s ) )' % (LDL, z, A52, YT_)), e1], 'breqtrd', '( abs ` ( %s ` %s ) ) <_ ( ( ; 1 5 / 2 ) x. %s )' % (LDL, z, W1))
    f2 = le_tr(w, A1, f1, '( abs ` ( %s ` %s ) )' % (LDL, z), '( ( ; 1 5 / 2 ) x. %s )' % W1, e3, BB)
    pt = c1([zin, f2], 'jca', '( %s e. %s /\\ ( abs ` ( %s ` %s ) ) <_ %s )' % (z, LD0F(LFN), LDL, z, BB))
    PC_ = PTL(C1_, 't')
    alv = c([pt], 'ralrimiva', 'A. t e. ( U [,] V ) ( %s e. %s /\\ ( abs ` ( %s ` %s ) ) <_ %s )' % (PC_, LD0F(LFN), LDL, PC_, BB))
    VZ = tsub(stmt('ef4vz'), {'G': LDL, 'D': LD0F(LFN), 'C': C1_, 'B': BB})
    va, vcn = ante_of(VZ)
    vz = c([conj(w, A0, va, {'%s e. ( %s -cn-> CC )' % (LDL, LD0F(LFN)): ldc, '%s e. RR' % C1_: c1r, 'U e. RR': ur, 'V e. RR': vr, 'U <_ V': uv, '%s e. RR' % BB: bbr, top_and(va)[2]: alv}), w.inst('ef4vz')], 'syl', vcn)
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
    w.qed([c0([c0.g(pa[0]), c0.g(pa[1]), aly0], '3jca', A0), fin], 'syl', S['ef4rx'])
    return run8(w)


def dlv_cc(w, A, nx, Sp, sc, s1):
    """( A -> DLV(Sp) e. CC ) from NX, Sp e. CC and 1 < Re Sp (lchvmcvg, isumcl); A must not contain k, n"""
    c = Ctx(w, A)
    Ak = '( %s /\\ k e. NN )' % A
    sk = Ctx(w, Ak)
    kn = sk([], 'simpr', 'k e. NN')
    CHK = '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) )'
    xk = sk([sk([lift(w, nx, Ak), kn], 'jca', '( %s /\\ k e. NN )' % NX), w.inst('lchrcl')], 'syl', '%s e. CC' % CHK)
    lk = sk([sk([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    kz = sk([sk([kn], 'nncnd', 'k e. CC'), sk([lift(w, sc, Ak)], 'negcld', '-u %s e. CC' % Sp)], 'cxpcld', '( k ^c -u %s ) e. CC' % Sp)
    VK = '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u %s ) )' % (CHK, Sp)
    vk = sk([sk([xk, lk], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHK), kz], 'mulcld', '%s e. CC' % VK)
    VN = '( ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` n ) ) x. ( Lam ` n ) ) x. ( n ^c -u %s ) )' % Sp
    fv, _ = _cg.mptval(w, Ak, 'n', 'NN', VN, 'k', kn, exs=sk([vk], 'elexd', '%s e. _V' % VK), gen=w.g)
    cvg = c([c([nx, c([sc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (Sp, Sp))], 'jca', '( %s /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (NX, Sp, Sp)), w.inst('lchvmcvg')], 'syl',
            'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % VN)
    return c([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), c([], '1zzd', '1 e. ZZ'), fv, vk, cvg], 'isumcl', '%s e. CC' % _ef1.DLV(Sp))


def ral_self(w, A, al, var, X, body, xin):
    """( A -> body ) from al : ( A -> A. var e. X body ) and xin : ( A -> var e. X ), var free in A"""
    return w.s([al, w.inst('rsp')], 'syl', '( %s -> ( %s e. %s -> %s ) )' % (A, var, X, body)) and \
        w.s([xin, w.s([al, w.inst('rsp')], 'syl', '( %s -> ( %s e. %s -> %s ) )' % (A, var, X, body))], 'mpd', '( %s -> %s )' % (A, body))


def abs_ne0(c, z, zc, azp):
    """( A -> z =/= 0 ) from abs z e. RR+"""
    w = c.w
    e = c([zc, w.inst('abs00')], 'syl', '( ( abs ` %s ) = 0 <-> %s = 0 )' % (z, z))
    return c([c([azp], 'rpne0d', '( abs ` %s ) =/= 0' % z), c([e], 'necon3bid', '( ( abs ` %s ) =/= 0 <-> %s =/= 0 )' % (z, z))], 'mpbid', '%s =/= 0' % z)


GENS = {'ef4hed': gen_hed, 'ef4lfd': gen_lfd, 'ef4rm': gen_rm, 'ef4rx': gen_rx}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
