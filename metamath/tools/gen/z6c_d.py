"""Sortie Z6c, section 7: blueprint Lemma 4.1, DetectionEstimate, Proposition 4.4.
z6g3gr   on Re w = 3 the anchor integrand G3 is GR (DSER)
z6detr   one modulus: ( 1 / R ) sum_n STERM = ( 1 / 2 pi i ) ( 1 / R ) VL(GR,CL) + ( 1 / R ) RES5
z6epsum  the residues summed are EPole
z6detid  FDV + e ^ ( -1 / X ) P ( 1 ) = ECTR + EPC            (Lean detection_identity_all)
z6detall | FDV + e ^ ( -1 / X ) P ( 1 ) - EPC | <_ P ( 1 ) / 8 (Lean detection_estimate_all)
z6dlbz   the detector lower bound                            (Lean detector_lower_bound_of_zero_all)
Run: MM_DB=sorties/z6c.mm LIN_FAST=1 python3 tools/gen/z6c_d.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6clib import *
from tm import sub
from cl import split_imp, lift, formula_of
from z6a_e3 import conjs, build, unpack, c_
from z6a_mlib import mpval, toqed
from z6c_s import dfx, rsetnn, stcc, cbvsum_nm, cl1, p1dcc
import z6b_r
import lin
from lin import linarith
import num

only = sys.argv[1:]
NNUZ = 'NN = ( ZZ>= ` 1 )'
X = XPD
SW = '( S + %s )' % W3
HP2 = HPT('2')
PHN = '( ( phi ` N ) / N )'
GX = '( ( _G ` ( 1 - S ) ) x. ( %s ^c ( 1 - S ) ) )' % X
PRH = PRIN('N', 'h')


def want(lab):
    return not only or lab in only


def mbody(mp, x, dom):
    pre = '( %s e. %s |-> ' % (x, dom)
    assert mp.startswith(pre) and mp.endswith(' )'), mp[:80]
    return mp[len(pre):-2]


def nere(w, ctx, V, Z, reV, rv, reZ, rz, hyps, leaves):
    """( ctx -> V =/= Z ) from reV: ( ctx -> ( Re ` V ) = rv ), reZ: ( ctx -> ( Re ` Z ) = rz ), rz < rv by linarith"""
    c2 = '( %s /\\ %s = %s )' % (ctx, V, Z); t = mkst(w, c2)
    e = t([t([], 'simpr', '%s = %s' % (V, Z))], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (V, Z))
    e2 = t([t([t([lift(w, reV, c2)], 'eqcomd', '%s = ( Re ` %s )' % (rv, V)), e], 'eqtrd', '%s = ( Re ` %s )' % (rv, Z)), lift(w, reZ, c2)], 'eqtrd', '%s = %s' % (rv, rz))
    L = {k: lift(w, v, c2) for k, v in leaves.items()}
    lt = linarith(w, c2, [lift(w, h, c2) for h in hyps], '%s < %s' % (rz, rv), leaves=L)
    ne = t([t([t([lt], 'ltned', '%s =/= %s' % (rz, rv))], 'necomd', '%s =/= %s' % (rv, rz))], 'neneqd', '-. %s = %s' % (rv, rz))
    nz = w.s([e2, ne], 'pm2.65da', '( %s -> -. %s = %s )' % (ctx, V, Z))
    return w.s([nz], 'neqned', '( %s -> %s =/= %s )' % (ctx, V, Z))


def tpi_facts(w, a):
    st = mkst(w, a)
    ic = cl1(w, a, 'ax-icn', '_i e. CC'); pc = cl1(w, a, 'picn', '_pi e. CC')
    tc = st([cl1(w, a, '2cn', '2 e. CC'), st([ic, pc], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    tn = st([cl1(w, a, '2cn', '2 e. CC'), st([ic, pc], 'mulcld', '( _i x. _pi ) e. CC'), cl1(w, a, '2ne0', '2 =/= 0'),
             st([ic, pc, cl1(w, a, 'ine0', '_i =/= 0'), cl1(w, a, 'pine0', '_pi =/= 0')], 'mulne0d', '( _i x. _pi ) =/= 0')], 'mulne0d', '%s =/= 0' % TPI)
    return tc, tn


# ================================================================== z6g3gr
def z6g3gr():
    w = W('z6g3gr', 'On the line ` Re w = 3 ` the anchor integrand (the Dirichlet series of ` C ` ) equals the contour integrand ` GR ` '
          '( ` E ( s ) / ( s - 1 ) ` is the series there by ` DSER ` ; Lean ` ectrInt_line_eq_Ghat ` at ` c = 3 ` ).')
    a = ante('z6g3gr'); f = unpack(w, a); st = mkst(w, a)
    sc = f['S e. CC']; ur = f['U e. RR']; s0 = f['0 <_ ( Re ` S )']
    w3c = st([cl1(w, a, '3cn', '3 e. CC'), st([cl1(w, a, 'ax-icn', '_i e. CC'), st([ur], 'recnd', 'U e. CC')], 'mulcld', '( _i x. U ) e. CC')], 'addcld', '%s e. CC' % W3)
    rw3 = st([cl1(w, a, '3re', '3 e. RR'), ur], 'crred', '( Re ` %s ) = 3' % W3)
    rs = st([sc], 'recld', '( Re ` S ) e. RR')
    rwr = st([w3c], 'recld', '( Re ` %s ) e. RR' % W3)
    L = {'( Re ` S )': rs, '( Re ` %s )' % W3: rwr}
    h2 = st([st([w3c, st([cl1(w, a, '2lt3', '2 < 3'), rw3], 'breqtrrd', '2 < ( Re ` %s )' % W3)], 'jca', '( %s e. CC /\\ 2 < ( Re ` %s ) )' % (W3, W3)),
             st([cl1(w, a, '2re', '2 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 2 < ( Re ` %s ) ) )' % (W3, HP2, W3, W3))], 'mpbird', '%s e. %s' % (W3, HP2))
    gs = linarith(w, a, [rw3, s0], '-u ( Re ` S ) < ( Re ` %s )' % W3, leaves=L)
    u5 = st([st([w3c, gs], 'jca', '( %s e. CC /\\ -u ( Re ` S ) < ( Re ` %s ) )' % (W3, W3)),
             st([st([rs], 'renegcld', '-u ( Re ` S ) e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ -u ( Re ` S ) < ( Re ` %s ) ) )' % (W3, U5, W3, W3))],
            'mpbird', '%s e. %s' % (W3, U5))
    r0 = cl1(w, a, 're0', '( Re ` 0 ) = 0')
    n0 = nere(w, a, W3, '0', rw3, '3', r0, '0', [], {})
    one_ = cl1(w, a, 'ax-1cn', '1 e. CC')
    P = '( 1 - S )'
    rp = st([st([one_, sc], 'resubd', '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` S ) )' % P),
             st([cl1(w, a, 're1', '( Re ` 1 ) = 1')], 'oveq1d', '( ( Re ` 1 ) - ( Re ` S ) ) = ( 1 - ( Re ` S ) )')], 'eqtrd', '( Re ` %s ) = ( 1 - ( Re ` S ) )' % P)
    nP = nere(w, a, W3, P, rw3, '3', rp, '( 1 - ( Re ` S ) )', [s0], {'( Re ` S )': rs})
    m1 = linarith(w, a, [rw3], '-u 1 < ( Re ` %s )' % W3, leaves=L)
    dg = st([st([w3c, st([m1, n0], 'jca', '( -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (W3, W3))], 'jca', '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ %s =/= 0 ) )' % (W3, W3, W3)),
             w.inst('z6rdg')], 'syl', '%s e. %s' % (W3, DG))
    UP = '( %s \\ { %s } )' % (U5, P)
    up = st([st([u5, nP], 'jca', '( %s e. %s /\\ %s =/= %s )' % (W3, U5, W3, P)), cl1(w, a, 'eldifsn', '( %s e. %s <-> ( %s e. %s /\\ %s =/= %s ) )' % (W3, UP, W3, U5, W3, P))],
            'mpbird', '%s e. %s' % (W3, UP))
    ds = st([st([dg, up], 'jca', '( %s e. %s /\\ %s e. %s )' % (W3, DG, W3, UP)), cl1(w, a, 'elin', '( %s e. %s <-> ( %s e. %s /\\ %s e. %s ) )' % (W3, DS, W3, DG, W3, UP))],
            'mpbird', '%s e. %s' % (W3, DS))
    # the point s = S + W3
    swc = st([sc, w3c], 'addcld', '%s e. CC' % SW)
    rsw = st([st([sc, w3c], 'readdd', '( Re ` %s ) = ( ( Re ` S ) + ( Re ` %s ) )' % (SW, W3)), st([rw3], 'oveq2d', '( ( Re ` S ) + ( Re ` %s ) ) = ( ( Re ` S ) + 3 )' % W3)],
             'eqtrd', '( Re ` %s ) = ( ( Re ` S ) + 3 )' % SW)
    rswr = st([swc], 'recld', '( Re ` %s ) e. RR' % SW)
    L2 = {'( Re ` S )': rs, '( Re ` %s )' % SW: rswr}
    g1 = linarith(w, a, [rsw, s0], '1 < ( Re ` %s )' % SW, leaves=L2)
    g0 = linarith(w, a, [rsw, s0], '0 < ( Re ` %s )' % SW, leaves=L2)
    hpz = st([st([swc, g0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (SW, SW)), st([cl1(w, a, '0re', '0 e. RR'), w.inst('elhp2')], 'syl',
                                                                                    '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (SW, HPZ, SW, SW))], 'mpbird', '%s e. %s' % (SW, HPZ))
    LSs = lambda s: 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u %s ) )' % s
    BODY = lambda s: '( 1 < ( Re ` %s ) -> ( E ` %s ) = ( ( %s - 1 ) x. %s ) )' % (s, s, s, LSs(s))
    idx = w.s([], 'id', '( s = %s -> s = %s )' % (SW, SW))
    cg, new = w.wcongr(BODY('s'), {'s': SW}, 's = %s' % SW, {'s': idx})
    assert new == BODY(SW), new
    rsp = w.s([cg], 'rspcv', '( %s e. %s -> ( %s -> %s ) )' % (SW, HPZ, DSER, BODY(SW)))
    ds1 = st([hpz, f[DSER], rsp], 'sylc', BODY(SW))
    de = st([g1, ds1], 'mpd', '( E ` %s ) = ( ( %s - 1 ) x. %s )' % (SW, SW, LSs(SW)))
    # LS ( SW ) e. CC (dserbnd)
    idm = w.s([], 'id', '( j = m -> j = m )')
    cgm, newm = w.wcongr('( abs ` ( C ` j ) ) <_ 1', {'j': 'm'}, 'j = m', {'j': idm})
    cbm = w.s([cgm], 'cbvralvw', '( %s <-> A. m e. NN ( abs ` ( C ` m ) ) <_ 1 )' % CB)
    cbmm = st([f[CB], c_(w, a, cbm, '( %s <-> A. m e. NN ( abs ` ( C ` m ) ) <_ 1 )' % CB)], 'mpbid', 'A. m e. NN ( abs ` ( C ` m ) ) <_ 1')
    dh = st([st([f['C : NN --> CC'], cl1(w, a, '1re', '1 e. RR'), cbmm], '3jca', '( C : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( C ` m ) ) <_ 1 )'),
             st([swc, g1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SW, SW))], 'jca',
            '( ( C : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( C ` m ) ) <_ 1 ) /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (SW, SW))
    lsb = st([dh, w.inst('dserbnd')], 'syl', '( abs ` %s ) <_ ( 1 x. ( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) )' % (LSs(SW), SW))
    lsc = st([lsb, w.inst('z6absle')], 'syl', '%s e. CC' % LSs(SW))
    rs1 = st([st([swc, one_], 'resubd', '( Re ` ( %s - 1 ) ) = ( ( Re ` %s ) - ( Re ` 1 ) )' % (SW, SW)),
              st([cl1(w, a, 're1', '( Re ` 1 ) = 1')], 'oveq2d', '( ( Re ` %s ) - ( Re ` 1 ) ) = ( ( Re ` %s ) - 1 )' % (SW, SW))], 'eqtrd', '( Re ` ( %s - 1 ) ) = ( ( Re ` %s ) - 1 )' % (SW, SW))
    s1n = nere(w, a, '( %s - 1 )' % SW, '0', rs1, '( ( Re ` %s ) - 1 )' % SW, r0, '0', [rsw, s0], L2)
    s1c = st([swc, one_], 'subcld', '( %s - 1 ) e. CC' % SW)
    dv = st([lsc, s1c, s1n], 'divcan3d', '( ( ( %s - 1 ) x. %s ) / ( %s - 1 ) ) = %s' % (SW, LSs(SW), SW, LSs(SW)))
    EQ = st([st([de], 'oveq1d', '( ( E ` %s ) / ( %s - 1 ) ) = ( ( ( %s - 1 ) x. %s ) / ( %s - 1 ) )' % (SW, SW, SW, LSs(SW), SW)), dv], 'eqtrd',
            '( ( E ` %s ) / ( %s - 1 ) ) = %s' % (SW, SW, LSs(SW)))
    g3v, g3val = mpval(w, a, 'w', HP2, mbody(G3('R'), 'w', HP2), W3, h2)
    grv, grval = mpval(w, a, 'w', DS, mbody(GR('R'), 'w', DS), W3, ds)
    MR_ = MRr('R', SW)
    GXW = '( ( _G ` %s ) x. ( %s ^c %s ) )' % (W3, X, W3)
    assert g3val == '( %s x. ( %s x. %s ) )' % (GXW, LSs(SW), MR_), g3val
    assert grval == '( %s x. ( ( ( E ` %s ) / ( %s - 1 ) ) x. %s ) )' % (GXW, SW, SW, MR_), grval
    e2 = st([st([EQ], 'oveq1d', '( ( ( E ` %s ) / ( %s - 1 ) ) x. %s ) = ( %s x. %s )' % (SW, SW, MR_, LSs(SW), MR_))], 'oveq2d', '%s = %s' % (grval, g3val))
    w.qed([g3v, st([grv, e2], 'eqtrd', '( %s ` %s ) = %s' % (GR('R'), W3, g3val))], 'eqtr4d', STATEMENTS['z6g3gr'])
    return w


# ================================================================== z6detr
def res5cc(w, a, f, R='R'):
    """( a -> RES5(R) e. CC ) (as in z6shiftr's generator); needs f['R e. NN'] for z6b_r.dfacts"""
    st = mkst(w, a)
    d = z6b_r.dfacts(w, a, f)
    sc = f['S e. CC']
    P = '( 1 - S )'
    one_ = cl1(w, a, 'ax-1cn', '1 e. CC')
    pc = st([one_, sc], 'subcld', '%s e. CC' % P)
    pdg, _ = applyn(w, a, 'z6pdg', {}, f)
    gpc = st([pdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % P)
    xpc = st([st([d['xrp']], 'rpcnd', '%s e. CC' % X), pc], 'cxpcld', '( %s ^c %s ) e. CC' % (X, P))
    oneh = st([st([one_, st([cl1(w, a, '0lt1', '0 < 1'), cl1(w, a, 're1', '( Re ` 1 ) = 1')], 'breqtrrd', '0 < ( Re ` 1 )')],
                  'jca', '( 1 e. CC /\\ 0 < ( Re ` 1 ) )'), st([cl1(w, a, '0re', '0 e. RR'), w.inst('elhp2')], 'syl',
                                                             '( 1 e. %s <-> ( 1 e. CC /\\ 0 < ( Re ` 1 ) ) )' % HPZ)], 'mpbird', '1 e. %s' % HPZ)
    e1c = st([st([f['E e. ( %s -cn-> CC )' % HPZ], w.inst('cncff')], 'syl', 'E : %s --> CC' % HPZ), oneh], 'ffvelcdmd', '( E ` 1 ) e. CC')
    resc = st([f['( E ` 1 ) = %s' % RESV], e1c], 'eqeltrrd', '%s e. CC' % RESV)
    m1c = z6b_r.mrcc(w, a, d['mff'], '1', one_)
    gx = st([gpc, xpc], 'mulcld', '%s e. CC' % GX)
    return st([gx, st([resc, m1c], 'mulcld', '( %s x. %s ) e. CC' % (RESV, MRr('R', '1')))], 'mulcld', '%s e. CC' % RES5), gx, resc, m1c


def z6detr():
    w = W('z6detr', 'One pseudocharacter modulus, shifted (Lean ` tsum_Sterm_eq_integral_shift ` and ` tsum_Sterm_eq_integral_shift_principal ` in one statement): '
          'the anchor identity ~ z6anchor at ` Re w = 3 ` , the two integrands agree there (~ z6g3gr , ~ z6vleq ), the shift ~ z6shiftr to ` Re w = CL ` , '
          'divided by ` 2 pi i ` .')
    a = ante('z6detr'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    rn, mu, _, _ = rsetnn(w, a, f, f['R e. %s' % RSD], r='R')
    f['R e. NN'] = rn; f['( mmu ` R ) =/= 0'] = mu
    rs = st([f['S e. CC']], 'recld', '( Re ` S ) e. RR')
    f['0 <_ ( Re ` S )'] = linarith(w, a, [f['( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )']], '0 <_ ( Re ` S )', leaves={'( Re ` S )': rs})
    an, _ = applyn(w, a, 'z6anchor', {}, f)
    SS = SSUM('R')
    an1 = st([an], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % STFR('R'))
    an2 = st([an], 'simprd', '( %s x. %s ) = %s' % (TPI, SS, VL(G3('R'), '3')))
    # the line Re w = 3: G3 and GR agree
    au = '( %s /\\ u e. RR )' % a; t = mkst(w, au); fu = LZ(w, f, au)
    fu['u e. RR'] = t([], 'simpr', 'u e. RR')
    gg, gc = applyn(w, au, 'z6g3gr', {'U': 'u'}, fu)
    ral = st([gg], 'ralrimiva', 'A. u e. RR %s' % gc)
    fre = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.s([], 'cnex', 'CC e. _V'), w.s([], 'fex', '( ( Re : CC --> RR /\\ CC e. _V ) -> Re e. _V )')], 'mp2an', 'Re e. _V')
    hp2x = w.s([w.s([fre], 'cnvex', "`' Re e. _V")], 'imaex', '%s e. _V' % HP2)
    g3x = st([c_(w, a, hp2x, '%s e. _V' % HP2)], 'mptexd', '%s e. _V' % G3('R'))
    dgx = w.s([w.s([], 'cnex', 'CC e. _V')], 'difexi', '%s e. _V' % DG)
    dsx = w.s([dgx], 'inex1', '%s e. _V' % DS)
    grx = st([c_(w, a, dsx, '%s e. _V' % DS)], 'mptexd', '%s e. _V' % GR('R'))
    fz = {'3 e. RR': cl1(w, a, '3re', '3 e. RR'), '%s e. _V' % G3('R'): g3x, '%s e. _V' % GR('R'): grx, 'A. u e. RR %s' % gc: ral}
    vq, _ = applyn(w, a, 'z6vleq', {'C': '3', 'F': G3('R'), 'G': GR('R'), 'V': '_V', 'W': '_V'}, fz)
    sh, _ = applyn(w, a, 'z6shiftr', {}, f)
    ec, _ = applyn(w, a, 'z6ectrl', {}, f)
    VLC = VL(GR('R'), CL); V3 = VL(GR('R'), '3')
    vlc = st([st([ec], 'simprd', split_imp(STATEMENTS['z6ectrl'])[1].split(' /\\ ', 1)[1][:-2] if False else None) if False else None], 'x', 'x') if False else None
    ecr = split_imp(STATEMENTS['z6ectrl'])[1]
    from z6a_e3 import _split
    ec2 = st([ec], 'simprd', _split(ecr)[1])
    vlcc = st([ec2, w.inst('z6absle')], 'syl', '%s e. CC' % VLC)
    k5c, gx, resc, m1c = res5cc(w, a, f)
    tc, tn = tpi_facts(w, a)
    # SS e. CC (isumcl with the letter m, then cbvsumv)
    am = '( %s /\\ m e. NN )' % a; tm_ = mkst(w, am); fm = LZ(w, f, am)
    mn = tm_([], 'simpr', 'm e. NN')
    cm = stcc(w, am, fm, 'R', 'm', mn, lift(w, rn, am))
    mv, _ = mpval(w, am, 'n', 'NN', STERM('R', 'n'), 'm', mn)
    ssm = st([w.s([], 'nnuz', NNUZ), cl1(w, a, '1z', '1 e. ZZ'), mv, cm['st'], an1], 'isumcl', 'sum_ m e. NN %s e. CC' % STERM('R', 'm'))
    cbs = cbvsum_nm(w, 'm', 'n', body=lambda v: STERM('R', v))
    ssc = st([c_(w, a, cbs, 'sum_ m e. NN %s = %s' % (STERM('R', 'm'), SS)), ssm], 'eqeltrrd', '%s e. CC' % SS)
    # TPI SS = V3 = VLC + TPI RES5
    t1 = st([an2, vq], 'eqtrd', '( %s x. %s ) = %s' % (TPI, SS, V3))
    TK = '( %s x. %s )' % (TPI, RES5)
    tkc = st([tc, k5c], 'mulcld', '%s e. CC' % TK)
    v3c = st([t1, st([tc, ssc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, SS))], 'eqeltrrd', '%s e. CC' % V3)
    t2 = st([sh, st([v3c, vlcc, tkc], 'subaddd', '( ( %s - %s ) = %s <-> ( %s + %s ) = %s )' % (V3, VLC, TK, VLC, TK, V3))], 'mpbid', '( %s + %s ) = %s' % (VLC, TK, V3))
    IT = '( 1 / %s )' % TPI
    itc = st([tc, tn], 'reccld', '%s e. CC' % IT)
    Z = '( ( %s x. %s ) + %s )' % (IT, VLC, RES5)
    u1 = st([tc, st([itc, vlcc], 'mulcld', '( %s x. %s ) e. CC' % (IT, VLC)), k5c], 'adddid', '( %s x. %s ) = ( ( %s x. ( %s x. %s ) ) + %s )' % (TPI, Z, TPI, IT, VLC, TK))
    u2 = st([st([tc, itc, vlcc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (TPI, IT, VLC, TPI, IT, VLC))], 'eqcomd',
            '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (TPI, IT, VLC, TPI, IT, VLC))
    u3 = st([st([tc, tn], 'recidd', '( %s x. %s ) = 1' % (TPI, IT))], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (TPI, IT, VLC, VLC))
    u4 = st([t([], 'x', 'x') if False else st([vlcc], 'mullidd', '( 1 x. %s ) = %s' % (VLC, VLC))], 'x', 'x') if False else st([vlcc], 'mullidd', '( 1 x. %s ) = %s' % (VLC, VLC))
    u5 = st([st([u2, u3], 'eqtrd', '( %s x. ( %s x. %s ) ) = ( 1 x. %s )' % (TPI, IT, VLC, VLC)), u4], 'eqtrd', '( %s x. ( %s x. %s ) ) = %s' % (TPI, IT, VLC, VLC))
    u6 = st([u5], 'oveq1d', '( ( %s x. ( %s x. %s ) ) + %s ) = ( %s + %s )' % (TPI, IT, VLC, TK, VLC, TK))
    u7 = st([st([u1, u6], 'eqtrd', '( %s x. %s ) = ( %s + %s )' % (TPI, Z, VLC, TK)), t2], 'eqtrd', '( %s x. %s ) = %s' % (TPI, Z, V3))
    zc = st([st([itc, vlcc], 'mulcld', '( %s x. %s ) e. CC' % (IT, VLC)), k5c], 'addcld', '%s e. CC' % Z)
    u8 = st([t1, u7], 'eqtr4d', '( %s x. %s ) = ( %s x. %s )' % (TPI, SS, TPI, Z))
    sz = st([u8, st([ssc, zc, tc, tn], 'mulcand', '( ( %s x. %s ) = ( %s x. %s ) <-> %s = %s )' % (TPI, SS, TPI, Z, SS, Z))], 'mpbid', '%s = %s' % (SS, Z))
    IR = '( 1 / R )'
    irc = st([st([rn], 'nncnd', 'R e. CC'), st([rn], 'nnne0d', 'R =/= 0')], 'reccld', '%s e. CC' % IR)
    v1 = st([sz], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (IR, SS, IR, Z))
    v2 = st([irc, st([itc, vlcc], 'mulcld', '( %s x. %s ) e. CC' % (IT, VLC)), k5c], 'adddid',
            '( %s x. %s ) = ( ( %s x. ( %s x. %s ) ) + ( %s x. %s ) )' % (IR, Z, IR, IT, VLC, IR, RES5))
    v3 = st([irc, itc, vlcc], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (IR, IT, VLC, IT, IR, VLC))
    v4 = st([v3], 'oveq1d', '( ( %s x. ( %s x. %s ) ) + ( %s x. %s ) ) = ( ( %s x. ( %s x. %s ) ) + ( %s x. %s ) )' % (IR, IT, VLC, IR, RES5, IT, IR, VLC, IR, RES5))
    fin = st([st([v1, v2], 'eqtrd', '( %s x. %s ) = ( ( %s x. ( %s x. %s ) ) + ( %s x. %s ) )' % (IR, SS, IR, IT, VLC, IR, RES5)), v4], 'eqtrd',
             '( %s x. %s ) = ( ( %s x. ( %s x. %s ) ) + ( %s x. %s ) )' % (IR, SS, IT, IR, VLC, IR, RES5))
    w.qed([st([vlcc, k5c], 'jca', '( %s e. CC /\\ %s e. CC )' % (VLC, RES5)), fin], 'jca', STATEMENTS['z6detr'])
    return w


# ================================================================== z6epsum
def z6epsum():
    w = W('z6epsum', 'The residues at the pole ` w = 1 - S ` , weighted and summed over the moduli, are ` Epole ` (~ z5epval for the principal character, '
          '~ z5ep0 otherwise; the ` Epole ` rewriting in Lean ` detection_identity_all ` ).')
    a = ante('z6epsum'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    p1c, fin, nv, rv = p1dcc(w, a, f)
    cv = st([f['C : NN --> CC'], cl1(w, a, 'nnex', 'NN e. _V')], 'fexd', 'C e. _V')
    ov = lambda T: cl1(w, a, 'ovex', '%s e. _V' % T)
    S6 = ('( ( %s e. _V /\\ %s e. _V /\\ %s e. _V ) /\\ ( C e. _V /\\ N e. _V /\\ %s e. _V ) )' % (Z1D, Z2D, X, RPD))
    s6 = st([st([ov(Z1D), ov(Z2D), ov(X)], '3jca', '( %s e. _V /\\ %s e. _V /\\ %s e. _V )' % (Z1D, Z2D, X)), st([cv, nv, rv], '3jca', '( C e. _V /\\ N e. _V /\\ %s e. _V )' % RPD)],
            'jca', S6)
    s6s = st([s6, f['S e. CC']], 'jca', '( %s /\\ S e. CC )' % S6)
    # PRN = PRH
    idh = w.s([], 'id', '( n = h -> n = h )')
    cgh, newh = w.congr('if ( ( n gcd N ) = 1 , 1 , 0 )', {'n': 'h'}, 'n = h', {'n': idh})
    prh = w.s([cgh], 'cbvmptv', '%s = %s' % (PRN, PRH))
    # the r-closures
    ar = '( %s /\\ r e. %s )' % (a, RSD); t = mkst(w, ar); fl = LZ(w, f, ar)
    rn, mu, _, _ = rsetnn(w, ar, fl, t([], 'simpr', 'r e. %s' % RSD))
    irc = t([t([rn], 'nncnd', 'r e. CC'), t([rn], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    M1 = MRr('r', '1')
    m1c = t([t([t([fl[sub(HAB0, {'A': Z1D, 'B': Z2D})], rn], 'jca', '( %s /\\ r e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})),
                t([fl['C : NN --> CC'], cl1(w, ar, 'ax-1cn', '1 e. CC')], 'jca', '( C : NN --> CC /\\ 1 e. CC )')], 'jca',
               '( ( %s /\\ r e. NN ) /\\ ( C : NN --> CC /\\ 1 e. CC ) )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z5mrcl')], 'syl', '%s e. CC' % M1)
    # GX e. CC
    P = '( 1 - S )'
    pdg, _ = applyn(w, a, 'z6pdg', {}, f)
    gpc = st([pdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % P)
    pc = st([cl1(w, a, 'ax-1cn', '1 e. CC'), f['S e. CC']], 'subcld', '%s e. CC' % P)
    xpc = st([st([f['%s e. RR+' % X]], 'rpcnd', '%s e. CC' % X), pc], 'cxpcld', '( %s ^c %s ) e. CC' % (X, P))
    gxc = st([gpc, xpc], 'mulcld', '%s e. CC' % GX)
    nn_ = f['N e. NN']
    phc = st([st([st([nn_, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nncnd', '( phi ` N ) e. CC'), st([nn_], 'nncnd', 'N e. CC'), st([nn_], 'nnne0d', 'N =/= 0')],
             'divcld', '%s e. CC' % PHN)
    TERM = lambda R_: '( ( 1 / r ) x. %s )' % sub(RES5, {'R': R_})
    # case C = PRN
    c1 = '( %s /\\ C = %s )' % (a, PRN); t1 = mkst(w, c1)
    rv1 = t1([t1([], 'simpr', 'C = %s' % PRN)], 'iftrued', '%s = %s' % (RESV, PHN))
    c1r = '( %s /\\ r e. %s )' % (c1, RSD); u = mkst(w, c1r)
    rnl = lambda s_: lift(w, s_, c1r) if False else None
    # lift closures from ar to c1r: build c1r facts by re-deriving r closures
    fl1 = LZ(w, f, c1r)
    rn1, _, _, _ = rsetnn(w, c1r, fl1, u([], 'simpr', 'r e. %s' % RSD))
    ir1 = u([u([rn1], 'nncnd', 'r e. CC'), u([rn1], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    m11 = u([u([u([fl1[sub(HAB0, {'A': Z1D, 'B': Z2D})], rn1], 'jca', '( %s /\\ r e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})),
                u([fl1['C : NN --> CC'], cl1(w, c1r, 'ax-1cn', '1 e. CC')], 'jca', '( C : NN --> CC /\\ 1 e. CC )')], 'jca',
               '( ( %s /\\ r e. NN ) /\\ ( C : NN --> CC /\\ 1 e. CC ) )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z5mrcl')], 'syl', '%s e. CC' % M1)
    gx1 = lift(w, gxc, c1r); ph1 = lift(w, phc, c1r)
    q1 = u([u([u([lift(w, rv1, c1r)], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (RESV, M1, PHN, M1))], 'oveq2d',
              '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (GX, RESV, M1, GX, PHN, M1))], 'oveq2d',
           '%s = ( ( 1 / r ) x. ( %s x. ( %s x. %s ) ) )' % (TERM('r'), GX, PHN, M1))
    q2 = u([u([u([gx1, ph1, m11], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (GX, PHN, M1, GX, PHN, M1))], 'eqcomd',
              '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (GX, PHN, M1, GX, PHN, M1))], 'oveq2d',
           '( ( 1 / r ) x. ( %s x. ( %s x. %s ) ) ) = ( ( 1 / r ) x. ( ( %s x. %s ) x. %s ) )' % (GX, PHN, M1, GX, PHN, M1))
    GP = '( %s x. %s )' % (GX, PHN)
    gp1 = u([gx1, ph1], 'mulcld', '%s e. CC' % GP)
    q3 = u([ir1, gp1, m11], 'mul12d', '( ( 1 / r ) x. ( %s x. %s ) ) = ( %s x. ( ( 1 / r ) x. %s ) )' % (GP, M1, GP, M1))
    per1 = u([u([q1, q2], 'eqtrd', '%s = ( ( 1 / r ) x. ( %s x. %s ) )' % (TERM('r'), GP, M1)), q3], 'eqtrd', '%s = ( %s x. ( ( 1 / r ) x. %s ) )' % (TERM('r'), GP, M1))
    SM = 'sum_ r e. %s ( ( 1 / r ) x. %s )' % (RSD, M1)
    sa = t1([per1], 'sumeq2dv', 'sum_ r e. %s %s = sum_ r e. %s ( %s x. ( ( 1 / r ) x. %s ) )' % (RSD, TERM('r'), RSD, GP, M1))
    sb = t1([lift(w, fin, c1), lift(w, st([gxc, phc], 'mulcld', '%s e. CC' % GP), c1), u([ir1, m11], 'mulcld', '( ( 1 / r ) x. %s ) e. CC' % M1)], 'fsummulc2',
            '( %s x. %s ) = sum_ r e. %s ( %s x. ( ( 1 / r ) x. %s ) )' % (GP, SM, RSD, GP, M1))
    EPB = '( %s x. %s )' % (GP, SM)
    sc1 = t1([sa, sb], 'eqtr4d', 'sum_ r e. %s %s = %s' % (RSD, TERM('r'), EPB))
    epv = t1([lift(w, s6s, c1), w.inst('z5epval')], 'syl', '%s = if ( C = %s , %s , 0 )' % (EPC, PRH, EPB))
    cph = t1([t1([], 'simpr', 'C = %s' % PRN), c_(w, c1, prh, '%s = %s' % (PRN, PRH))], 'eqtrd', 'C = %s' % PRH)
    ep1 = t1([epv, t1([cph], 'iftrued', 'if ( C = %s , %s , 0 ) = %s' % (PRH, EPB, EPB))], 'eqtrd', '%s = %s' % (EPC, EPB))
    case1 = t1([sc1, ep1], 'eqtr4d', 'sum_ r e. %s %s = %s' % (RSD, TERM('r'), EPC))
    # case C =/= PRN
    c0 = '( %s /\\ -. C = %s )' % (a, PRN); t0 = mkst(w, c0)
    rv0 = t0([t0([], 'simpr', '-. C = %s' % PRN)], 'iffalsed', '%s = 0' % RESV)
    c0r = '( %s /\\ r e. %s )' % (c0, RSD); v = mkst(w, c0r)
    fl0 = LZ(w, f, c0r)
    rn0, _, _, _ = rsetnn(w, c0r, fl0, v([], 'simpr', 'r e. %s' % RSD))
    ir0 = v([v([rn0], 'nncnd', 'r e. CC'), v([rn0], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    m10 = v([v([v([fl0[sub(HAB0, {'A': Z1D, 'B': Z2D})], rn0], 'jca', '( %s /\\ r e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})),
                v([fl0['C : NN --> CC'], cl1(w, c0r, 'ax-1cn', '1 e. CC')], 'jca', '( C : NN --> CC /\\ 1 e. CC )')], 'jca',
               '( ( %s /\\ r e. NN ) /\\ ( C : NN --> CC /\\ 1 e. CC ) )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z5mrcl')], 'syl', '%s e. CC' % M1)
    z1 = v([v([lift(w, rv0, c0r)], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (RESV, M1, M1)), v([m10], 'mul02d', '( 0 x. %s ) = 0' % M1)], 'eqtrd', '( %s x. %s ) = 0' % (RESV, M1))
    z2 = v([v([z1], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. 0 )' % (GX, RESV, M1, GX)), v([lift(w, gxc, c0r)], 'mul01d', '( %s x. 0 ) = 0' % GX)], 'eqtrd',
           '( %s x. ( %s x. %s ) ) = 0' % (GX, RESV, M1))
    z3 = v([v([z2], 'oveq2d', '%s = ( ( 1 / r ) x. 0 )' % TERM('r')), v([ir0], 'mul01d', '( ( 1 / r ) x. 0 ) = 0')], 'eqtrd', '%s = 0' % TERM('r'))
    s0 = t0([z3], 'sumeq2dv', 'sum_ r e. %s %s = sum_ r e. %s 0' % (RSD, TERM('r'), RSD))
    sz = t0([t0([lift(w, fin, c0)], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (RSD, RSD)), w.inst('sumz')], 'syl', 'sum_ r e. %s 0 = 0' % RSD)
    cne = t0([t0([t0([], 'simpr', '-. C = %s' % PRN)], 'neqned', 'C =/= %s' % PRN), c_(w, c0, prh, '%s = %s' % (PRN, PRH))], 'neeqtrd', 'C =/= %s' % PRH)
    ep0 = t0([t0([lift(w, s6s, c0), cne], 'jca', '( ( %s /\\ S e. CC ) /\\ C =/= %s )' % (S6, PRH)), w.inst('z5ep0')], 'syl', '%s = 0' % EPC)
    case0 = t0([t0([s0, sz], 'eqtrd', 'sum_ r e. %s %s = 0' % (RSD, TERM('r'))), ep0], 'eqtr4d', 'sum_ r e. %s %s = %s' % (RSD, TERM('r'), EPC))
    w.qed([case1, case0], 'pm2.61dan', STATEMENTS['z6epsum'])
    return w


# ================================================================== z6detid
def z6detid():
    w = W('z6detid', 'Blueprint Lemma 4.1 (Lean ` detection_identity_all ` , every character): at a zero ` S ` of ` E ` in the detection box, '
          '` F ( S ) + e ^ ( -1 / X ) P ( 1 ) = E_ctr + E_pole ` : the split ~ z6split , each modulus shifted (~ z6detr ), the residues summed (~ z6epsum ).')
    a = ante('z6detid'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    rs = st([f['S e. CC']], 'recld', '( Re ` S ) e. RR')
    f['0 <_ ( Re ` S )'] = linarith(w, a, [f['( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )']], '0 <_ ( Re ` S )', leaves={'( Re ` S )': rs})
    sp, _ = applyn(w, a, 'z6split', {}, f)
    p1c, fin, nv, rv = p1dcc(w, a, f)
    ar = '( %s /\\ r e. %s )' % (a, RSD); t = mkst(w, ar); fl = LZ(w, f, ar)
    fl['r e. %s' % RSD] = t([], 'simpr', 'r e. %s' % RSD)
    dr, drc = applyn(w, ar, 'z6detr', {'R': 'r'}, fl)
    VLr = VL(GR('r'), CL); Kr = RES5R('r')
    cl_ = t([dr], 'simpld', '( %s e. CC /\\ %s e. CC )' % (VLr, Kr))
    eq = t([dr], 'simprd', split_imp(sub(STATEMENTS['z6detr'], {'R': 'r'}))[1].split(' /\\ ( ( 1 / r )', 1)[0] if False else
           '( ( 1 / r ) x. %s ) = ( ( ( 1 / %s ) x. ( ( 1 / r ) x. %s ) ) + ( ( 1 / r ) x. %s ) )' % (SSUM('r'), TPI, VLr, Kr))
    vlc = t([cl_], 'simpld', '%s e. CC' % VLr); kc = t([cl_], 'simprd', '%s e. CC' % Kr)
    rn, mu, _, _ = rsetnn(w, ar, fl, fl['r e. %s' % RSD])
    irc = t([t([rn], 'nncnd', 'r e. CC'), t([rn], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    tc, tn = tpi_facts(w, a)
    IT = '( 1 / %s )' % TPI
    itc = st([tc, tn], 'reccld', '%s e. CC' % IT)
    A_ = '( ( 1 / r ) x. %s )' % VLr; B_ = '( ( 1 / r ) x. %s )' % Kr
    ac = t([irc, vlc], 'mulcld', '%s e. CC' % A_)
    bc = t([irc, kc], 'mulcld', '%s e. CC' % B_)
    iac = t([lift(w, itc, ar), ac], 'mulcld', '( %s x. %s ) e. CC' % (IT, A_))
    s1 = st([eq], 'sumeq2dv', 'sum_ r e. %s ( ( 1 / r ) x. %s ) = sum_ r e. %s ( ( %s x. %s ) + %s )' % (RSD, SSUM('r'), RSD, IT, A_, B_))
    s2 = st([fin, iac, bc], 'fsumadd', 'sum_ r e. %s ( ( %s x. %s ) + %s ) = ( sum_ r e. %s ( %s x. %s ) + sum_ r e. %s %s )' % (RSD, IT, A_, B_, RSD, IT, A_, RSD, B_))
    s3 = st([st([fin, itc, ac], 'fsummulc2', '( %s x. sum_ r e. %s %s ) = sum_ r e. %s ( %s x. %s )' % (IT, RSD, A_, RSD, IT, A_))], 'eqcomd',
            'sum_ r e. %s ( %s x. %s ) = %s' % (RSD, IT, A_, ECTR))
    ep, _ = applyn(w, a, 'z6epsum', {}, f)
    s4 = st([s3, ep], 'oveq12d', '( sum_ r e. %s ( %s x. %s ) + sum_ r e. %s %s ) = ( %s + %s )' % (RSD, IT, A_, RSD, B_, ECTR, EPC))
    ch = st([st([sp, s1], 'eqtrd', '( %s + ( %s x. %s ) ) = sum_ r e. %s ( ( %s x. %s ) + %s )' % (FDV, E1, P1D, RSD, IT, A_, B_)), s2], 'eqtrd',
            '( %s + ( %s x. %s ) ) = ( sum_ r e. %s ( %s x. %s ) + sum_ r e. %s %s )' % (FDV, E1, P1D, RSD, IT, A_, RSD, B_))
    w.qed([ch, s4], 'eqtrd', STATEMENTS['z6detid'])
    return w


# ================================================================== z6detall
def z6detall():
    w = W('z6detall', 'Blueprint Lemmas 4.1 + 4.2 (Lean ` detection_estimate_all ` ): the hypothesis ` DetectionEstimate ` of ~ z5ddlb holds at every zero '
          '` S ` of ` E ` in the detection box under (T1): ~ z6detid and ~ z6ectr .')
    a = ante('z6detall'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    di = w.s([], 'z6detid', STATEMENTS['z6detid'])
    ec, _ = applyn(w, a, 'z6ectr', {}, f)
    ecc = st([ec, w.inst('z6absle')], 'syl', '%s e. CC' % ECTR)
    p1c, fin, nv, rv = p1dcc(w, a, f)
    ep = w.s([], 'z6epsum', STATEMENTS['z6epsum'])
    ar = '( %s /\\ r e. %s )' % (a, RSD); t = mkst(w, ar); fl = LZ(w, f, ar)
    fl['r e. %s' % RSD] = t([], 'simpr', 'r e. %s' % RSD)
    dr, _ = applyn(w, ar, 'z6detr', {'R': 'r'}, fl)
    Kr = RES5R('r')
    kc = t([t([dr], 'simpld', '( %s e. CC /\\ %s e. CC )' % (VL(GR('r'), CL), Kr))], 'simprd', '%s e. CC' % Kr)
    rn, mu, _, _ = rsetnn(w, ar, fl, fl['r e. %s' % RSD])
    irc = t([t([rn], 'nncnd', 'r e. CC'), t([rn], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    sc = st([fin, t([irc, kc], 'mulcld', '( ( 1 / r ) x. %s ) e. CC' % Kr)], 'fsumcl', 'sum_ r e. %s ( ( 1 / r ) x. %s ) e. CC' % (RSD, Kr))
    epc = st([ep, sc], 'eqeltrrd' if False else 'x', 'x') if False else st([ep, sc], 'eqeltrrd', '%s e. CC' % EPC)
    L = '( %s + ( %s x. %s ) )' % (FDV, E1, P1D)
    e1 = st([di], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (L, EPC, ECTR, EPC, EPC))
    e2 = st([ecc, epc], 'pncand', '( ( %s + %s ) - %s ) = %s' % (ECTR, EPC, EPC, ECTR))
    e3 = st([st([e1, e2], 'eqtrd', '( %s - %s ) = %s' % (L, EPC, ECTR))], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (L, EPC, ECTR))
    w.qed([e3, ec], 'eqbrtrd', STATEMENTS['z6detall'])
    return w


# ================================================================== z6dlbz
def z6dlbz():
    w = W('z6dlbz', 'Blueprint Proposition 4.4, unconditional, every character (Lean ` detector_lower_bound_of_zero_all ` , at a general ` sigma = T ` with '
          '` 0 <_ T <_ Re S ` ): ` ( 1 / 400 ) ( phi ( N ) / N ) log D <_ | F ( S ) | ` at every zero ` S =/= 1 ` of ` E ` in the detection box, '
          'with the height clause for the principal character: ~ z5ddlb with its ` DetectionEstimate ` discharged by ~ z6detall .')
    a = ante('z6dlbz'); f = unpack(w, a); st = mkst(w, a)
    dfx(w, a, f)
    rs = st([f['S e. CC']], 'recld', '( Re ` S ) e. RR')
    tr = f['T e. RR']
    L = {'( Re ` S )': rs, 'T': tr}
    f['0 <_ ( Re ` S )'] = linarith(w, a, [f['( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S )']], '0 <_ ( Re ` S )', leaves=L)
    f['T <_ 1'] = linarith(w, a, [f['T <_ ( Re ` S )'], f['( Re ` S ) <_ 1']], 'T <_ 1', leaves=L)
    f['%s e. CC' % FDV], _ = applyn(w, a, 'z6fdvcl', {}, f)
    A7_ = split_imp(STATEMENTS['z6detall'])[0]
    da = st([f[A7_], w.inst('z6detall')], 'syl', split_imp(STATEMENTS['z6detall'])[1])
    f[split_imp(STATEMENTS['z6detall'])[1]] = da
    lb, co = applyn(w, a, 'z5ddlb', {'F': FDV}, f)
    toqed(w, lb, 'z6dlbz')
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6g3gr, z6detr, z6epsum, z6detid, z6detall, z6dlbz]:
        if want(fn.__name__):
            if not run(fn()):
                break
