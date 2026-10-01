"""Sortie LD2, section 6 part 2: the per-point block (ld2macn ld2vlcv ld2licl ld2ptw ld2li ld2sq1).
Run: MM_DB=sorties/ld2.mm MM_ENGINE=mmatch python3 tools/gen/ld2_c.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ld2lib import *

only = sys.argv[1:]
want = lambda l: not only or l in only
L = LOGD
IS = '( Im ` S )'; RS = '( Re ` S )'


def rrss(w, A):
    return a1(w, A, 'ax-resscn', 'RR C_ CC')


def hab0(w, A, c, dr, d1):
    """HAB0 at ( D , 2 D ) and the RR+ triple from D e. RR, 1 < D"""
    D2 = '( 2 x. D )'
    z = linarith(w, A, [d1], '0 < D', closure=c)
    lt = linarith(w, A, [d1], 'D < %s' % D2, closure=c)
    return J(w, A, J(w, A, dr, z), J(w, A, c.mem(D2, 'RR'), lt))


def ld2macn():
    w = W('ld2macn', 'Lean ` continuous_Mr_line ` : ` u |-> abs Mr ( S + ( 1/2 - Re S ) + i u ) ` is continuous on ` RR ` (~ z6mrhol composed with the affine line, ~ cncfmpt1f , ~ abscncf ).')
    A = ante('ld2macn'); P = parts(w, A)
    dr, d1, cf, sc = P['D e. RR'], P['1 < D'], P['C : NN --> CC'], P['S e. CC']
    c = Closure(w, A, {'D': [('RR', dr), ('gt1', d1)], 'S': ('CC', sc), '_i': ('CC', a1(w, A, 'ax-icn', '_i e. CC'))})
    c.leaf(RS, 'RR', dst(w, A, [sc], 'recld', '%s e. RR' % RS))
    h0 = hab0(w, A, c, dr, d1)
    mh = dst(w, A, [ap(w, A, 'z6mrhol', [J(w, A, h0, a1(w, A, '1nn', '1 e. NN')), cf], subst(concl('z6mrhol'), {'A': 'D', 'B': '( 2 x. D )', 'R': '1'}))], 'simpld',
             '( s e. CC |-> ( %s ` s ) ) e. ( CC -cn-> CC )' % MRF)
    Au = '( %s /\\ u e. RR )' % A
    cu = Closure(w, Au, {'D': [('RR', lift(w, dr, Au)), ('gt1', lift(w, d1, Au))], 'S': ('CC', lift(w, sc, Au)), 'u': ('RR', w.s([], 'simpr', '( %s -> u e. RR )' % Au)), '_i': ('CC', a1(w, Au, 'ax-icn', '_i e. CC'))})
    cu.leaf(RS, 'RR', lift(w, c.mem(RS, 'RR'), Au))
    cn = CN(w, A, 'u', 'RR', rrss(w, A), c, cu)
    AFF = '( S + %s )' % HLU('u')
    acn = cn(AFF)
    G = '( s e. CC |-> ( %s ` s ) )' % MRF
    comp = w.s([mh, acn], 'cncfmpt1f', '( %s -> ( u e. RR |-> ( %s ` %s ) ) e. ( RR -cn-> CC ) )' % (A, G, AFF))
    gv = fvmd(w, Au, 's', 'CC', '( %s ` s )' % MRF, AFF, cu.mem(AFF, 'CC'), a1(w, Au, 'fvex', '%s e. _V' % MRU('u')))
    me = dst(w, A, [gv], 'mpteq2dva', '( u e. RR |-> ( %s ` %s ) ) = ( u e. RR |-> %s )' % (G, AFF, MRU('u')))
    mcn = dst(w, A, [me, comp], 'eqeltrrd', '( u e. RR |-> %s ) e. ( RR -cn-> CC )' % MRU('u'))
    cn.memo[MRU('u')] = mcn
    cn(MA('u'))
    return fin(w)


def a7setup(w, A):
    """parts, base closure and the A7C pieces for an antecedent A containing A7C"""
    P, c, F = setupx(w, A)
    G = a7parts(w, A, P, c)
    G.update(F)
    return P, c, G


def ld2vlcv():
    w = W('ld2vlcv', 'Lean ` integrable_Ghat_line_half ` : the truncated line integrals of the contour integrand on ` Re w = 1/2 - Re S ` converge to ` VL ` (~ z6vlcvg with the strip ~ dshgrsd and the majorant ~ dshgrmaj at ` R = 1 ` ; DSH\'s ~ dshvlc gives only the closure).')
    A = ante('ld2vlcv'); P, c, F = a7setup(w, A)
    gcn = grcn1(w, A, F)
    Au = '( %s /\\ u e. RR )' % A
    ur = w.s([], 'simpr', '( %s -> u e. RR )' % Au)
    Fu = dict(F); Fu = {k: (lift(w, v, Au) if isinstance(v, str) else v) for k, v in F.items()}
    zin, zc, rez, imz = hlu_ds(w, Au, Fu, 'u', ur)
    Z = HLU('u')
    alz = dst(w, A, [zin], 'ralrimiva', 'A. u e. RR %s e. %s' % (Z, Z6.DS))
    # the majorant on the line
    ais = c.mem('( abs ` %s )' % IS, 'RR')
    y5r = dst(w, A, [ais, w.s([], '1red', '( %s -> 1 e. RR )' % A)], 'readdcld', '%s e. RR' % Y5)
    c.leaf('( abs ` %s )' % IS, 'RR', ais); c.leaf('( abs ` %s )' % IS, 'ge0', c.ge0('( abs ` %s )' % IS))
    y5rp = dst(w, A, [y5r, linarith(w, A, [c.ge0('( abs ` %s )' % IS)], '0 < %s' % Y5, closure=c)], 'elrpd', '%s e. RR+' % Y5)
    OM = '( # ` { p e. Prime | p || N } )'
    omn = ap(w, A, 'hashcl', [ap(w, A, 'prmdvdsfi', [F['nN']], '{ p e. Prime | p || N } e. Fin')], '%s e. NN0' % OM)
    c.leaf(OM, 'NN0', omn); c.leaf('N', 'NN', F['nN'])
    m5r = c.mem(M5, 'RR')
    C2 = '( %s /\\ %s <_ ( abs ` u ) )' % (Au, Y5)
    gmj = ap(w, C2, 'dshgrmaj', [lift(w, F['a7r'], C2)], SM1)
    zc2 = lift(w, zc, C2); imz2 = lift(w, imz, C2)
    aim = dst(w, C2, [imz2], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` u )' % Z)
    y5le = dst(w, C2, [w.s([], 'simpr', '( %s -> %s <_ ( abs ` u ) )' % (C2, Y5)), aim], 'breqtrrd', '%s <_ ( abs ` ( Im ` %s ) )' % (Y5, Z))
    rez2 = lift(w, rez, C2)
    hl3 = linarith(w, C2, [lift(w, F['lo'], C2)], '%s <_ 3' % HL, closure=Closure(w, C2, {HL: ('RR', lift(w, F['hlr'], C2)), RS: ('RR', lift(w, c.mem(RS, 'RR'), C2))}))
    le1 = dst(w, C2, [lift(w, F['hlr'], C2), eqc(w, C2, rez2)], 'eqled', '%s <_ ( Re ` %s )' % (HL, Z))
    le3 = dst(w, C2, [rez2, hl3], 'eqbrtrd', '( Re ` %s ) <_ 3' % Z)
    insm, newm = inst_forall(w, C2, gmj, 'z', SM1[len('A. z e. CC '):], Z, zc2)
    bnd = dst(w, C2, [J(w, C2, J(w, C2, le1, le3), y5le), insm], 'mpd', split_imp(newm)[1])
    E4 = lambda x: '( 2 ^c -u ( %s / 4 ) )' % x
    q3 = dst(w, C2, [dst(w, C2, [dst(w, C2, [aim], 'oveq1d', '( ( abs ` ( Im ` %s ) ) / 4 ) = ( ( abs ` u ) / 4 )' % Z)], 'negeqd', '-u ( ( abs ` ( Im ` %s ) ) / 4 ) = -u ( ( abs ` u ) / 4 )' % Z)], 'oveq2d',
             '%s = %s' % (E4('( abs ` ( Im ` %s ) )' % Z), E4('( abs ` u )')))
    q4 = dst(w, C2, [q3], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (M5, E4('( abs ` ( Im ` %s ) )' % Z), M5, E4('( abs ` u )')))
    bnd2 = dst(w, C2, [bnd, q4], 'breqtrd', '( abs ` ( %s ` %s ) ) <_ ( %s x. %s )' % (GRH, Z, M5, E4('( abs ` u )')))
    MJ = '( %s <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) )' % (Y5, GRH, Z, M5, E4('( abs ` u )'))
    alm = dst(w, A, [dst(w, Au, [bnd2], 'ex', MJ)], 'ralrimiva', 'A. u e. RR %s' % MJ)
    hyp = J(w, A, J(w, A, F['hlr'], J(w, A, gcn, alz)), J(w, A, J(w, A, m5r, y5rp), alm))
    vc = ap(w, A, 'z6vlcvg', [hyp], subst(concl('z6vlcvg'), {'C': HL, 'G': GRH, 'M': M5, 'Y': Y5}))
    dst(w, A, [vc], 'simpld', '%s ~~>r %s' % (VLFH, VLH))
    return fin(w)


def ld2licl():
    w = W('ld2licl', 'The truncated line integral ` LIH ( H ) ` of the contour integrand is ` i S. ( -H , H ) G ( HL + i u ) du ` with an integrable integrand (~ z6lvert with ~ dshgrcn and the strip ~ dshgrsd through ~ z6segd ).')
    A = ante('ld2licl'); P, c, F = a7setup(w, A)
    hrp = P['H e. RR+']
    gcn = grcn1(w, A, F)
    Au = '( %s /\\ u e. RR )' % A
    ur = w.s([], 'simpr', '( %s -> u e. RR )' % Au)
    Fu = {k: (lift(w, v, Au) if isinstance(v, str) else v) for k, v in F.items()}
    zin, zc, rez, imz = hlu_ds(w, Au, Fu, 'u', ur)
    alz = dst(w, A, [zin], 'ralrimiva', 'A. u e. RR %s e. %s' % (HLU('u'), Z6.DS))
    sg = ap(w, A, 'z6segd', [J(w, A, F['hlr'], hrp), alz], '( ( %s + ( _i x. -u H ) ) cseg ( %s + ( _i x. H ) ) ) C_ %s' % (HL, HL, Z6.DS))
    ap(w, A, 'z6lvert', [J(w, A, F['hlr'], hrp), J(w, A, gcn, sg)], concl('ld2licl'))
    return fin(w)


def ptwfacts(w, A, c, F, U, ur):
    """under A (containing HP6) at a real U (step ur): the point W = HLU(U) in DS, the value of GRHV(U), the closures of the four factors
    and the identities Re W = HL, Im W = U, Re ( S + W ) = 1/2, Im ( S + W ) = Im S + U; returns a dict"""
    R = {}
    zin, zc, rez, imz = hlu_ds(w, A, F, U, ur)
    Wp = HLU(U)
    R.update(zin=zin, zc=zc, rez=rez, imz=imz)
    body_ = GRH.split(' |-> ', 1)[1][:-2]
    assert GRH == '( w e. %s |-> %s )' % (Z6.DS, body_)
    cg, val = w.congr(body_, {'w': Wp}, 'w = %s' % Wp, {'w': w.s([], 'id', '( w = %s -> w = %s )' % (Wp, Wp))})
    sub = w.s([cg], 'adantl', '( ( %s /\\ w = %s ) -> %s = %s )' % (A, Wp, body_, val))
    R['val'] = w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (A, GRH, GRH)), sub, zin, a1(w, A, 'ovex', '%s e. _V' % val)], 'fvmptd', '( %s -> %s = %s )' % (A, GRHV(U), val))
    R['body'] = val
    Z = '( S + %s )' % Wp
    c.leaf(Wp, 'CC', zc)
    zcc = c.mem(Z, 'CC')
    wdg = ap(w, A, 'elinel1', [zin], '%s e. %s' % (Wp, DG))
    R['gc'] = ap(w, A, 'gamcl', [wdg], '( _G ` %s ) e. CC' % Wp)
    c.leaf('( _G ` %s )' % Wp, 'CC', R['gc'])
    R['yc'] = dst(w, A, [c.mem(YP, 'CC'), zc], 'cxpcld', '( %s ^c %s ) e. CC' % (YP, Wp))
    c.leaf('( %s ^c %s )' % (YP, Wp), 'CC', R['yc'])
    # Re ( S + W ) = 1/2, Im ( S + W ) = Im S + U
    rez2 = eqt(w, A, dst(w, A, [F['sc'], zc], 'readdd', '( Re ` %s ) = ( %s + ( Re ` %s ) )' % (Z, RS, Wp)),
               eqt(w, A, dst(w, A, [rez], 'oveq2d', '( %s + ( Re ` %s ) ) = ( %s + %s )' % (RS, Wp, RS, HL)), ringeq(w, A, '( %s + %s )' % (RS, HL), '( 1 / 2 )', c)))
    imz2 = eqt(w, A, dst(w, A, [F['sc'], zc], 'imaddd', '( Im ` %s ) = ( %s + ( Im ` %s ) )' % (Z, IS, Wp)), dst(w, A, [imz], 'oveq2d', '( %s + ( Im ` %s ) ) = ( %s + %s )' % (IS, Wp, IS, U)))
    R.update(rez2=rez2, imz2=imz2, zcc=zcc)
    # ( S + W ) e. HPZ and E ( S + W ) e. CC
    rp = dst(w, A, [c.mem('( Re ` %s )' % Z, 'RR'), dst(w, A, [w.s([num.fact(w, '( 1 / 2 )', 'gt0')], 'a1i', '( %s -> 0 < ( 1 / 2 ) )' % A), rez2], 'breqtrrd', '0 < ( Re ` %s )' % Z)], 'elrpd', '( Re ` %s ) e. RR+' % Z)
    rio = dst(w, A, [rp, a1(w, A, 'ioorp', '( 0 (,) +oo ) = RR+')], 'eleqtrrd', '( Re ` %s ) e. ( 0 (,) +oo )' % Z)
    ffn = dst(w, A, [a1(w, A, 'ref', 'Re : CC --> RR')], 'ffnd', 'Re Fn CC')
    hp = dst(w, A, [J(w, A, zcc, rio), ap(w, A, 'elpreima', [ffn], '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( 0 (,) +oo ) ) )' % (Z, HPZ, Z, Z))], 'mpbird', '%s e. %s' % (Z, HPZ))
    ef = ap(w, A, 'cncff', [F['ecn']], 'E : %s --> CC' % HPZ)
    R['ec'] = dst(w, A, [ef, hp], 'ffvelcdmd', '( E ` %s ) e. CC' % Z)
    c.leaf('( E ` %s )' % Z, 'CC', R['ec'])
    # ( S + W ) =/= 1
    A1 = '( %s /\\ %s = 1 )' % (A, Z)
    r1 = eqt(w, A1, eqt(w, A1, eqc(w, A1, lift(w, rez2, A1)), dst(w, A1, [w.s([], 'simpr', '( %s -> %s = 1 )' % (A1, Z))], 'fveq2d', '( Re ` %s ) = ( Re ` 1 )' % Z)), a1(w, A1, 're1', '( Re ` 1 ) = 1'))
    ne = w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], 'halflt1', '( 1 / 2 ) < 1'), w.inst('ltne')], 'mp2an', '1 =/= ( 1 / 2 )')
    nz1 = dst(w, A, [r1, dst(w, A1, [w.s([w.s([ne], 'necomi', '( 1 / 2 ) =/= 1')], 'a1i', '( %s -> ( 1 / 2 ) =/= 1 )' % A1)], 'neneqd', '-. ( 1 / 2 ) = 1')], 'pm2.65da', '-. %s = 1' % Z)
    zne = dst(w, A, [nz1], 'neqned', '%s =/= 1' % Z)
    R['dne'] = dst(w, A, [zcc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A), zne], 'subne0d', '( %s - 1 ) =/= 0' % Z)
    c.leaf('( %s - 1 )' % Z, 'ne0', R['dne'])
    QE = '( ( E ` %s ) / ( %s - 1 ) )' % (Z, Z)
    R['qc'] = c.mem(QE, 'CC')
    R['mc'] = ap(w, A, 'z5mrcl', [J(w, A, hab0(w, A, c, F['dr'], F['d1']), a1(w, A, '1nn', '1 e. NN')), J(w, A, F['cf'], zcc)], '%s e. CC' % MRU(U))
    c.leaf(MRU(U), 'CC', R['mc'])
    R['Z'] = Z; R['W'] = Wp; R['QE'] = QE
    return R


def ld2ptw():
    w = W('ld2ptw', 'Lean ` norm_ectrInt_half_le ` (Lemma 3.6, pointwise): on the half line, ` abs ( Gamma ( w ) Y ^ w L ( S + w ) M ( S + w ) ) <_ K e ^ -( abs u / 2 ) abs M ( S + w ) ` (~ ld2gam , ~ abscxp , ~ ld1lhalf , ~ ld2wsq ; ` K = 8 12000 600000 CTau D ^ ( 201 / 800 ) log D Y ^ ( 1/2 - sigma ) ` ).')
    A = ante('ld2ptw'); P, c, F = a7setup(w, A)
    ur = P['U e. RR']; tr = P['T e. RR']; t39 = P['( ; 3 9 / ; 5 0 ) <_ T']; tre = P['T <_ ( Re ` S )']; hdn = P[HDN]
    c.leaf('U', 'RR', ur)
    kcr = kcfacts(w, A, c, F, tr)
    R = ptwfacts(w, A, c, F, 'U', ur)
    Wp, Z, QE = R['W'], R['Z'], R['QE']
    AU = '( abs ` U )'; EU = '( exp ` -u %s )' % AU; U1 = '( 1 + %s )' % AU
    c.leaf(AU, 'RR', c.mem(AU, 'RR')); c.leaf(AU, 'ge0', c.ge0(AU))
    c.leaf(EU, 'RR+', dst(w, A, [c.mem('-u %s' % AU, 'RR')], 'rpefcld', '%s e. RR+' % EU))
    # (1) Gamma
    lo = linarith(w, A, [F['re1']], '-u ( 1 / 2 ) <_ %s' % HL, closure=c)
    hi = linarith(w, A, [F['lo']], '%s <_ -u ( 7 / ; 2 5 )' % HL, closure=c)
    lo2 = dst(w, A, [lo, eqc(w, A, R['rez'])], 'breqtrd', '-u ( 1 / 2 ) <_ ( Re ` %s )' % Wp)
    hi2 = dst(w, A, [R['rez'], hi], 'eqbrtrd', '( Re ` %s ) <_ -u ( 7 / ; 2 5 )' % Wp)
    gm = ap(w, A, 'ld2gam', [J(w, A, R['zc'], J(w, A, lo2, hi2))], '( abs ` ( _G ` %s ) ) <_ ( %s x. ( exp ` -u ( abs ` ( Im ` %s ) ) ) )' % (Wp, GAMC, Wp))
    gm2 = dst(w, A, [gm, dst(w, A, [dst(w, A, [dst(w, A, [dst(w, A, [R['imz']], 'fveq2d', '( abs ` ( Im ` %s ) ) = %s' % (Wp, AU))], 'negeqd', '-u ( abs ` ( Im ` %s ) ) = -u %s' % (Wp, AU))], 'fveq2d', '( exp ` -u ( abs ` ( Im ` %s ) ) ) = %s' % (Wp, EU))], 'oveq2d',
                                  '( %s x. ( exp ` -u ( abs ` ( Im ` %s ) ) ) ) = ( %s x. %s )' % (GAMC, Wp, GAMC, EU))], 'breqtrd', '( abs ` ( _G ` %s ) ) <_ ( %s x. %s )' % (Wp, GAMC, EU))
    AG = '( abs ` ( _G ` %s ) )' % Wp
    # (2) Y ^ w
    AY = '( abs ` ( %s ^c %s ) )' % (YP, Wp)
    ay = eqt(w, A, ap(w, A, 'abscxp', [c.mem(YP, 'RR+'), R['zc']], '%s = ( %s ^c ( Re ` %s ) )' % (AY, YP, Wp)), dst(w, A, [R['rez']], 'oveq2d', '( %s ^c ( Re ` %s ) ) = ( %s ^c %s )' % (YP, Wp, YP, HL)))
    hlt = linarith(w, A, [tre], '%s <_ ( ( 1 / 2 ) - T )' % HL, closure=c)
    y1 = dst(w, A, [c.mem(YP, 'RR'), ltle(w, A, c, F['y1']), c.mem(HL, 'RR'), c.mem('( ( 1 / 2 ) - T )', 'RR'), hlt], 'cxplead', '( %s ^c %s ) <_ %s' % (YP, HL, YPT))
    ay2 = dst(w, A, [ay, y1], 'eqbrtrd', '%s <_ %s' % (AY, YPT))
    # (3) the L-function bound at Z = S + W
    hz2 = J(w, A, F['dr'], F['d1'], linarith(w, A, [F['dl']], '2 <_ %s' % L, closure=c))
    lh = ap(w, A, 'ld1lhalf', [J(w, A, hz2, J(w, A, F['nN'], hdn)), J(w, A, J(w, A, F['sc'], R['zcc']), J(w, A, R['rez2'], F['cvx']))],
            subst(concl('ld1lhalf'), {'Z': Z}))
    imd = eqt(w, A, dst(w, A, [R['imz2']], 'oveq1d', '( ( Im ` %s ) - %s ) = ( ( %s + U ) - %s )' % (Z, IS, IS, IS)), dst(w, A, [c.mem(IS, 'CC'), c.mem('U', 'CC')], 'pncan2d', '( ( %s + U ) - %s ) = U' % (IS, IS)))
    BL = '( %s x. ( %s x. ( ( 1 + ( abs ` ( ( Im ` %s ) - %s ) ) ) ^ 2 ) ) )' % (KHALF, L, Z, IS)
    BL2 = '( %s x. ( %s x. ( %s ^ 2 ) ) )' % (KHALF, L, U1)
    r0, t0 = w.rewrite(BL, {'( ( Im ` %s ) - %s )' % (Z, IS): ('U', imd)}, A)
    assert t0 == BL2, (t0, BL2)
    AQ = '( abs ` %s )' % QE
    lh2 = dst(w, A, [lh, r0], 'breqtrd', '%s <_ %s' % (AQ, BL2))
    # the product
    AM = MA('U')
    for e_ in (AG, AY, AQ, AM):
        c.leaf(e_, 'RR', c.mem(e_, 'RR')); c.leaf(e_, 'ge0', c.ge0(e_))
    c.leaf(U1, 'RR', c.mem(U1, 'RR')); c.leaf(U1, 'ge0', c.ge0(U1))
    E8 = '( D ^c ( 1 / ; ; 8 0 0 ) )'
    p1 = dst(w, A, [c.mem('( _G ` %s )' % Wp, 'CC'), c.mem('( %s ^c %s )' % (YP, Wp), 'CC')], 'absmuld', '( abs ` ( ( _G ` %s ) x. ( %s ^c %s ) ) ) = ( %s x. %s )' % (Wp, YP, Wp, AG, AY))
    p2 = dst(w, A, [c.mem(QE, 'CC'), c.mem(MRU('U'), 'CC')], 'absmuld', '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (QE, MRU('U'), AQ, AM))
    G2 = '( ( _G ` %s ) x. ( %s ^c %s ) )' % (Wp, YP, Wp); Q2 = '( %s x. %s )' % (QE, MRU('U'))
    assert R['body'] == '( %s x. %s )' % (G2, Q2), R['body']
    p3 = eqt(w, A, dst(w, A, [c.mem(G2, 'CC'), c.mem(Q2, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (R['body'], G2, Q2)), dst(w, A, [p1, p2], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (G2, Q2, AG, AY, AQ, AM)))
    av = eqt(w, A, dst(w, A, [R['val']], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (GRHV('U'), R['body'])), p3)
    GE = '( %s x. %s )' % (GAMC, EU)
    s1 = dst(w, A, [c.mem(AG, 'RR'), c.mem(GE, 'RR'), c.mem(AY, 'RR'), c.mem(YPT, 'RR'), c.ge0(AG), c.ge0(AY), gm2, ay2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (AG, AY, GE, YPT))
    s2 = dst(w, A, [c.mem(AQ, 'RR'), c.mem(BL2, 'RR'), c.mem(AM, 'RR'), c.ge0(AM), lh2], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (AQ, AM, BL2, AM))
    L1 = '( %s x. %s )' % (AG, AY); L2_ = '( %s x. %s )' % (AQ, AM); R1 = '( %s x. %s )' % (GE, YPT); R2 = '( %s x. %s )' % (BL2, AM)
    s3 = dst(w, A, [c.mem(L1, 'RR'), c.mem(R1, 'RR'), c.mem(L2_, 'RR'), c.mem(R2, 'RR'), c.ge0(L1), c.ge0(L2_), s1, s2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (L1, L2_, R1, R2))
    Q = '( ( ( ( %s x. %s ) x. %s ) x. %s ) x. %s )' % (GAMC, KHALF, L, YPT, AM)
    c.leaf(E8, 'RR+', c.mem(E8, 'RR+'))
    rg = ringeq(w, A, '( %s x. %s )' % (R1, R2), '( %s x. ( ( %s ^ 2 ) x. %s ) )' % (Q, U1, EU), c)
    ws = ap(w, A, 'ld2wsq', [J(w, A, c.mem(AU, 'RR'), c.ge0(AU))], '( ( %s ^ 2 ) x. %s ) <_ ( 8 x. %s )' % (U1, EU, WT('U')))
    c.leaf(WT('U'), 'RR+', dst(w, A, [c.mem('-u ( ( 1 / 2 ) x. %s )' % AU, 'RR')], 'rpefcld', '%s e. RR+' % WT('U')))
    s4 = dst(w, A, [c.mem('( ( %s ^ 2 ) x. %s )' % (U1, EU), 'RR'), c.mem('( 8 x. %s )' % WT('U'), 'RR'), c.mem(Q, 'RR'), c.ge0(Q), ws], 'lemul2ad', '( %s x. ( ( %s ^ 2 ) x. %s ) ) <_ ( %s x. ( 8 x. %s ) )' % (Q, U1, EU, Q, WT('U')))
    # the constant: 12000 x. 8 x. 600000 = 576 x. 10 ^ 8
    e8 = pow10_8(w)
    LIT = '; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0'
    rk, KCL = w.rewrite(KC, {P8: (LIT, w.s([e8], 'a1i', '( %s -> %s = %s )' % (A, P8, LIT)))}, A)
    rg2 = ringeq(w, A, '( %s x. ( 8 x. %s ) )' % (Q, WT('U')), '( %s x. ( %s x. %s ) )' % (KCL, WT('U'), AM), c)
    rk2 = dst(w, A, [rk], 'oveq1d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (KC, WT('U'), AM, KCL, WT('U'), AM))
    fe = eqt(w, A, rg2, eqc(w, A, rk2))
    t1 = dst(w, A, [s3, rg], 'breqtrd', '( %s x. %s ) <_ ( %s x. ( ( %s ^ 2 ) x. %s ) )' % (L1, L2_, Q, U1, EU))
    t2 = dst(w, A, [s4, fe], 'breqtrd', '( %s x. ( ( %s ^ 2 ) x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (Q, U1, EU, KC, WT('U'), AM))
    FIN = '( %s x. ( %s x. %s ) )' % (KC, WT('U'), AM)
    t3 = dst(w, A, [c.mem('( %s x. %s )' % (L1, L2_), 'RR'), c.mem('( %s x. ( ( %s ^ 2 ) x. %s ) )' % (Q, U1, EU), 'RR'), c.mem(FIN, 'RR'), t1, t2], 'letrd', '( %s x. %s ) <_ %s' % (L1, L2_, FIN))
    dst(w, A, [av, t3], 'eqbrtrd', '( abs ` %s ) <_ %s' % (GRHV('U'), FIN))
    return fin(w)


def cnwm(w, A, c, F, tr):
    """( A -> ( u e. RR |-> ( WT x. MA ) ) e. cn ), ( ... ( WT x. MA ^ 2 ) ... ), ( ... WT ... ) under A containing HP6"""
    wt = ap(w, A, 'ld2wtcn', [c.mem('( 1 / 2 )', 'RR')], '( u e. RR |-> %s ) e. ( RR -cn-> CC )' % WT('u'))
    ma = ap(w, A, 'ld2macn', [J(w, A, J(w, A, F['dr'], F['d1']), J(w, A, F['cf'], F['sc']))], '( u e. RR |-> %s ) e. ( RR -cn-> CC )' % MA('u'))
    wm = w.s([wt, ma], 'mulcncf', '( %s -> ( u e. RR |-> ( %s x. %s ) ) e. ( RR -cn-> CC ) )' % (A, WT('u'), MA('u')))
    Au = '( %s /\\ u e. RR )' % A
    ur = w.s([], 'simpr', '( %s -> u e. RR )' % Au)
    cu = Closure(w, Au, {'u': ('RR', ur)})
    _, Ru = ptwfacts_light(w, Au, cu, F, ur)
    sq = dst(w, Au, [Ru], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (MA('u'), MA('u'), MA('u')))
    m2 = w.s([ma, ma], 'mulcncf', '( %s -> ( u e. RR |-> ( %s x. %s ) ) e. ( RR -cn-> CC ) )' % (A, MA('u'), MA('u')))
    me = dst(w, A, [sq], 'mpteq2dva', '( u e. RR |-> ( %s ^ 2 ) ) = ( u e. RR |-> ( %s x. %s ) )' % (MA('u'), MA('u'), MA('u')))
    m2b = dst(w, A, [me, m2], 'eqeltrd', '( u e. RR |-> ( %s ^ 2 ) ) e. ( RR -cn-> CC )' % MA('u'))
    wm2 = w.s([wt, m2b], 'mulcncf', '( %s -> ( u e. RR |-> ( %s x. ( %s ^ 2 ) ) ) e. ( RR -cn-> CC ) )' % (A, WT('u'), MA('u')))
    return wt, wm, wm2


def ptwfacts_light(w, Au, cu, F, ur):
    """( Au -> MA(u) e. CC ) under Au = ( A /\\ u e. RR ) (F: the A7C pieces under A)"""
    A = Au[2:].rsplit(' /\\ u e. RR )', 1)[0]
    D2 = '( 2 x. D )'
    dr = lift(w, F['dr'], Au); d1 = lift(w, F['d1'], Au); sc = lift(w, F['sc'], Au)
    c0 = Closure(w, Au, {'D': [('RR', dr), ('gt1', d1)], 'S': ('CC', sc), 'u': ('RR', ur), '_i': ('CC', a1(w, Au, 'ax-icn', '_i e. CC'))})
    c0.leaf(RS, 'RR', dst(w, Au, [sc], 'recld', '%s e. RR' % RS))
    h0 = hab0(w, Au, c0, dr, d1)
    Z = '( S + %s )' % HLU('u')
    mc = ap(w, Au, 'z5mrcl', [J(w, Au, h0, a1(w, Au, '1nn', '1 e. NN')), J(w, Au, lift(w, F['cf'], Au), c0.mem(Z, 'CC'))], '%s e. CC' % MRU('u'))
    mar = dst(w, Au, [mc], 'abscld', '%s e. RR' % MA('u'))
    return mar, dst(w, Au, [mar], 'recnd', '%s e. CC' % MA('u'))


def ld2li():
    w = W('ld2li', 'Lean ` h2 ` of ` sq_norm_EctrHalf_le ` on a truncation: ` abs LIH ( H ) <_ K S. ( -H , H ) e ^ -( abs u / 2 ) abs M du ` (~ ld2licl , ~ itgabs , ~ itgle with ~ ld2ptw , ~ itgmulc2 ).')
    A = ante('ld2li'); P, c, F = a7setup(w, A)
    tr = P['T e. RR']; hrp = P['H e. RR+']
    c.leaf('H', 'RR+', hrp)
    kcr = kcfacts(w, A, c, F, tr)
    hp6 = P[HP6]; a7c = P[A7C]
    lc = ap(w, A, 'ld2licl', [J(w, A, a7c, hrp)], concl('ld2licl'))
    ibl = dst(w, A, [lc], 'simpld', '( u e. %s |-> %s ) e. L^1' % (IOH('H'), GRHV('u')))
    val = dst(w, A, [lc], 'simprd', '%s = ( _i x. %s )' % (LIH('H'), ITG(IOH('H'), GRHV('u'), 'u')))
    I = IOH('H')
    Au = '( %s /\\ u e. %s )' % (A, I)
    ur = ap(w, Au, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, I))], 'u e. RR')
    gv = a1(w, Au, 'fvex', '%s e. _V' % GRHV('u'))
    itc = w.s([gv, ibl], 'itgcl', '( %s -> %s e. CC )' % (A, ITG(I, GRHV('u'), 'u')))
    a1_ = eqt(w, A, dst(w, A, [val], 'fveq2d', '( abs ` %s ) = ( abs ` ( _i x. %s ) )' % (LIH('H'), ITG(I, GRHV('u'), 'u'))),
              eqt(w, A, dst(w, A, [a1(w, A, 'ax-icn', '_i e. CC'), itc], 'absmuld', '( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (ITG(I, GRHV('u'), 'u'), ITG(I, GRHV('u'), 'u'))),
                  eqt(w, A, dst(w, A, [a1(w, A, 'absi', '( abs ` _i ) = 1')], 'oveq1d', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) )' % (ITG(I, GRHV('u'), 'u'), ITG(I, GRHV('u'), 'u'))),
                      dst(w, A, [dst(w, A, [dst(w, A, [itc], 'abscld', '( abs ` %s ) e. RR' % ITG(I, GRHV('u'), 'u'))], 'recnd', '( abs ` %s ) e. CC' % ITG(I, GRHV('u'), 'u'))], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (ITG(I, GRHV('u'), 'u'), ITG(I, GRHV('u'), 'u'))))))
    ia = w.s([gv, ibl], 'itgabs', '( %s -> ( abs ` %s ) <_ %s )' % (A, ITG(I, GRHV('u'), 'u'), ITG(I, '( abs ` %s )' % GRHV('u'), 'u')))
    iab = w.s([gv, ibl], 'iblabs', '( %s -> ( u e. %s |-> ( abs ` %s ) ) e. L^1 )' % (A, I, GRHV('u')))
    # the pointwise bound and the majorant's integrability
    pt = ap(w, Au, 'ld2ptw', [J(w, Au, lift(w, hp6, Au), ur)], subst(concl('ld2ptw'), {'U': 'u'}))
    wt, wm, wm2 = cnwm(w, A, c, F, tr)
    nh = c.mem('-u H', 'RR'); hr = c.mem('H', 'RR')
    WM = '( %s x. %s )' % (WT('u'), MA('u'))
    ibwm = w.s([J(w, A, nh, hr), wm], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, WM))
    Fu = {k: (lift(w, v, Au) if isinstance(v, str) else v) for k, v in F.items()}
    cu = liftcl(w, None, Au, basefacts(F)); cu.leaf('u', 'RR', ur); cu.leaf(IS, 'RR', dst(w, Au, [Fu['sc']], 'imcld', '%s e. RR' % IS))
    cu.leaf('_i', 'CC', a1(w, Au, 'ax-icn', '_i e. CC'))
    mar, mac = ptwfacts_light(w, Au, cu, F, ur)
    cu.leaf(MA('u'), 'RR', mar); cu.leaf(MA('u'), 'CC', mac)
    cu.leaf(WT('u'), 'RR+', dst(w, Au, [cu.mem('-u ( ( 1 / 2 ) x. ( abs ` u ) )', 'RR')], 'rpefcld', '%s e. RR+' % WT('u')))
    wmc = cu.mem(WM, 'CC')
    kcc = c.mem(KC, 'CC')
    ibk = w.s([kcc, wmc, ibwm], 'iblmulc2', '( %s -> ( u e. %s |-> ( %s x. %s ) ) e. L^1 )' % (A, I, KC, WM))
    # abs GRHV real: from the L^1 membership? use the value: GRHV e. CC via ld2licl's integrand? simpler: abs of a set is real when the set is complex -- take it from ld2ptw's chain: abs GRHV <_ ... does not give RR.  Use GRHV(u) e. CC from the body closure:
    Ru = ptwfacts(w, Au, cu, Fu, 'u', ur)
    gcc = dst(w, Au, [Ru['val'], cu.mem(Ru['body'], 'CC')], 'eqeltrd', '%s e. CC' % GRHV('u'))
    agr = dst(w, Au, [gcc], 'abscld', '( abs ` %s ) e. RR' % GRHV('u'))
    kr = dst(w, Au, [lift(w, c.mem(KC, 'RR'), Au), cu.mem(WM, 'RR')], 'remulcld', '( %s x. %s ) e. RR' % (KC, WM))
    il = w.s([iab, ibk, agr, kr, pt], 'itgle', '( %s -> %s <_ %s )' % (A, ITG(I, '( abs ` %s )' % GRHV('u'), 'u'), ITG(I, '( %s x. %s )' % (KC, WM), 'u')))
    mc = w.s([kcc, wmc, ibwm], 'itgmulc2', '( %s -> ( %s x. %s ) = %s )' % (A, KC, ITG(I, WM, 'u'), ITG(I, '( %s x. %s )' % (KC, WM), 'u')))
    aI = dst(w, A, [itc], 'abscld', '( abs ` %s ) e. RR' % ITG(I, GRHV('u'), 'u'))
    i1 = dst(w, A, [agr, iab], 'itgrecl', '%s e. RR' % ITG(I, '( abs ` %s )' % GRHV('u'), 'u'))
    i2 = dst(w, A, [kr, ibk], 'itgrecl', '%s e. RR' % ITG(I, '( %s x. %s )' % (KC, WM), 'u'))
    ch = dst(w, A, [aI, i1, i2, ia, il], 'letrd', '( abs ` %s ) <_ %s' % (ITG(I, GRHV('u'), 'u'), ITG(I, '( %s x. %s )' % (KC, WM), 'u')))
    ch2 = dst(w, A, [ch, eqc(w, A, mc)], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (ITG(I, GRHV('u'), 'u'), KC, ITG(I, WM, 'u')))
    dst(w, A, [a1_, ch2], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. %s )' % (LIH('H'), KC, ITG(I, WM, 'u')))
    return fin(w)


def ld2sq1():
    w = W('ld2sq1', 'Lean ` sq_norm_EctrHalf_le ` on a truncation: ` ( abs LIH ( H ) ) ^ 2 <_ K ^ 2 4 S. ( -H , H ) e ^ -( abs u / 2 ) ( abs M ) ^ 2 du ` (~ ld2li , Cauchy-Schwarz ~ ld2cs at the constants ` S. W Z ` and ` 4 ` with ` S. W <_ 4 ` from ~ ld2wint ).')
    A = ante('ld2sq1'); P, c, F = a7setup(w, A)
    tr = P['T e. RR']; hrp = P['H e. RR+']
    c.leaf('H', 'RR+', hrp)
    kcr = kcfacts(w, A, c, F, tr)
    hp6 = P[HP6]
    I = IOH('H')
    li = ap(w, A, 'ld2li', [w.s([], 'id', '( %s -> %s )' % (A, A))], concl('ld2li'))
    WM = lambda v: '( %s x. %s )' % (WT(v), MA(v)); WM2 = lambda v: '( %s x. ( %s ^ 2 ) )' % (WT(v), MA(v))
    I1 = ITG(I, WM('u'), 'u'); I0 = ITG(I, WT('u'), 'u'); I2 = ITG(I, WM2('u'), 'u')
    wt, wm, wm2 = cnwm(w, A, c, F, tr)
    nh = c.mem('-u H', 'RR'); hr = c.mem('H', 'RR')
    h1 = J(w, A, nh, hr)
    # the hypotheses of ld2cs at the integration variable v
    Av = '( %s /\\ v e. %s )' % (A, I)
    vr = ap(w, Av, 'elioore', [w.s([], 'simpr', '( %s -> v e. %s )' % (Av, I))], 'v e. RR')
    cv = Closure(w, Av, {'v': ('RR', vr)})
    # MA(v) e. RR by z5mrcl at v
    D2 = '( 2 x. D )'
    dr = lift(w, F['dr'], Av); d1 = lift(w, F['d1'], Av); sc = lift(w, F['sc'], Av)
    c0 = Closure(w, Av, {'D': [('RR', dr), ('gt1', d1)], 'S': ('CC', sc), 'v': ('RR', vr), '_i': ('CC', a1(w, Av, 'ax-icn', '_i e. CC'))})
    c0.leaf(RS, 'RR', dst(w, Av, [sc], 'recld', '%s e. RR' % RS))
    h0 = hab0(w, Av, c0, dr, d1)
    Zv = '( S + %s )' % HLU('v')
    mc = ap(w, Av, 'z5mrcl', [J(w, Av, h0, a1(w, Av, '1nn', '1 e. NN')), J(w, Av, lift(w, F['cf'], Av), c0.mem(Zv, 'CC'))], '%s e. CC' % MRU('v'))
    mar = dst(w, Av, [mc], 'abscld', '%s e. RR' % MA('v')); ma0 = dst(w, Av, [mc], 'absge0d', '0 <_ %s' % MA('v'))
    cv.leaf(MA('v'), 'RR', mar); cv.leaf(MA('v'), 'ge0', ma0)
    wtv = dst(w, Av, [cv.mem('-u ( ( 1 / 2 ) x. ( abs ` v ) )', 'RR')], 'rpefcld', '%s e. RR+' % WT('v'))
    cv.leaf(WT('v'), 'RR+', wtv)
    h2 = J(w, Av, cv.mem(WT('v'), 'RR'), cv.ge0(WT('v'))); h3 = J(w, Av, mar, ma0)
    def rebind(step, eu, ev):
        cg, _ = w.congr(eu, {'u': 'v'}, 'u = v', {'u': w.s([], 'id', '( u = v -> u = v )')})
        me = w.s([cg], 'cbvmptv', '( u e. RR |-> %s ) = ( v e. RR |-> %s )' % (eu, ev))
        return dst(w, A, [w.s([me], 'a1i', '( %s -> ( u e. RR |-> %s ) = ( v e. RR |-> %s ) )' % (A, eu, ev)), step], 'eqeltrrd', '( v e. RR |-> %s ) e. ( RR -cn-> CC )' % ev)
    wtv = rebind(wt, WT('u'), WT('v')); wmv = rebind(wm, WM('u'), WM('v')); wm2v = rebind(wm2, WM2('u'), WM2('v'))
    ib0 = w.s([h1, wtv], 'ld2rribl', '( %s -> ( v e. %s |-> %s ) e. L^1 )' % (A, I, WT('v')))
    ib1 = w.s([h1, wmv], 'ld2rribl', '( %s -> ( v e. %s |-> %s ) e. L^1 )' % (A, I, WM('v')))
    ib2 = w.s([h1, wm2v], 'ld2rribl', '( %s -> ( v e. %s |-> %s ) e. L^1 )' % (A, I, WM2('v')))
    # I1 real
    ibu = w.s([h1, wm], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, WM('u')))
    Au = '( %s /\\ u e. %s )' % (A, I)
    ur = ap(w, Au, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, I))], 'u e. RR')
    cu = liftcl(w, None, Au, basefacts(F)); cu.leaf('u', 'RR', ur)
    maru, macu = ptwfacts_light(w, Au, cu, F, ur)
    cu.leaf(MA('u'), 'RR', maru); cu.leaf(MA('u'), 'CC', macu)
    cu.leaf(WT('u'), 'RR+', dst(w, Au, [cu.mem('-u ( ( 1 / 2 ) x. ( abs ` u ) )', 'RR')], 'rpefcld', '%s e. RR+' % WT('u')))
    i1r = dst(w, A, [cu.mem(WM('u'), 'RR'), ibu], 'itgrecl', '%s e. RR' % I1)
    h7 = J(w, A, i1r, c.mem('4', 'RR'))
    I1v = ITG(I, WM('v'), 'v'); I0v = ITG(I, WT('v'), 'v'); I2v = ITG(I, WM2('v'), 'v')
    cs = w.s([h1, h2, h3, ib0, ib1, ib2, h7], 'ld2cs', '( %s -> ( ( 2 x. ( %s x. 4 ) ) x. %s ) <_ ( ( ( %s ^ 2 ) x. %s ) + ( ( 4 ^ 2 ) x. %s ) ) )' % (A, I1, I1v, I1, I0v, I2v))
    # rename v -> u in the three integrals
    def rn(expr_v, expr_u):
        cg, _ = w.congr(expr_v, {'v': 'u'}, 'v = u', {'v': w.s([], 'id', '( v = u -> v = u )')})
        return w.s([cg], 'cbvitgv', '%s = %s' % (ITG(I, expr_v, 'v'), ITG(I, expr_u, 'u')))
    r1 = rn(WM('v'), WM('u')); r0 = rn(WT('v'), WT('u')); r2 = rn(WM2('v'), WM2('u'))
    e1 = dst(w, A, [w.s([r1], 'a1i', '( %s -> %s = %s )' % (A, I1v, I1))], 'oveq2d', '( ( 2 x. ( %s x. 4 ) ) x. %s ) = ( ( 2 x. ( %s x. 4 ) ) x. %s )' % (I1, I1v, I1, I1))
    e2 = dst(w, A, [dst(w, A, [w.s([r0], 'a1i', '( %s -> %s = %s )' % (A, I0v, I0))], 'oveq2d', '( ( %s ^ 2 ) x. %s ) = ( ( %s ^ 2 ) x. %s )' % (I1, I0v, I1, I0)),
                    dst(w, A, [w.s([r2], 'a1i', '( %s -> %s = %s )' % (A, I2v, I2))], 'oveq2d', '( ( 4 ^ 2 ) x. %s ) = ( ( 4 ^ 2 ) x. %s )' % (I2v, I2))], 'oveq12d',
             '( ( ( %s ^ 2 ) x. %s ) + ( ( 4 ^ 2 ) x. %s ) ) = ( ( ( %s ^ 2 ) x. %s ) + ( ( 4 ^ 2 ) x. %s ) )' % (I1, I0v, I2v, I1, I0, I2))
    cs3 = w.s([cs, e1, e2], '3brtr3d', '( %s -> ( ( 2 x. ( %s x. 4 ) ) x. %s ) <_ ( ( ( %s ^ 2 ) x. %s ) + ( ( 4 ^ 2 ) x. %s ) ) )' % (A, I1, I1, I1, I0, I2))
    # S. W <_ 4
    wi = ap(w, A, 'ld2wint', [c.mem('( 1 / 2 )', 'RR+'), hrp], '%s <_ ( 2 / ( 1 / 2 ) )' % I0)
    q1 = ap(w, A, 'divrec', [c.mem('2', 'CC'), c.mem('( 1 / 2 )', 'CC'), c.ne0('( 1 / 2 )')], '( 2 / ( 1 / 2 ) ) = ( 2 x. ( 1 / ( 1 / 2 ) ) )')
    q2 = dst(w, A, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A), c.mem('2', 'CC'), a1(w, A, 'ax-1ne0', '1 =/= 0'), c.ne0('2')], 'recdivd', '( 1 / ( 1 / 2 ) ) = ( 2 / 1 )')
    q3 = eqt(w, A, q2, dst(w, A, [c.mem('2', 'CC')], 'div1d', '( 2 / 1 ) = 2'))
    q4 = eqt(w, A, q1, eqt(w, A, dst(w, A, [q3], 'oveq2d', '( 2 x. ( 1 / ( 1 / 2 ) ) ) = ( 2 x. 2 )'), a1(w, A, '2t2e4', '( 2 x. 2 ) = 4')))
    wi2 = dst(w, A, [wi, q4], 'breqtrd', '%s <_ 4' % I0)
    ib0u = w.s([h1, wt], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, WT('u')))
    ib2u = w.s([h1, wm2], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, WM2('u')))
    i0r = dst(w, A, [cu.mem(WT('u'), 'RR'), ib0u], 'itgrecl', '%s e. RR' % I0)
    i2r = dst(w, A, [cu.mem(WM2('u'), 'RR'), ib2u], 'itgrecl', '%s e. RR' % I2)
    for e_, s_ in ((I1, i1r), (I0, i0r), (I2, i2r)):
        c.leaf(e_, 'RR', s_)
    sq0 = dst(w, A, [i1r], 'sqge0d', '0 <_ ( %s ^ 2 )' % I1)
    m1 = dst(w, A, [i0r, c.mem('4', 'RR'), c.mem('( %s ^ 2 )' % I1, 'RR'), sq0, wi2], 'lemul2ad', '( ( %s ^ 2 ) x. %s ) <_ ( ( %s ^ 2 ) x. 4 )' % (I1, I0, I1))
    P2 = '( %s ^ 2 )' % I1
    e16 = eqt(w, A, dst(w, A, [c.mem('4', 'CC')], 'sqvald', '( 4 ^ 2 ) = ( 4 x. 4 )'), a1(w, A, '4t4e16', '( 4 x. 4 ) = ; 1 6'))
    sqv = dst(w, A, [c.mem(I1, 'CC')], 'sqvald', '%s = ( %s x. %s )' % (P2, I1, I1))
    elhs = eqt(w, A, ringeq(w, A, '( ( 2 x. ( %s x. 4 ) ) x. %s )' % (I1, I1), '( 8 x. ( %s x. %s ) )' % (I1, I1), c),
               eqc(w, A, dst(w, A, [sqv], 'oveq2d', '( 8 x. %s ) = ( 8 x. ( %s x. %s ) )' % (P2, I1, I1))))
    erhs = dst(w, A, [dst(w, A, [e16], 'oveq1d', '( ( 4 ^ 2 ) x. %s ) = ( ; 1 6 x. %s )' % (I2, I2))], 'oveq2d', '( ( %s x. %s ) + ( ( 4 ^ 2 ) x. %s ) ) = ( ( %s x. %s ) + ( ; 1 6 x. %s ) )' % (P2, I0, I2, P2, I0, I2))
    cs4 = w.s([cs3, elhs, erhs], '3brtr3d', '( %s -> ( 8 x. %s ) <_ ( ( %s x. %s ) + ( ; 1 6 x. %s ) ) )' % (A, P2, P2, I0, I2))
    c.leaf(P2, 'RR', c.mem(P2, 'RR')); c.leaf(P2, 'ge0', sq0)
    csq = linarith(w, A, [cs4, m1], '%s <_ ( 4 x. %s )' % (P2, I2), closure=c)
    # ( abs LIH ) ^ 2 <_ ( KC I1 ) ^ 2 = KC ^ 2 I1 ^ 2 <_ KC ^ 2 ( 4 I2 )
    AL = '( abs ` %s )' % LIH('H')
    # abs LIH real: LIH e. CC by ld2licl
    lc = ap(w, A, 'ld2licl', [J(w, A, P[A7C], hrp)], concl('ld2licl'))
    ibl = dst(w, A, [lc], 'simpld', '( u e. %s |-> %s ) e. L^1' % (I, GRHV('u')))
    val = dst(w, A, [lc], 'simprd', '%s = ( _i x. %s )' % (LIH('H'), ITG(I, GRHV('u'), 'u')))
    gv = a1(w, Au, 'fvex', '%s e. _V' % GRHV('u'))
    itc = w.s([gv, ibl], 'itgcl', '( %s -> %s e. CC )' % (A, ITG(I, GRHV('u'), 'u')))
    lic = dst(w, A, [val, dst(w, A, [a1(w, A, 'ax-icn', '_i e. CC'), itc], 'mulcld', '( _i x. %s ) e. CC' % ITG(I, GRHV('u'), 'u'))], 'eqeltrd', '%s e. CC' % LIH('H'))
    alr = dst(w, A, [lic], 'abscld', '%s e. RR' % AL); al0 = dst(w, A, [lic], 'absge0d', '0 <_ %s' % AL)
    c.leaf(AL, 'RR', alr)
    sq1 = ap(w, A, 'le2sq2', [J(w, A, alr, al0), J(w, A, c.mem('( %s x. %s )' % (KC, I1), 'RR'), li)], '( %s ^ 2 ) <_ ( ( %s x. %s ) ^ 2 )' % (AL, KC, I1))
    sqm = dst(w, A, [c.mem(KC, 'CC'), c.mem(I1, 'CC')], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (KC, I1, KC, I1))
    k2 = dst(w, A, [c.mem('( %s ^ 2 )' % I1, 'RR'), c.mem('( 4 x. %s )' % I2, 'RR'), c.mem('( %s ^ 2 )' % KC, 'RR'), dst(w, A, [c.mem(KC, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % KC), csq], 'lemul2ad',
             '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) <_ ( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (KC, I1, KC, I2))
    t1 = dst(w, A, [sq1, sqm], 'breqtrd', '( %s ^ 2 ) <_ ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (AL, KC, I1))
    dst(w, A, [c.mem('( %s ^ 2 )' % AL, 'RR'), c.mem('( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (KC, I1), 'RR'), c.mem('( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (KC, I2), 'RR'), t1, k2], 'letrd',
        '( %s ^ 2 ) <_ ( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (AL, KC, I2))
    return fin(w)


if __name__ == '__main__':
    for f in (ld2macn, ld2vlcv, ld2licl, ld2ptw, ld2li, ld2sq1):
        if want(f.__name__):
            f()
