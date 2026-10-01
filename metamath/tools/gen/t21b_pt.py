"""Sortie T21b: t21pt (the main inequality of theta_AP_T21 at one point)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from t21b_psi import ERR, OML, ZTT as ZT3_ignore
from c8lib import lin8
from mvlib import ringeq as ringeq_d
import cl as _cl

L = LX
PHI = '( phi ` N )'


def gen_pt():
    w = W('t21pt', 'T2.1 at one point: with the density bodies at ` N ` , the pinned ` R ` , ` V ` , the zeta clearance and the eight thresholds at ` X ` , ` abs ( theta ( Y ; N , A ) - Y / phi ( N ) ) <_ E Y / phi ( N ) ` for ` A ` a unit mod ` N ` at the level, no bad conductor dividing ` N ` (Lean ` theta_AP_T21 ` 2034-2197; ~ t21tha , ~ t21efe , ~ t21sm , ~ t21zt , ~ t21nzb ).')
    A0, concl = split_imp(SB['t21pt'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    er, e0 = u['E e. RR'], u['0 < E']
    xr, ur, zeta = u['X e. RR'], u['U e. RR'], u[ZETA('U', 'V')]
    nn, az, ag = u['N e. NN'], u['A e. ZZ'], u['( A gcd N ) = 1']
    yr, nx, ny, yx = u['Y e. RR'], u['N <_ ( X ^c %s )' % F191], u['( N x. ( X ^c %s ) ) <_ Y' % F709], u['Y <_ X']
    rp_, vp = u['R e. RR+'], u['V e. RR+']
    hb = u[HBAD(Z191, TAU, 'V', 'N')]
    tu = u
    ks = list(tu)
    E10 = '( exp ` ; 1 0 )'
    t1 = tu['%s <_ X' % E10]
    t2 = tu['( %s x. ( %s ^ 2 ) ) <_ ( E x. ( X ^c %s ) )' % (C675, L, F2931800)]
    t3 = tu['( ; 8 1 x. %s ) <_ ( E x. ( X ^c %s ) )' % (L, F259900)]
    t8a = tu['R <_ ( ( 1 - U ) x. %s )' % L]
    # exp 1 <_ X
    e10r = s([s([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'reefcld', '%s e. RR' % E10)
    e1r = s([s([], '1red', '1 e. RR')], 'reefcld', '( exp ` 1 ) e. RR')
    ef = ap(w, A0, [s([], '1red', '1 e. RR'), s([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'efle', '( 1 <_ ; 1 0 <-> ( exp ` 1 ) <_ %s )' % E10)
    e1l = s([s([num.le_lit(w, '1', '; 1 0')], 'a1i', '1 <_ ; 1 0'), ef], 'mpbid', '( exp ` 1 ) <_ %s' % E10)
    xe = s([e1r, e10r, xr, e1l, t1], 'letrd', '( exp ` 1 ) <_ X')
    import t21a_z1
    b = t21a_z1.x_basics(w, A0, xr, xe)
    lr = b['lr']; xp = b['xp']
    lp = s([lr, lin.linarith(w, A0, [b['l1']], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    ep = s([er, e0], 'elrpd', 'E e. RR+')
    # level facts
    uu = dict(u); uu['( exp ` 1 ) <_ X'] = xe
    import t21b_tr
    c = t21b_tr.basics(w, A0, uu)
    nr, np_ = c['nr'], c['np']
    # tau, U <_ tau
    rr = s([rp_], 'rpred', 'R e. RR')
    RL = '( R / %s )' % L
    rlr = s([rr, lp], 'rerpdivcld', '%s e. RR' % RL)
    U1 = '( 1 - U )'
    rl1 = s([t8a, s([rr, s([s([], '1red', '1 e. RR'), ur], 'resubcld', '%s e. RR' % U1), lp], 'ledivmuld', '( %s <_ %s <-> R <_ ( %s x. %s ) )' % (RL, U1, L, U1))], 'x', 'x') if False else None
    cm = s([s([s([], '1red', '1 e. RR') and ur, s([lr], 'recnd', '%s e. CC' % L)], 'x', 'x')], 'x', 'x') if False else None
    u1r = s([s([], '1red', '1 e. RR'), ur], 'resubcld', '%s e. RR' % U1)
    mc = s([s([u1r], 'recnd', '%s e. CC' % U1), s([lr], 'recnd', '%s e. CC' % L)], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (U1, L, L, U1))
    t8c = s([t8a, mc], 'breqtrd', 'R <_ ( %s x. %s )' % (L, U1))
    rlu = s([t8c, s([rr, u1r, lp], 'ledivmuld', '( %s <_ %s <-> R <_ ( %s x. %s ) )' % (RL, U1, L, U1))], 'mpbird', '%s <_ %s' % (RL, U1))
    taur = s([s([], '1red', '1 e. RR'), rlr], 'resubcld', '%s e. RR' % TAU)
    ut = lin8(w, A0, [rlu], 'U <_ %s' % TAU, {'U': ur, RL: rlr})
    # hbad in the letter j
    FZ = '( 2 ... ( |_ ` %s ) )' % Z191
    bcj = lambda e_: w.s([], 't21bcj', '%s = %s' % (BC(TAU, 'V', e_), BC(TAU, 'V', e_, y='j')))
    b1 = w.s([bcj('e')], 'neeq1i', '( %s =/= (/) <-> %s =/= (/) )' % (BC(TAU, 'V', 'e'), BC(TAU, 'V', 'e', y='j')))
    b2 = w.s([w.s([b1], 'a1i', '( e e. %s -> ( %s =/= (/) <-> %s =/= (/) ) )' % (FZ, BC(TAU, 'V', 'e'), BC(TAU, 'V', 'e', y='j')))], 'rabbiia', '%s = %s' % (BAD(Z191, TAU, 'V'), BAD(Z191, TAU, 'V', y='j')))
    b3 = w.s([b2], 'raleqi', '( %s <-> %s )' % (HBAD(Z191, TAU, 'V', 'N'), HBAD(Z191, TAU, 'V', 'N', y='j')))
    hbj = s([hb, s([b3], 'a1i', '( %s <-> %s )' % (HBAD(Z191, TAU, 'V', 'N'), HBAD(Z191, TAU, 'V', 'N', y='j')))], 'mpbid', HBAD(Z191, TAU, 'V', 'N', y='j'))
    z191r = s([s([xp, c['f191']], 'rpcxpcld', '%s e. RR+' % Z191)], 'rpred', '%s e. RR' % Z191)
    vr = s([vp], 'rpred', 'V e. RR')
    he = ap(w, A0, [nn, taur, ur, ut, vr, b['x3r'], z191r, nx, zeta, hbj], 't21nzb', HEMPTY('N', X3, TAU, 'V'))
    # zones
    LFB = LFD_BODY('G', 'C'); LGB = LGD_BODY('H', 'P', 'B', 'K')
    T4X = '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( X ^c %s ) )' % (N4320, L, F7900)
    T5X = '( ( %s x. ( 5 ^ K ) ) x. H ) <_ ( E x. ( %s ^c %s ) )' % (N50112, L, F92)
    T6X = '( ; 1 8 x. %s ) <_ %s' % (CSL, L)
    EXZ = '( exp ` ( -u %s x. R ) )' % F9200; E28 = '( exp ` ( ; 2 8 x. R ) )'
    zt = ap(w, A0, [nn, xr, xe, yr, nx, ny, yx, er, e0, u['G e. RR'], u['1 <_ G'], u['C e. RR'], u['1 <_ C'], u['C <_ 2'], u[LFB],
                    u['H e. RR'], u['1 <_ H'], u['P e. RR'], u['0 <_ P'], u['P <_ ( 7 / 2 )'], u['B e. RR'], u['1 <_ B'], u['B <_ ( 5 / 4 )'], u['K e. NN0'], u[LGB],
                    rp_, vp, u['( %s x. ( G x. %s ) ) <_ E' % (N6912, EXZ)], u['( ; 2 7 x. ( G x. %s ) ) <_ ( E x. V )' % E28],
                    tu[T4X], tu[T5X], tu[T6X], tu['R <_ %s' % CSL], tu['( ; 4 0 x. R ) <_ %s' % L], he], 't21zt', '%s <_ ( ( 4 x. ( E x. Y ) ) / ; 2 7 )' % ZT(X3, 'Y', HALF))
    efe = ap(w, A0, [nn, xr, xe, yr, nx, ny, yx, er, e0, t2], 't21efe', '%s <_ ( ( ( E / 9 ) x. Y ) / N )' % EFERR('N', X3, 'Y'))
    SM = '( ( %s x. ( log ` Y ) ) + %s )' % (OM('N'), SQL('Y'))
    sm = ap(w, A0, [nn, xr, xe, yr, nx, ny, yx, er, e0, t3], 't21sm', '%s <_ ( ( ( ( 2 x. E ) / ; 2 7 ) x. Y ) / N )' % SM)
    # 100 <_ Y
    A_ = '( ; ; 7 0 9 / ; 9 0 )'
    Ah = '( ( ; ; 7 0 9 / ; 9 0 ) / 2 )'
    ahr = s([num.real(w, Ah)], 'a1i', '%s e. RR' % Ah) if False else s([s([num.real(w, A_)], 'a1i', '%s e. RR' % A_), s([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+')], 'rerpdivcld', '%s e. RR' % Ah)
    ah0 = lin.linarith(w, A0, [], '0 <_ %s' % Ah, leaves={}) if False else s([s([num.real(w, A_)], 'a1i', '%s e. RR' % A_), s([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), s([num.le_lit(w, '0', A_)], 'a1i', '0 <_ %s' % A_)], 'divge0d', '0 <_ %s' % Ah)
    g1 = ap(w, A0, [ahr, ah0], 'efge1p2', '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ ( exp ` %s )' % (Ah, Ah, Ah))
    EA = '( exp ` %s )' % Ah
    ear = s([ahr], 'reefcld', '%s e. RR' % EA)
    cla = _cl.Closure(w, A0, {})
    cla.leaf(Ah, 'RR', ahr)
    sqa = s([s([ahr], 'recnd', '%s e. CC' % Ah)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (Ah, Ah, Ah))
    # numeric: 12 <_ ( 1 + a ) + a^2 / 2 with a = 709/180
    a12 = lin.nlinarith(w, A0, [], '; 1 2 <_ ( ( 1 + %s ) + ( ( %s x. %s ) / 2 ) )' % (Ah, Ah, Ah), leaves={}) if False else None
    v = lin.lineq(w, A0, Ah, '( ; ; 7 0 9 / ; ; 1 8 0 )')
    a12 = s([s([s([sqa, s([v, v], 'oveq12d', '( %s x. %s ) = ( ( ; ; 7 0 9 / ; ; 1 8 0 ) x. ( ; ; 7 0 9 / ; ; 1 8 0 ) )' % (Ah, Ah))], 'eqtrd', '( %s ^ 2 ) = ( ( ; ; 7 0 9 / ; ; 1 8 0 ) x. ( ; ; 7 0 9 / ; ; 1 8 0 ) )' % Ah)], 'x', 'x')], 'x', 'x') if False else None
    sq2 = s([sqa, s([v, v], 'oveq12d', '( %s x. %s ) = ( ( ; ; 7 0 9 / ; ; 1 8 0 ) x. ( ; ; 7 0 9 / ; ; 1 8 0 ) )' % (Ah, Ah))], 'eqtrd', '( %s ^ 2 ) = ( ( ; ; 7 0 9 / ; ; 1 8 0 ) x. ( ; ; 7 0 9 / ; ; 1 8 0 ) )' % Ah)
    mul = s([num.mul_lits(w, '( ; ; 7 0 9 / ; ; 1 8 0 )', '( ; ; 7 0 9 / ; ; 1 8 0 )')], 'x', 'x') if False else None
    PR = '( ( ; ; 7 0 9 / ; ; 1 8 0 ) x. ( ; ; 7 0 9 / ; ; 1 8 0 ) )'
    pr_ = s([num.real(w, '( ; ; 7 0 9 / ; ; 1 8 0 )'), num.real(w, '( ; ; 7 0 9 / ; ; 1 8 0 )')], 'x', 'x') if False else None
    p15 = lin.nlinarith(w, A0, [], '; 1 5 <_ %s' % PR, leaves={}) if False else None
    # 709/180 >= 3.9 so its square >= 15: ( 39 / 10 ) <_ 709/180
    q39 = s([num.le_lit(w, '( ; 3 9 / ; 1 0 )', '( ; ; 7 0 9 / ; ; 1 8 0 )')], 'a1i', '( ; 3 9 / ; 1 0 ) <_ ( ; ; 7 0 9 / ; ; 1 8 0 )')
    r709 = s([num.real(w, '( ; ; 7 0 9 / ; ; 1 8 0 )')], 'a1i', '( ; ; 7 0 9 / ; ; 1 8 0 ) e. RR')
    r39 = s([num.real(w, '( ; 3 9 / ; 1 0 )')], 'a1i', '( ; 3 9 / ; 1 0 ) e. RR')
    z39 = s([num.le_lit(w, '0', '( ; 3 9 / ; 1 0 )')], 'a1i', '0 <_ ( ; 3 9 / ; 1 0 )')
    sq39 = s([r39, r709, r39, r709, z39, z39, q39, q39], 'lemul12ad', '( ( ; 3 9 / ; 1 0 ) x. ( ; 3 9 / ; 1 0 ) ) <_ %s' % PR)
    m39 = lin.lineq(w, A0, '( ( ; 3 9 / ; 1 0 ) x. ( ; 3 9 / ; 1 0 ) )', '( ; ; ; 1 5 2 1 / ; ; 1 0 0 )')
    prr = s([r709, r709], 'remulcld', '%s e. RR' % PR)
    clb = _cl.Closure(w, A0, {})
    for k_, st_ in ((Ah, ahr), (PR, prr), ('( %s ^ 2 )' % Ah, s([ahr], 'resqcld', '( %s ^ 2 ) e. RR' % Ah)), (EA, ear)):
        clb.leaf(k_, 'RR', st_); clb.atom(k_)
    e12 = lin.linarith(w, A0, [g1, sq2, sq39, m39, v], '; 1 2 <_ %s' % EA, closure=clb)
    # exp A = exp(a) exp(a) >= 144 >= 100
    EAA = '( exp ` %s )' % A_
    aa = lin.lineq(w, A0, A_, '( %s + %s )' % (Ah, Ah)) if False else None
    ea2 = s([s([s([s([ahr], 'recnd', '%s e. CC' % Ah), s([ahr], 'recnd', '%s e. CC' % Ah)], 'jca', '( %s e. CC /\\ %s e. CC )' % (Ah, Ah)), w.inst('efadd')], 'syl', '( exp ` ( %s + %s ) ) = ( %s x. %s )' % (Ah, Ah, EA, EA))], 'x', 'x') if False else None
    ea2 = ap(w, A0, [s([ahr], 'recnd', '%s e. CC' % Ah), s([ahr], 'recnd', '%s e. CC' % Ah)], 'efadd', '( exp ` ( %s + %s ) ) = ( %s x. %s )' % (Ah, Ah, EA, EA))
    hh = lin.lineq(w, A0, '( %s + %s )' % (Ah, Ah), A_)
    ea3 = s([s([s([hh], 'fveq2d', '( exp ` ( %s + %s ) ) = %s' % (Ah, Ah, EAA))], 'eqcomd', '%s = ( exp ` ( %s + %s ) )' % (EAA, Ah, Ah)), ea2], 'eqtrd', '%s = ( %s x. %s )' % (EAA, EA, EA))
    twelve = s([num.real(w, '; 1 2')], 'a1i', '; 1 2 e. RR')
    p144 = s([twelve, ear, twelve, ear, s([num.ge0_nat(w, 12)], 'a1i', '0 <_ ; 1 2'), s([num.ge0_nat(w, 12)], 'a1i', '0 <_ ; 1 2'), e12, e12], 'lemul12ad', '( ; 1 2 x. ; 1 2 ) <_ ( %s x. %s )' % (EA, EA))
    earr = s([s([num.real(w, A_)], 'a1i', '%s e. RR' % A_)], 'reefcld', '%s e. RR' % EAA)
    e100 = lin8(w, A0, [p144, ea3], '; ; 1 0 0 <_ %s' % EAA, {'( %s x. %s )' % (EA, EA): s([ear, ear], 'remulcld', '( %s x. %s ) e. RR' % (EA, EA)), EAA: earr}) if False else None
    m144 = s([num.mul_lits(w, '; 1 2', '; 1 2')], 'x', 'x') if False else None
    c144 = lin.lineq(w, A0, '( ; 1 2 x. ; 1 2 )', '; ; 1 4 4')
    e100 = lin8(w, A0, [p144, ea3, c144], '; ; 1 0 0 <_ %s' % EAA, {'( %s x. %s )' % (EA, EA): s([ear, ear], 'remulcld', '( %s x. %s ) e. RR' % (EA, EA)), EAA: earr, '( ; 1 2 x. ; 1 2 )': s([twelve, twelve], 'remulcld', '( ; 1 2 x. ; 1 2 ) e. RR')})
    # X ^c ( 709 / 900 ) >= ( exp 10 ) ^c ( 709 / 900 ) = exp ( 709 / 90 )
    X709 = '( X ^c %s )' % F709
    e10p = s([s([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'rpefcld', '%s e. RR+' % E10)
    cx = s([e10r, s([e10p], 'rpge0d', '0 <_ %s' % E10), xr, c['f709'], s([num.le_lit(w, '0', F709)], 'a1i', '0 <_ %s' % F709), t1], 'cxple2ad', '( %s ^c %s ) <_ %s' % (E10, F709, X709))
    ce = s([s([e10p], 'rpcnd', '%s e. CC' % E10), s([e10p], 'rpne0d', '%s =/= 0' % E10), s([num.cc(w, F709)], 'a1i', '%s e. CC' % F709)], 'cxpefd', '( %s ^c %s ) = ( exp ` ( %s x. ( log ` %s ) ) )' % (E10, F709, F709, E10))
    le10 = ap(w, A0, [s([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'relogef', '( log ` %s ) = ; 1 0' % E10)
    mm_ = s([s([le10], 'oveq2d', '( %s x. ( log ` %s ) ) = ( %s x. ; 1 0 )' % (F709, E10, F709)), lin.lineq(w, A0, '( %s x. ; 1 0 )' % F709, A_)], 'eqtrd', '( %s x. ( log ` %s ) ) = %s' % (F709, E10, A_))
    ce2 = s([ce, s([mm_], 'fveq2d', '( exp ` ( %s x. ( log ` %s ) ) ) = %s' % (F709, E10, EAA))], 'eqtrd', '( %s ^c %s ) = %s' % (E10, F709, EAA))
    x709 = s([s([ce2], 'eqcomd', '%s = ( %s ^c %s )' % (EAA, E10, F709)), cx], 'eqbrtrd', '%s <_ %s' % (EAA, X709))
    x709r = s([s([xp, c['f709']], 'rpcxpcld', '%s e. RR+' % X709)], 'rpred', '%s e. RR' % X709)
    y100 = lin.nlinarith(w, A0, [e100, x709, c['n1'], ny], '; ; 1 0 0 <_ Y', leaves={EAA: earr, X709: x709r, 'N': nr, 'Y': yr})
    ny_ = lin.nlinarith(w, A0, [c['n1'], ny, lin.linarith(w, A0, [e100, x709], '1 <_ %s' % X709, leaves={EAA: earr, X709: x709r})], 'N <_ Y', leaves={X709: x709r, 'N': nr, 'Y': yr})
    t2x = lin.linarith(w, A0, [b['x8']], '2 <_ %s' % X3, leaves={X3: b['x3r']})
    tha = ap(w, A0, [nn, az, ag, yr, y100, b['x3r'], t2x, ny_], 't21tha', '( abs ` ( ( A ( thetaAP ` N ) Y ) - ( Y / %s ) ) ) <_ ( ( ( %s + %s ) + ( ( 3 / %s ) x. %s ) ) + %s )' %
             (PHI, EFERR('N', X3, 'Y'), OML.replace('Y', 'Y'), PHI, ZT(X3, 'Y', HALF), SQL('Y')))
    # combine, multiplied by phi
    phn = s([nn, w.inst('phicl')], 'syl', '%s e. NN' % PHI)
    php = s([phn], 'nnrpd', '%s e. RR+' % PHI)
    phr = s([php], 'rpred', '%s e. RR' % PHI)
    phl = s([nn, w.inst('z5phile')], 'syl', '%s <_ N' % PHI)
    EF = EFERR('N', X3, 'Y')
    e9y = '( ( E / 9 ) x. Y )'
    y0 = lin.linarith(w, A0, [c['y1']], '0 <_ Y', leaves={'Y': yr})
    e9yr = s([s([er, s([num.rp_nat(w, 9)], 'a1i', '9 e. RR+')], 'rerpdivcld', '( E / 9 ) e. RR'), yr], 'remulcld', '%s e. RR' % e9y)
    e9y0 = s([s([er, s([num.rp_nat(w, 9)], 'a1i', '9 e. RR+'), lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er})], 'divge0d', '0 <_ ( E / 9 )'), y0], 'x', 'x') if False else None
    e9y0 = s([s([er, s([num.real(w, '9')], 'a1i', '9 e. RR')], 'x', 'x')], 'x', 'x') if False else None
    e90 = s([er, s([num.rp_nat(w, 9)], 'a1i', '9 e. RR+'), lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er})], 'divge0d', '0 <_ ( E / 9 )')
    e9y0 = s([s([er, s([num.rp_nat(w, 9)], 'a1i', '9 e. RR+')], 'rerpdivcld', '( E / 9 ) e. RR'), yr, e90, y0], 'mulge0d', '0 <_ %s' % e9y)

    def to_phi(bound, lhs, num_, numr, num0):
        # lhs <_ num / N  ==>  ( lhs x. phi ) <_ num
        d1 = s([php, np_, numr, num0, phl], 'lediv2ad', '( %s / N ) <_ ( %s / %s )' % (num_, num_, PHI))
        lr_ = s([s([numr, np_], 'rerpdivcld', '( %s / N ) e. RR' % num_)], 'x', 'x') if False else None
        return d1
    EFr = s([s([num.real(w, C12)], 'a1i', '%s e. RR' % C12), _efsum(w, A0, s, c, b)], 'remulcld', '%s e. RR' % EF)
    d1 = s([php, np_, e9yr, e9y0, phl], 'lediv2ad', '( %s / N ) <_ ( %s / %s )' % (e9y, e9y, PHI))
    f1 = s([EFr, s([e9yr, np_], 'rerpdivcld', '( %s / N ) e. RR' % e9y), s([e9yr, php], 'rerpdivcld', '( %s / %s ) e. RR' % (e9y, PHI)), efe, d1], 'letrd', '%s <_ ( %s / %s )' % (EF, e9y, PHI))
    f1p = s([f1, s([EFr, e9yr, php], 'lemuldivd', '( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) )' % (EF, PHI, e9y, EF, e9y, PHI))], 'mpbird', '( %s x. %s ) <_ %s' % (EF, PHI, e9y))
    e2y = '( ( ( 2 x. E ) / ; 2 7 ) x. Y )'
    e2yr = s([s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er], 'remulcld', '( 2 x. E ) e. RR'), s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '( ( 2 x. E ) / ; 2 7 ) e. RR'), yr], 'remulcld', '%s e. RR' % e2y)
    e2y0 = s([s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er], 'remulcld', '( 2 x. E ) e. RR'), s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+'),
                 s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er, s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er})], 'mulge0d', '0 <_ ( 2 x. E )')], 'divge0d', '0 <_ ( ( 2 x. E ) / ; 2 7 )'),
              yr, s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er], 'remulcld', '( 2 x. E ) e. RR'), s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '( ( 2 x. E ) / ; 2 7 ) e. RR') and None or
              s([s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er], 'remulcld', '( 2 x. E ) e. RR'), s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+'),
                   s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er, s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er})], 'mulge0d', '0 <_ ( 2 x. E )')], 'divge0d', '0 <_ ( ( 2 x. E ) / ; 2 7 )'), y0], 'x', 'x') if False else y0], 'mulge0d', '0 <_ %s' % e2y) if False else None
    c2e = s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er], 'remulcld', '( 2 x. E ) e. RR'), s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '( ( 2 x. E ) / ; 2 7 ) e. RR')
    c2e0 = s([s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er], 'remulcld', '( 2 x. E ) e. RR'), s([num.rp_nat(w, 27)], 'a1i', '; 2 7 e. RR+'),
              s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), er, s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er})], 'mulge0d', '0 <_ ( 2 x. E )')], 'divge0d', '0 <_ ( ( 2 x. E ) / ; 2 7 )')
    e2y0 = s([c2e, yr, c2e0, y0], 'mulge0d', '0 <_ %s' % e2y)
    SMr = s([_omlr(w, A0, s, nn, c), _sqlr(w, A0, s, c)], 'readdcld', '%s e. RR' % SM)
    d2 = s([php, np_, e2yr, e2y0, phl], 'lediv2ad', '( %s / N ) <_ ( %s / %s )' % (e2y, e2y, PHI))
    f2 = s([SMr, s([e2yr, np_], 'rerpdivcld', '( %s / N ) e. RR' % e2y), s([e2yr, php], 'rerpdivcld', '( %s / %s ) e. RR' % (e2y, PHI)), sm, d2], 'letrd', '%s <_ ( %s / %s )' % (SM, e2y, PHI))
    f2p = s([f2, s([SMr, e2yr, php], 'lemuldivd', '( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) )' % (SM, PHI, e2y, SM, e2y, PHI))], 'mpbird', '( %s x. %s ) <_ %s' % (SM, PHI, e2y))
    # the main chain
    D = '( ( A ( thetaAP ` N ) Y ) - ( Y / %s ) )' % PHI
    ZTT = ZT(X3, 'Y', HALF)
    TZ = '( ( 3 / %s ) x. %s )' % (PHI, ZTT)
    RHS = '( ( ( %s + %s ) + %s ) + %s )' % (EF, OML, TZ, SQL('Y'))
    thr_ = ap(w, A0, [nn, az, yr], 'thetaapcl', '( A ( thetaAP ` N ) Y ) e. RR')
    dr = s([thr_, s([yr, php], 'rerpdivcld', '( Y / %s ) e. RR' % PHI)], 'resubcld', '%s e. RR' % D)
    adr = s([s([dr], 'recnd', '%s e. CC' % D)], 'abscld', '( abs ` %s ) e. RR' % D)
    ztr = s([zt, zt], 'x', 'x') if False else None
    import t21b_zt
    ZTr = _ztr(w, A0, nn, b, yr, y0)
    omlr = _omlr(w, A0, s, nn, c); sqlr = _sqlr(w, A0, s, c)
    tzr = s([s([s([num.real(w, '3')], 'a1i', '3 e. RR'), php], 'rerpdivcld', '( 3 / %s ) e. RR' % PHI), ZTr], 'remulcld', '%s e. RR' % TZ)
    rhsr = s([s([s([EFr, omlr], 'readdcld', '( %s + %s ) e. RR' % (EF, OML)), tzr], 'readdcld', '( ( %s + %s ) + %s ) e. RR' % (EF, OML, TZ)), sqlr], 'readdcld', '%s e. RR' % RHS)
    m1 = s([adr, rhsr, phr, s([php], 'rpge0d', '0 <_ %s' % PHI), tha], 'lemul1ad', '( ( abs ` %s ) x. %s ) <_ ( %s x. %s )' % (D, PHI, RHS, PHI))
    cl = _cl.Closure(w, A0, {})
    for k_, st_ in ((EF, EFr), (OML, omlr), (TZ, tzr), (SQL('Y'), sqlr), (PHI, phr)):
        cl.leaf(k_, 'RR', st_); cl.atom(k_)
    ex = ringeq_d(w, A0, '( %s x. %s )' % (RHS, PHI), '( ( ( %s x. %s ) + ( %s x. %s ) ) + ( %s x. %s ) )' % (EF, PHI, SM, PHI, TZ, PHI), cl)
    tzp = s([s([s([s([num.cc(w, '3')], 'a1i', '3 e. CC'), s([php], 'rpcnd', '%s e. CC' % PHI)], 'x', 'x')], 'x', 'x')], 'x', 'x') if False else None
    q3 = s([s([s([num.real(w, '3')], 'a1i', '3 e. RR'), php], 'rerpdivcld', '( 3 / %s ) e. RR' % PHI)], 'recnd', '( 3 / %s ) e. CC' % PHI)
    tz1 = s([q3, s([ZTr], 'recnd', '%s e. CC' % ZTT), s([php], 'rpcnd', '%s e. CC' % PHI)], 'mul32d', '( %s x. %s ) = ( ( ( 3 / %s ) x. %s ) x. %s )' % (TZ, PHI, PHI, PHI, ZTT))
    tz2 = s([s([num.cc(w, '3')], 'a1i', '3 e. CC'), s([php], 'rpcnd', '%s e. CC' % PHI), s([php], 'rpne0d', '%s =/= 0' % PHI)], 'divcan1d', '( ( 3 / %s ) x. %s ) = 3' % (PHI, PHI))
    tz3 = s([tz1, s([tz2], 'oveq1d', '( ( ( 3 / %s ) x. %s ) x. %s ) = ( 3 x. %s )' % (PHI, PHI, ZTT, ZTT))], 'eqtrd', '( %s x. %s ) = ( 3 x. %s )' % (TZ, PHI, ZTT))
    EY = '( E x. Y )'
    eyr = s([er, yr], 'remulcld', '%s e. RR' % EY)
    ey0 = s([er, yr, lin.linarith(w, A0, [e0], '0 <_ E', leaves={'E': er}), y0], 'mulge0d', '0 <_ %s' % EY)
    cl2 = _cl.Closure(w, A0, {})
    for k_, st_ in (('E', er), ('Y', yr)):
        cl2.leaf(k_, 'RR', st_); cl2.atom(k_)
    q1 = ringeq_d(w, A0, e9y, '( ( 1 / 9 ) x. %s )' % EY, cl2)
    q2 = ringeq_d(w, A0, e2y, '( ( 2 / ; 2 7 ) x. %s )' % EY, cl2)
    tot = lin8(w, A0, [m1, ex, tz3, f1p, f2p, q1, q2, zt, ey0], '( ( abs ` %s ) x. %s ) <_ %s' % (D, PHI, EY),
               {'( ( abs ` %s ) x. %s )' % (D, PHI): s([adr, phr], 'remulcld', '( ( abs ` %s ) x. %s ) e. RR' % (D, PHI)), '( %s x. %s )' % (RHS, PHI): s([rhsr, phr], 'remulcld', '( %s x. %s ) e. RR' % (RHS, PHI)),
                '( %s x. %s )' % (EF, PHI): s([EFr, phr], 'remulcld', '( %s x. %s ) e. RR' % (EF, PHI)), '( %s x. %s )' % (SM, PHI): s([SMr, phr], 'remulcld', '( %s x. %s ) e. RR' % (SM, PHI)),
                '( %s x. %s )' % (TZ, PHI): s([tzr, phr], 'remulcld', '( %s x. %s ) e. RR' % (TZ, PHI)), ZTT: ZTr, EY: eyr, e9y: e9yr, e2y: e2yr})
    fin = s([tot, s([adr, eyr, php], 'lemuldivd', '( ( ( abs ` %s ) x. %s ) <_ %s <-> ( abs ` %s ) <_ ( %s / %s ) )' % (D, PHI, EY, D, EY, PHI))], 'mpbid', concl)
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21pt']))
    return go(w)


def _efsum(w, A0, s, c, b):
    import t21b_h
    p = t21b_h.eferr_parts(w, A0, 'N', c['nr'], c['n1'], c['yr'], c['y1'], b['x3r'], lin.linarith(w, A0, [b['x8']], '2 <_ %s' % X3, leaves={X3: b['x3r']}), T=X3)
    return p['ir']


def _omlr(w, A0, s, nn, c):
    omn = s([s([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin'), w.inst('hashcl')], 'syl', '%s e. NN0' % OM('N'))
    return s([s([omn], 'nn0red', '%s e. RR' % OM('N')), s([c['yp']], 'relogcld', '( log ` Y ) e. RR')], 'remulcld', '%s e. RR' % OML)


def _sqlr(w, A0, s, c):
    yp = c['yp']
    t2s = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), s([s([yp], 'rpsqrtcld', '( sqrt ` Y ) e. RR+')], 'rpred', '( sqrt ` Y ) e. RR')], 'remulcld', '( 2 x. ( sqrt ` Y ) ) e. RR')
    return s([t2s, s([yp], 'relogcld', '( log ` Y ) e. RR')], 'remulcld', '%s e. RR' % SQL('Y'))


def _ztr(w, A0, nn, b, yr, y0):
    import t21alib as _ta
    from cl import lift as lf
    half_r = w.s([num.real(w, HALF)], 'a1i', '( %s -> %s e. RR )' % (A0, HALF))
    h0 = w.s([w.s([], 'halfgt0', '0 < %s' % HALF)], 'a1i', '( %s -> 0 < %s )' % (A0, HALF))
    h1 = lin.linarith(w, A0, [w.s([w.s([], 'halflt1', '%s < 1' % HALF)], 'a1i', '( %s -> %s < 1 )' % (A0, HALF))], '%s <_ 1' % HALF, leaves={HALF: half_r})
    tr = b['x3r']
    tot, inf = _ta.nc_real(w, A0, nn, half_r, h0, h1, tr, HALF, X3)
    C1, C2 = inf['C1'], inf['C2']
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, ZFX(HALF, X3)))
    qf = _ta.q_facts(w, C2, qin, lf(w, half_r, C2), lf(w, tr, C2), HALF, X3)
    wr, w0, _ = _ta.wt_facts(w, C2, inf['orr'], inf['or0'], qf)
    yre = w.s([lf(w, yr, C2), lf(w, y0, C2), qf['re']], 'recxpcld', '( %s -> ( Y ^c ( Re ` q ) ) e. RR )' % C2)
    body = w.s([wr, yre], 'remulcld', '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) e. RR )' % (C2, WT()))
    inner = w.s([inf['zfin'], body], 'fsumrecl', '( %s -> sum_ q e. %s ( %s x. ( Y ^c ( Re ` q ) ) ) e. RR )' % (C1, ZFX(HALF, X3), WT()))
    return w.s([inf['dfin'], inner], 'fsumrecl', '( %s -> %s e. RR )' % (A0, ZT(X3, 'Y', HALF)))


if __name__ == '__main__':
    gen_pt()
