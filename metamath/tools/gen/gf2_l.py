"""Sortie GF2, section L: the left line Re w = -99/100 at the frozen parameters (Lean norm_LFunction_left_line_le,
norm_gramInt_left_le, norm_Brem_le).  Helpers gf2els2/4/5 are the log D >_ 2 variants of Z6a's z6els2/4/5.
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_l.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L_
import gf1lib as G1L
from gf1lib import tsub, proj, build
from mvlib import ringeq, ringeqp

S_ = L_.S
E99 = '( ; 9 9 / ; ; 2 0 0 )'
L1S = ('( ( ( N e. NN /\\ D e. RR ) /\\ ( ( T e. RR /\\ 0 <_ T ) /\\ ( A e. RR /\\ 0 <_ A ) /\\ ( U e. RR /\\ 0 <_ U ) ) /\\ '
       '( ( T - A ) <_ U /\\ ( N x. ( A + 2 ) ) <_ D ) ) -> ( ( N x. ( T + 2 ) ) <_ ( D x. ( 1 + U ) ) /\\ ( N x. ( T + 3 ) ) <_ ( ( 2 x. D ) x. ( 1 + U ) ) ) )')
C2 = '; ; ; ; ; 2 0 0 0 0 0'
C6 = '; ; ; ; ; 6 0 0 0 0 0'
D4 = '( ( 2 x. ( 2 x. D ) ) x. ( 1 + U ) )'
S_['gf2els2'] = ('( ( ( D e. RR+ /\\ 2 <_ ( log ` D ) ) /\\ ( U e. RR /\\ 0 <_ U ) /\\ ( B e. RR+ /\\ B <_ %s ) ) -> '
                 '( log ` B ) <_ ( ( 2 x. ( log ` D ) ) x. ( 1 + U ) ) )' % D4)


def gf2els2():
    w = W('gf2els2', 'Helper of ~ gf2lcv : ` log B <_ 2 log D ( 1 + U ) ` from ` B <_ 4 D ( 1 + U ) ` , ` log D >_ 2 ` ( ` log 4 < 2 ` , ` log ( 1 + U ) <_ U ` ).')
    a = split_imp(S_['gf2els2'])[0]; st = mkst(w, a)
    Lg = '( log ` D )'; U = '( 1 + U )'
    drp = proj(w, a, 'D e. RR+'); ur = proj(w, a, 'U e. RR'); u0 = proj(w, a, '0 <_ U'); brp = proj(w, a, 'B e. RR+'); l2 = proj(w, a, '2 <_ ( log ` D )')
    bb = proj(w, a, 'B <_ %s' % D4)
    lr = st([drp], 'relogcld', '%s e. RR' % Lg)
    tworp = a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')
    Urp = st([st([st([], '1red', '1 e. RR'), ur], 'readdcld', '%s e. RR' % U), lin.linarith(w, a, [u0], '0 < %s' % U, leaves={'U': ur})], 'elrpd', '%s e. RR+' % U)
    D2 = '( 2 x. D )'; D22 = '( 2 x. ( 2 x. D ) )'
    d2rp = st([tworp, drp], 'rpmulcld', '%s e. RR+' % D2); d22rp = st([tworp, d2rp], 'rpmulcld', '%s e. RR+' % D22)
    d4rp = st([d22rp, Urp], 'rpmulcld', '%s e. RR+' % D4)
    g1 = st([bb, st([brp, d4rp, w.inst('logleb')], 'syl2anc', '( B <_ %s <-> ( log ` B ) <_ ( log ` %s ) )' % (D4, D4))], 'mpbid', '( log ` B ) <_ ( log ` %s )' % D4)
    g2a = st([d22rp, Urp, w.inst('relogmul')], 'syl2anc', '( log ` %s ) = ( ( log ` %s ) + ( log ` %s ) )' % (D4, D22, U))
    g2b = st([tworp, d2rp, w.inst('relogmul')], 'syl2anc', '( log ` %s ) = ( ( log ` 2 ) + ( log ` %s ) )' % (D22, D2))
    g2c = st([tworp, drp, w.inst('relogmul')], 'syl2anc', '( log ` %s ) = ( ( log ` 2 ) + %s )' % (D2, Lg))
    eu = '( exp ` U )'
    g3a = st([ur, u0, w.inst('bvefge1p')], 'syl2anc', '%s <_ %s' % (U, eu))
    eurp = st([ur], 'rpefcld', '%s e. RR+' % eu)
    g3c = st([g3a, st([Urp, eurp, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (U, eu, U, eu))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (U, eu))
    g3 = st([g3c, st([ur, w.inst('relogef')], 'syl', '( log ` %s ) = U' % eu)], 'breqtrd', '( log ` %s ) <_ U' % U)
    lg2 = a1(w, a, w.s([], 'log2le1', '( log ` 2 ) < 1'), '( log ` 2 ) < 1')
    pu = st([st([], '1red', '1 e. RR'), lr, ur, u0, lin.linarith(w, a, [l2], '1 <_ %s' % Lg, leaves={Lg: lr})],
            'lemul1ad', '( 1 x. U ) <_ ( %s x. U )' % Lg)
    LV = {Lg: lr, 'U': ur, '( log ` B )': st([brp], 'relogcld', '( log ` B ) e. RR'), '( log ` %s )' % D4: st([d4rp], 'relogcld', '( log ` %s ) e. RR' % D4),
          '( log ` %s )' % D22: st([d22rp], 'relogcld', '( log ` %s ) e. RR' % D22), '( log ` %s )' % D2: st([d2rp], 'relogcld', '( log ` %s ) e. RR' % D2),
          '( log ` %s )' % U: st([Urp], 'relogcld', '( log ` %s ) e. RR' % U),
          '( log ` 2 )': a1(w, a, w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'), '( log ` 2 ) e. RR'),
          '( %s x. U )' % Lg: st([lr, ur], 'remulcld', '( %s x. U ) e. RR' % Lg)}
    fin = lin.linarith(w, a, [g1, g2a, g2b, g2c, lg2, g3, l2, pu, u0], split_imp(S_['gf2els2'])[1], leaves=LV, products=True)
    w.qed([fin], 'idi', S_['gf2els2'])
    return w


RW = '( Re ` W )'
IFE = 'if ( 1 <_ %s , 0 , ( ( 1 - %s ) / 2 ) )' % (RW, RW)
W13 = '( W e. CC /\\ ( ( 1 / ; ; 1 0 0 ) <_ %s /\\ %s <_ ( 3 / ; ; 1 0 0 ) ) )' % (RW, RW)
S_['gf2els4'] = '( %s -> ( ( 1 / ( abs ` ( W - 1 ) ) ) <_ 2 /\\ ( %s e. RR /\\ %s <_ %s ) ) )' % (W13, IFE, IFE, E99)


def gf2els4():
    w = W('gf2els4', 'Helper of ~ gf2lcv : on ` 1/100 <_ Re W <_ 3/100 ` , ` 1 / | W - 1 | <_ 2 ` and the convexity exponent is at most ` 99/200 ` .')
    a = W13; st = mkst(w, a)
    I = '( 1 / ( abs ` ( W - 1 ) ) )'
    wc = proj(w, a, 'W e. CC'); lo = proj(w, a, '( 1 / ; ; 1 0 0 ) <_ %s' % RW); hi = proj(w, a, '%s <_ ( 3 / ; ; 1 0 0 )' % RW)
    rw = st([wc], 'recld', '%s e. RR' % RW)
    one_c = st([], '1cnd', '1 e. CC')
    w1 = st([one_c, wc], 'subcld', '( 1 - W ) e. CC'); wm1 = st([wc, one_c], 'subcld', '( W - 1 ) e. CC')
    LV = {RW: rw, '( Re ` ( 1 - W ) )': st([w1], 'recld', '( Re ` ( 1 - W ) ) e. RR'), '( Re ` 1 )': st([one_c], 'recld', '( Re ` 1 ) e. RR'),
          '( abs ` ( 1 - W ) )': st([w1], 'abscld', '( abs ` ( 1 - W ) ) e. RR'), '( abs ` ( W - 1 ) )': st([wm1], 'abscld', '( abs ` ( W - 1 ) ) e. RR')}
    rs = st([one_c, wc], 'resubd', '( Re ` ( 1 - W ) ) = ( ( Re ` 1 ) - %s )' % RW)
    re1 = a1(w, a, w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
    rl = st([w1], 'releabsd', '( Re ` ( 1 - W ) ) <_ ( abs ` ( 1 - W ) )')
    asb = st([wc, one_c], 'abssubd', '( abs ` ( W - 1 ) ) = ( abs ` ( 1 - W ) )')
    half = lin.linarith(w, a, [rs, re1, hi, rl, asb], '( 1 / 2 ) <_ ( abs ` ( W - 1 ) )', leaves=LV)
    awp = lin.linarith(w, a, [half], '0 < ( abs ` ( W - 1 ) )', leaves=LV)
    lrb = st([st([a1(w, a, num.real(w, '( 1 / 2 )'), '( 1 / 2 ) e. RR'), a1(w, a, num.fact(w, '( 1 / 2 )', 'gt0'), '0 < ( 1 / 2 )')], 'jca', '( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) )'),
              st([LV['( abs ` ( W - 1 ) )'], awp], 'jca', '( ( abs ` ( W - 1 ) ) e. RR /\\ 0 < ( abs ` ( W - 1 ) ) )'), w.inst('lerec')], 'syl2anc',
             '( ( 1 / 2 ) <_ ( abs ` ( W - 1 ) ) <-> %s <_ ( 1 / ( 1 / 2 ) ) )' % I)
    rr2 = a1(w, a, w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0'), w.inst('recrec')], 'mp2an', '( 1 / ( 1 / 2 ) ) = 2'), '( 1 / ( 1 / 2 ) ) = 2')
    hI = st([st([half, lrb], 'mpbid', '%s <_ ( 1 / ( 1 / 2 ) )' % I), rr2], 'breqtrd', '%s <_ 2' % I)
    rlt = lin.linarith(w, a, [hi], '%s < 1' % RW, leaves=LV)
    nle = st([rlt, st([rw, st([], '1red', '1 e. RR')], 'ltnled', '( %s < 1 <-> -. 1 <_ %s )' % (RW, RW))], 'mpbid', '-. 1 <_ %s' % RW)
    if1 = st([nle], 'iffalsed', '%s = ( ( 1 - %s ) / 2 )' % (IFE, RW))
    HR = '( ( 1 - %s ) / 2 )' % RW
    hr = st([st([st([], '1red', '1 e. RR'), rw], 'resubcld', '( 1 - %s ) e. RR' % RW)], 'rehalfcld', '%s e. RR' % HR)
    LV[HR] = hr
    hle = lin.linarith(w, a, [lo], '%s <_ %s' % (HR, E99), leaves={RW: rw})
    ifr = st([if1, hr], 'eqeltrd', '%s e. RR' % IFE)
    ile = st([if1, hle], 'eqbrtrd', '%s <_ %s' % (IFE, E99))
    w.qed([hI, st([ifr, ile], 'jca', '( %s e. RR /\\ %s <_ %s )' % (IFE, IFE, E99))], 'jca', S_['gf2els4'])
    return w


S_['gf2els5'] = '( ( ( ( ( V e. RR /\\ V <_ ( ( ; ; ; ; ; 2 0 0 0 0 0 x. O ) x. ( ( P x. G ) + I ) ) ) /\\ ( ( O e. RR /\\ 0 <_ O ) /\\ O <_ ( C x. F ) ) ) /\\ ( ( C e. RR /\\ F e. RR ) /\\ ( ( P e. RR /\\ 0 <_ P ) /\\ P <_ ( H x. ( 1 + U ) ) ) ) ) /\\ ( ( ( G e. RR /\\ 0 <_ G ) /\\ G <_ ( ( 2 x. L ) x. ( 1 + U ) ) ) /\\ ( ( ( I e. RR /\\ 0 <_ I ) /\\ I <_ 2 ) /\\ ( ( H e. RR /\\ 1 <_ H ) /\\ ( ( L e. RR /\\ 2 <_ L ) /\\ ( U e. RR /\\ 0 <_ U ) ) ) ) ) ) -> V <_ ( ( ( ( ; ; ; ; ; 6 0 0 0 0 0 x. C ) x. ( F x. H ) ) x. L ) x. ( ( 1 + U ) ^ 2 ) ) )'


def gf2els5():
    w = W('gf2els5', 'Helper of ~ gf2lcv : the final algebra, ` 200000 O ( P G + I ) <_ 600000 C F H L ( 1 + U ) ^ 2 ` from ` O <_ C F ` , '
          '` P <_ H ( 1 + U ) ` , ` G <_ 2 L ( 1 + U ) ` , ` I <_ 2 ` , ` 1 <_ H ` , ` 2 <_ L ` (~ z6els5 with ` log D >_ 2 ` ).')
    a = split_imp(S_['gf2els5'])[0]; st = mkst(w, a)
    f = lambda x: proj(w, a, x)
    U = '( 1 + U )'; UU = '( %s x. %s )' % (U, U); HL = '( H x. L )'
    R = lambda x: f('%s e. RR' % x)
    LV = {x: R(x) for x in 'V O C F P G I H L U'.split()}
    Ur = st([st([], '1red', '1 e. RR'), R('U')], 'readdcld', '%s e. RR' % U); u0 = f('0 <_ U')
    U1 = lin.linarith(w, a, [u0], '1 <_ %s' % U, leaves=LV)
    HUr = st([R('H'), Ur], 'remulcld', '( H x. %s ) e. RR' % U)
    L2Ur = st([st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), R('L')], 'remulcld', '( 2 x. L ) e. RR'), Ur], 'remulcld',
              '( ( 2 x. L ) x. %s ) e. RR' % U)
    m1 = st([R('P'), HUr, R('G'), L2Ur, f('0 <_ P'), f('0 <_ G'), f('P <_ ( H x. %s )' % U), f('G <_ ( ( 2 x. L ) x. %s )' % U)], 'lemul12ad',
            '( P x. G ) <_ ( ( H x. %s ) x. ( ( 2 x. L ) x. %s ) )' % (U, U))
    L0 = lin.linarith(w, a, [f('2 <_ L')], '0 <_ L', leaves=LV)
    q1 = st([st([], '1red', '1 e. RR'), R('H'), R('L'), L0, f('1 <_ H')], 'lemul1ad', '( 1 x. L ) <_ %s' % HL)
    HLr = st([R('H'), R('L')], 'remulcld', '%s e. RR' % HL)
    H0 = lin.linarith(w, a, [f('1 <_ H')], '0 <_ H', leaves=LV)
    HL0 = st([R('H'), R('L'), H0, L0], 'mulge0d', '0 <_ %s' % HL)
    UUr = st([Ur, Ur], 'remulcld', '%s e. RR' % UU)
    UU1 = st([st([], '1red', '1 e. RR'), Ur, st([], '1red', '1 e. RR'), Ur, a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), U1, U1],
             'lemul12ad', '( 1 x. 1 ) <_ %s' % UU)
    q2 = st([st([], '1red', '1 e. RR'), UUr, HLr, HL0, lin.linarith(w, a, [UU1], '1 <_ %s' % UU, leaves={UU: UUr})], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (HL, HL, UU))
    LV2 = dict(LV); LV2.update({HL: HLr, UU: UUr, '( %s x. %s )' % (HL, UU): st([HLr, UUr], 'remulcld', '( %s x. %s ) e. RR' % (HL, UU))})
    two = lin.linarith(w, a, [q1, q2, f('2 <_ L')], '2 <_ ( %s x. %s )' % (HL, UU), leaves=LV2, products=True)
    Xe = '( ( P x. G ) + I )'; Y = '( 3 x. ( %s x. %s ) )' % (HL, UU)
    PG = '( ( H x. %s ) x. ( ( 2 x. L ) x. %s ) )' % (U, U)
    LV3 = dict(LV2); LV3.update({'( P x. G )': st([R('P'), R('G')], 'remulcld', '( P x. G ) e. RR'), PG: st([HUr, L2Ur], 'remulcld', '%s e. RR' % PG)})
    e_pg = ringeq(w, a, PG, '( 2 x. ( %s x. %s ) )' % (HL, UU), Closure(w, a, {'H': R('H'), 'L': R('L'), 'U': R('U')}))
    xy = lin.linarith(w, a, [m1, two, f('I <_ 2'), e_pg], '%s <_ %s' % (Xe, Y), leaves=LV3, products=True)
    pg0 = st([R('P'), R('G'), f('0 <_ P'), f('0 <_ G')], 'mulge0d', '0 <_ ( P x. G )')
    Xer = st([LV3['( P x. G )'], R('I')], 'readdcld', '%s e. RR' % Xe)
    Yr = st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), LV2['( %s x. %s )' % (HL, UU)]], 'remulcld', '%s e. RR' % Y)
    Xe0 = lin.linarith(w, a, [pg0, f('0 <_ I')], '0 <_ %s' % Xe, leaves=LV3)
    CF = '( C x. F )'
    m2 = st([R('O'), st([R('C'), R('F')], 'remulcld', '%s e. RR' % CF), Xer, Yr, f('0 <_ O'), Xe0, f('O <_ %s' % CF), xy], 'lemul12ad', '( O x. %s ) <_ ( %s x. %s )' % (Xe, CF, Y))
    vle = f('V <_ ( ( %s x. O ) x. %s )' % (C2, Xe))
    c2r = a1(w, a, num.real(w, C2), '%s e. RR' % C2)
    c20 = a1(w, a, num.ge0_nat(w, 200000), '0 <_ %s' % C2)
    m3 = st([st([R('O'), Xer], 'remulcld', '( O x. %s ) e. RR' % Xe), st([st([R('C'), R('F')], 'remulcld', '%s e. RR' % CF), Yr], 'remulcld', '( %s x. %s ) e. RR' % (CF, Y)), c2r, c20, m2],
            'lemul2ad', '( %s x. ( O x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (C2, Xe, C2, CF, Y))
    as_ = st([st([c2r], 'recnd', '%s e. CC' % C2), st([R('O')], 'recnd', 'O e. CC'), st([Xer], 'recnd', '%s e. CC' % Xe)], 'mulassd',
             '( ( %s x. O ) x. %s ) = ( %s x. ( O x. %s ) )' % (C2, Xe, C2, Xe))
    g1 = st([R('V'), st([st([c2r, R('O')], 'remulcld', '( %s x. O ) e. RR' % C2), Xer], 'remulcld', '( ( %s x. O ) x. %s ) e. RR' % (C2, Xe)),
             st([c2r, st([st([R('C'), R('F')], 'remulcld', '%s e. RR' % CF), Yr], 'remulcld', '( %s x. %s ) e. RR' % (CF, Y))], 'remulcld', '( %s x. ( %s x. %s ) ) e. RR' % (C2, CF, Y)),
             vle, st([as_, m3], 'eqbrtrd', '( ( %s x. O ) x. %s ) <_ ( %s x. ( %s x. %s ) )' % (C2, Xe, C2, CF, Y))], 'letrd', 'V <_ ( %s x. ( %s x. %s ) )' % (C2, CF, Y))
    T1_ = '( ( ( ( %s x. C ) x. ( F x. H ) ) x. L ) x. ( %s ^ 2 ) )' % (C6, U)
    e3 = ringeqp(w, a, T1_, '( %s x. ( %s x. %s ) )' % (C2, CF, Y), Closure(w, a, {x: R(x) for x in 'C F H L U'.split()}))
    w.qed([g1, e3], 'breqtrrd', S_['gf2els5'])
    return w


OMGN = '( 2 ^ ( # ` { p e. Prime | p || N } ) )'
CVXBW = ('( ( %s x. %s ) x. ( ( ( ( N x. ( ( abs ` ( Im ` W ) ) + 2 ) ) ^c %s ) x. ( log ` ( N x. ( ( abs ` ( Im ` W ) ) + 3 ) ) ) ) + ( 1 / ( abs ` ( W - 1 ) ) ) ) )'
         % (C2, OMGN, IFE))
C12 = '; ; ; ; ; ; 1 2 0 0 0 0 0'
D397 = '( D ^c ( ; ; 3 9 7 / ; ; 8 0 0 ) )'
UW = '( abs ` ( ( Im ` W ) - ( Im ` S ) ) )'
KLC = '( ( ( ( %s x. CTau ) x. %s ) x. ( log ` D ) ) x. ( ( 1 + %s ) ^ 2 ) )' % (C12, D397, UW)
HZ2 = '( D e. RR /\\ 1 < D /\\ 2 <_ ( log ` D ) )'
LCH = '( ( ( %s /\\ N e. NN ) /\\ ( S e. CC /\\ ( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ ( 2 x. D ) ) ) /\\ ( %s /\\ ( V e. RR /\\ V <_ %s ) ) )' % (HZ2, W13, CVXBW)
S_['gf2lcv'] = '( %s -> V <_ %s )' % (LCH, KLC)


def ctre(w, a):
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    c = w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )'),
             w.s([w.s([], '2re', '2 e. RR'), w.s([knn], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('reexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. RR')],
            'eqeltri', 'CTau e. RR')
    return a1(w, a, c, 'CTau e. RR')


def gf2lcv():
    w = W('gf2lcv', 'The convexity bound on the left contour (Lean ` norm_LFunction_left_line_le ` , generic in the value): a real ` V ` below '
          'I1 at ` W ` , ` 1/100 <_ Re W <_ 3/100 ` , is at most ` 1200000 C_tau D ^ ( 397/800 ) log D ( 1 + | Im W - Im S | ) ^ 2 ` when '
          '` N ( | Im S | + 2 ) <_ 2 D ` , ` log D >_ 2 ` (~ z6els1 , ~ z6els3 at ` 2 D ` , ~ gf2els2 , ~ gf2els4 , ~ gf2els5 , ~ z6omgd ).')
    a = LCH; st = mkst(w, a)
    f = lambda x: proj(w, a, x)
    IW = '( Im ` W )'; IS = '( Im ` S )'
    T = '( abs ` %s )' % IW; AA = '( abs ` %s )' % IS; U = UW
    A_ = '( N x. ( %s + 2 ) )' % T; B_ = '( N x. ( %s + 3 ) )' % T
    nn = f('N e. NN'); sc = f('S e. CC'); wc = f('W e. CC'); dr = f('D e. RR'); d1 = f('1 < D'); l2 = f('2 <_ ( log ` D )')
    iwc = st([st([wc], 'imcld', '%s e. RR' % IW)], 'recnd', '%s e. CC' % IW)
    isc = st([st([sc], 'imcld', '%s e. RR' % IS)], 'recnd', '%s e. CC' % IS)
    dfc = st([iwc, isc], 'subcld', '( %s - %s ) e. CC' % (IW, IS))
    R = {}; G0 = {}
    for x, c_ in ((T, iwc), (AA, isc), (U, dfc)):
        R[x] = st([c_], 'abscld', '%s e. RR' % x); G0[x] = st([c_], 'absge0d', '0 <_ %s' % x)
    tau = st([iwc, isc], 'abs2difd', '( %s - %s ) <_ %s' % (T, AA, U))
    n0 = st([st([nn], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N'); nr = st([nn], 'nnred', 'N e. RR')
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    D2 = '( 2 x. D )'
    d2r = st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), dr], 'remulcld', '%s e. RR' % D2)
    hs = f('( N x. ( %s + 2 ) ) <_ %s' % (AA, D2))
    e1 = st([st([st([nn, d2r], 'jca', '( N e. NN /\\ %s e. RR )' % D2),
                 st([st([R[T], G0[T]], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (T, T)), st([R[AA], G0[AA]], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (AA, AA)),
                     st([R[U], G0[U]], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (U, U))], '3jca',
                    '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (T, T, AA, AA, U, U)),
                 st([tau, hs], 'jca', '( ( %s - %s ) <_ %s /\\ ( N x. ( %s + 2 ) ) <_ %s )' % (T, AA, U, AA, D2))], '3jca',
                tsub(split_imp(L1S)[0], {'D': D2, 'T': T, 'A': AA, 'U': U})), w.inst('z6els1')], 'syl',
            '( %s <_ ( %s x. ( 1 + %s ) ) /\\ %s <_ ( ( 2 x. %s ) x. ( 1 + %s ) ) )' % (A_, D2, U, B_, D2, U))
    a1b = st([e1], 'simpld', '%s <_ ( %s x. ( 1 + %s ) )' % (A_, D2, U))
    b1b = st([e1], 'simprd', '%s <_ ( ( 2 x. %s ) x. ( 1 + %s ) )' % (B_, D2, U))
    T2 = '( %s + 2 )' % T; T3 = '( %s + 3 )' % T
    t2r = st([R[T], a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR')], 'readdcld', '%s e. RR' % T2)
    t3r = st([R[T], a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'readdcld', '%s e. RR' % T3)
    ar_ = st([nr, t2r], 'remulcld', '%s e. RR' % A_)
    a1_ = st([st([st([], '1red', '1 e. RR'), nr, st([], '1red', '1 e. RR'), t2r, a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'),
                  st([nn], 'nnge1d', '1 <_ N'), lin.linarith(w, a, [G0[T]], '1 <_ %s' % T2, leaves={T: R[T]})], 'lemul12ad', '( 1 x. 1 ) <_ %s' % A_),
              a1(w, a, w.s([], '1t1e1', '( 1 x. 1 ) = 1'), '( 1 x. 1 ) = 1')], 'eqbrtrrd', '1 <_ %s' % A_)
    a0_ = lin.linarith(w, a, [a1_], '0 <_ %s' % A_, leaves={A_: ar_})
    d21 = lin.linarith(w, a, [d1], '1 <_ ( 2 x. D )', leaves={'D': dr})
    e3 = st([st([d2r, d21], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (D2, D2)), st([R[U], G0[U]], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (U, U)),
             st([st([ar_, a0_], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (A_, A_)), a1b], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ %s <_ ( %s x. ( 1 + %s ) ) )' % (A_, A_, A_, D2, U)),
             w.inst('z6els3')], 'syl3anc', '( ( %s ^c %s ) <_ ( ( %s ^c %s ) x. ( 1 + %s ) ) /\\ 1 <_ ( %s ^c %s ) )' % (A_, E99, D2, E99, U, D2, E99))
    H = '( %s ^c %s )' % (D2, E99)
    pe99 = st([e3], 'simpld', '( %s ^c %s ) <_ ( %s x. ( 1 + %s ) )' % (A_, E99, H, U)); h1 = st([e3], 'simprd', '1 <_ %s' % H)
    br_ = st([nr, t3r], 'remulcld', '%s e. RR' % B_)
    b0p = st([st([nn], 'nnrpd', 'N e. RR+'), st([t3r, lin.linarith(w, a, [G0[T]], '0 < %s' % T3, leaves={T: R[T]})], 'elrpd', '%s e. RR+' % T3)], 'rpmulcld', '%s e. RR+' % B_)
    e2 = st([st([drp, l2], 'jca', '( D e. RR+ /\\ 2 <_ ( log ` D ) )'), st([R[U], G0[U]], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (U, U)),
             st([b0p, b1b], 'jca', '( %s e. RR+ /\\ %s <_ ( ( 2 x. %s ) x. ( 1 + %s ) ) )' % (B_, B_, D2, U)), w.inst('gf2els2')], 'syl3anc',
            '( log ` %s ) <_ ( ( 2 x. ( log ` D ) ) x. ( 1 + %s ) )' % (B_, U))
    e4 = st([proj(w, a, W13), w.inst('gf2els4')], 'syl', split_imp(S_['gf2els4'])[1])
    i2 = st([e4], 'simpld', '( 1 / ( abs ` ( W - 1 ) ) ) <_ 2')
    ifr = st([e4], 'simprld', '%s e. RR' % IFE); ile = st([e4], 'simprrd', '%s <_ %s' % (IFE, E99))
    PE = '( %s ^c %s )' % (A_, IFE)
    e99r = a1(w, a, num.real(w, E99), '%s e. RR' % E99)
    pl = st([st([ar_, a1_], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (A_, A_)), st([ifr, e99r], 'jca', '( %s e. RR /\\ %s e. RR )' % (IFE, E99)), ile, w.inst('cxplea')], 'syl3anc',
            '%s <_ ( %s ^c %s )' % (PE, A_, E99))
    per = st([ar_, a0_, ifr], 'recxpcld', '%s e. RR' % PE); pe0 = st([ar_, a0_, ifr], 'cxpge0d', '0 <_ %s' % PE)
    hr = st([d2r, lin.linarith(w, a, [d1], '0 <_ ( 2 x. D )', leaves={'D': dr}), e99r], 'recxpcld', '%s e. RR' % H)
    pb = st([per, st([ar_, a0_, e99r], 'recxpcld', '( %s ^c %s ) e. RR' % (A_, E99)), st([hr, st([st([], '1red', '1 e. RR'), R[U]], 'readdcld', '( 1 + %s ) e. RR' % U)], 'remulcld',
                                                                                         '( %s x. ( 1 + %s ) ) e. RR' % (H, U)), pl, pe99], 'letrd', '%s <_ ( %s x. ( 1 + %s ) )' % (PE, H, U))
    # omega
    nd = lin.linarith(w, a, [hs, st([nr, R[AA], n0, G0[AA]], 'mulge0d', '0 <_ ( N x. %s )' % AA), n0], 'N <_ D',
                      leaves={'N': nr, 'D': dr, AA: R[AA], '( N x. %s )' % AA: st([nr, R[AA]], 'remulcld', '( N x. %s ) e. RR' % AA)}, products=True)
    om = st([nn, st([dr, nd], 'jca', '( D e. RR /\\ N <_ D )'), w.inst('z6omgd')], 'syl2anc', '%s <_ ( CTau x. ( D ^c ( 1 / ; ; 8 0 0 ) ) )' % OMGN)
    F8 = '( D ^c ( 1 / ; ; 8 0 0 ) )'
    d0 = st([drp], 'rpge0d', '0 <_ D')
    f8r = st([dr, d0, a1(w, a, num.real(w, '( 1 / ; ; 8 0 0 )'), '( 1 / ; ; 8 0 0 ) e. RR')], 'recxpcld', '%s e. RR' % F8)
    f80 = st([dr, d0, a1(w, a, num.real(w, '( 1 / ; ; 8 0 0 )'), '( 1 / ; ; 8 0 0 ) e. RR')], 'cxpge0d', '0 <_ %s' % F8)
    ct = ctre(w, a)
    from gf2_s import OMGN as _OM
    from z6b_m import omgfacts
    omr, om1 = omgfacts(w, a, nn)
    om0 = lin.linarith(w, a, [om1], '0 <_ %s' % OMGN, leaves={OMGN: omr})
    Lg = '( log ` D )'
    lr = st([drp], 'relogcld', '%s e. RR' % Lg)
    Gl = '( log ` %s )' % B_
    glr = st([b0p], 'relogcld', '%s e. RR' % Gl)
    b1_ = st([st([st([], '1red', '1 e. RR'), nr, st([], '1red', '1 e. RR'), t3r, a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), a1(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'),
                  st([nn], 'nnge1d', '1 <_ N'), lin.linarith(w, a, [G0[T]], '1 <_ %s' % T3, leaves={T: R[T]})], 'lemul12ad', '( 1 x. 1 ) <_ %s' % B_),
              a1(w, a, w.s([], '1t1e1', '( 1 x. 1 ) = 1'), '( 1 x. 1 ) = 1')], 'eqbrtrrd', '1 <_ %s' % B_)
    gl0 = st([br_, b1_, w.inst('logge0')], 'syl2anc', '0 <_ %s' % Gl)
    I_ = '( 1 / ( abs ` ( W - 1 ) ) )'
    one_c = st([], '1cnd', '1 e. CC')
    wm1 = st([wc, one_c], 'subcld', '( W - 1 ) e. CC')
    rw_ = st([wc], 'recld', '( Re ` W ) e. RR')
    rlt = lin.linarith(w, a, [f('( Re ` W ) <_ ( 3 / ; ; 1 0 0 )')], '( Re ` W ) < 1', leaves={'( Re ` W )': rw_})
    fv1 = w.s([w.s([], 'fveq2', '( W = 1 -> ( Re ` W ) = ( Re ` 1 ) )'), w.s([], 're1', '( Re ` 1 ) = 1')], 'eqtrdi', '( W = 1 -> ( Re ` W ) = 1 )')
    wn1 = st([st([rw_, rlt], 'ltned', '( Re ` W ) =/= 1'), w.s([fv1], 'necon3i', '( ( Re ` W ) =/= 1 -> W =/= 1 )')], 'syl', 'W =/= 1')
    awp = st([wm1, st([wc, one_c, wn1], 'subne0d', '( W - 1 ) =/= 0'), w.inst('absrpcl')], 'syl2anc', '( abs ` ( W - 1 ) ) e. RR+')
    ir = st([awp], 'rprecred', '%s e. RR' % I_); i0 = st([st([awp], 'rpreccld', '%s e. RR+' % I_)], 'rpge0d', '0 <_ %s' % I_)
    Ux = '( 1 + %s )' % U
    fct = {'V e. RR': f('V e. RR'), 'V <_ %s' % CVXBW: f('V <_ %s' % CVXBW), '%s e. RR' % OMGN: omr, '0 <_ %s' % OMGN: om0,
           '%s <_ ( CTau x. %s )' % (OMGN, F8): om, 'CTau e. RR': ct, '%s e. RR' % F8: f8r, '%s e. RR' % PE: per, '0 <_ %s' % PE: pe0,
           '%s <_ ( %s x. %s )' % (PE, H, Ux): pb, '%s e. RR' % Gl: glr, '0 <_ %s' % Gl: gl0, '%s <_ ( ( 2 x. %s ) x. %s )' % (Gl, Lg, Ux): e2,
           '%s e. RR' % I_: ir, '0 <_ %s' % I_: i0, '%s <_ 2' % I_: i2, '%s e. RR' % H: hr, '1 <_ %s' % H: h1, '%s e. RR' % Lg: lr, '2 <_ %s' % Lg: l2,
           '%s e. RR' % U: R[U], '0 <_ %s' % U: G0[U]}
    subs = {'O': OMGN, 'C': 'CTau', 'F': F8, 'P': PE, 'G': Gl, 'I': I_, 'H': H, 'L': Lg, 'U': U}
    e5 = st([build(w, a, tsub(split_imp(S_['gf2els5'])[0], subs), fct), w.inst('gf2els5')], 'syl', tsub(split_imp(S_['gf2els5'])[1], subs))
    # ( 2 D ) ^ ( 99/200 ) <_ 2 D ^ ( 99/200 )
    D99 = '( D ^c %s )' % E99
    two0 = a1(w, a, w.s([], '0le2', '0 <_ 2'), '0 <_ 2'); two_r = a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR')
    hm = st([two_r, two0, dr, d0, st([e99r], 'recnd', '%s e. CC' % E99)], 'mulcxpd', '%s = ( ( 2 ^c %s ) x. %s )' % (H, E99, D99))
    t99 = st([st([two_r, a1(w, a, w.s([], '1le2', '1 <_ 2'), '1 <_ 2')], 'jca', '( 2 e. RR /\\ 1 <_ 2 )'), st([e99r, st([], '1red', '1 e. RR')], 'jca', '( %s e. RR /\\ 1 e. RR )' % E99),
              lin.linarith(w, a, [], '%s <_ 1' % E99), w.inst('cxplea')], 'syl3anc', '( 2 ^c %s ) <_ ( 2 ^c 1 )' % E99)
    t991 = st([t99, st([st([], '2cnd', '2 e. CC')], 'cxp1d', '( 2 ^c 1 ) = 2')], 'breqtrd', '( 2 ^c %s ) <_ 2' % E99)
    d99r = st([dr, d0, e99r], 'recxpcld', '%s e. RR' % D99); d990 = st([dr, d0, e99r], 'cxpge0d', '0 <_ %s' % D99)
    t2r_ = st([two_r, two0, e99r], 'recxpcld', '( 2 ^c %s ) e. RR' % E99)
    hb = st([hm, st([t2r_, two_r, d99r, d990, t991], 'lemul1ad', '( ( 2 ^c %s ) x. %s ) <_ ( 2 x. %s )' % (E99, D99, D99))], 'eqbrtrd', '%s <_ ( 2 x. %s )' % (H, D99))
    fh = st([hr, st([two_r, d99r], 'remulcld', '( 2 x. %s ) e. RR' % D99), f8r, f80, hb], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 2 x. %s ) )' % (F8, H, F8, D99))
    # D ^ ( 1/800 ) D ^ ( 99/200 ) = D ^ ( 397/800 )
    ad = st([st([dr], 'recnd', 'D e. CC'), st([drp], 'rpne0d', 'D =/= 0'), a1(w, a, num.cc(w, '( 1 / ; ; 8 0 0 )'), '( 1 / ; ; 8 0 0 ) e. CC'), st([e99r], 'recnd', '%s e. CC' % E99)],
            'cxpaddd', '( D ^c ( ( 1 / ; ; 8 0 0 ) + %s ) ) = ( %s x. %s )' % (E99, F8, D99))
    ex_ = ringeq(w, a, '( ( 1 / ; ; 8 0 0 ) + %s )' % E99, '( ; ; 3 9 7 / ; ; 8 0 0 )', Closure(w, a, {}))
    d397 = st([st([ex_], 'oveq2d', '( D ^c ( ( 1 / ; ; 8 0 0 ) + %s ) ) = %s' % (E99, D397)), ad], 'eqtr3d', '%s = ( %s x. %s )' % (D397, F8, D99))
    # scale by ( C6 CTau ) , L , ( 1 + U ) ^ 2
    c6c = st([a1(w, a, num.real(w, C6), '%s e. RR' % C6), ct], 'remulcld', '( %s x. CTau ) e. RR' % C6)
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    cg0 = w.s([w.s([], '2re', '2 e. RR'), w.s([knn], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.s([], '0le2', '0 <_ 2'), w.inst('expge0')], 'mp3an', '0 <_ ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')
    ct0 = a1(w, a, w.s([cg0, w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')], 'breqtrri', '0 <_ CTau'), '0 <_ CTau')
    C6C = '( %s x. CTau )' % C6
    c6c0 = st([a1(w, a, num.real(w, C6), '%s e. RR' % C6), ct, a1(w, a, num.ge0_nat(w, 600000), '0 <_ %s' % C6), ct0], 'mulge0d', '0 <_ %s' % C6C)
    FH = '( %s x. %s )' % (F8, H); F2D = '( %s x. ( 2 x. %s ) )' % (F8, D99)
    fhr = st([f8r, hr], 'remulcld', '%s e. RR' % FH); f2dr = st([f8r, st([two_r, d99r], 'remulcld', '( 2 x. %s ) e. RR' % D99)], 'remulcld', '%s e. RR' % F2D)
    m1 = st([fhr, f2dr, c6c, c6c0, fh], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (C6C, FH, C6C, F2D))
    l0 = lin.linarith(w, a, [l2], '0 <_ %s' % Lg, leaves={Lg: lr})
    X1 = '( %s x. %s )' % (C6C, FH); Y1 = '( %s x. %s )' % (C6C, F2D)
    x1r = st([c6c, fhr], 'remulcld', '%s e. RR' % X1); y1r = st([c6c, f2dr], 'remulcld', '%s e. RR' % Y1)
    m2 = st([x1r, y1r, lr, l0, m1], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (X1, Lg, Y1, Lg))
    U2 = '( ( 1 + %s ) ^ 2 )' % U
    u1r = st([st([], '1red', '1 e. RR'), R[U]], 'readdcld', '( 1 + %s ) e. RR' % U)
    u2r = st([u1r], 'resqcld', '%s e. RR' % U2); u20 = st([u1r], 'sqge0d', '0 <_ %s' % U2)
    X2 = '( %s x. %s )' % (X1, Lg); Y2 = '( %s x. %s )' % (Y1, Lg)
    m3 = st([st([x1r, lr], 'remulcld', '%s e. RR' % X2), st([y1r, lr], 'remulcld', '%s e. RR' % Y2), u2r, u20, m2], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (X2, U2, Y2, U2))
    vb = st([f('V e. RR'), st([st([x1r, lr], 'remulcld', '%s e. RR' % X2), u2r], 'remulcld', '( %s x. %s ) e. RR' % (X2, U2)),
             st([st([y1r, lr], 'remulcld', '%s e. RR' % Y2), u2r], 'remulcld', '( %s x. %s ) e. RR' % (Y2, U2)), e5, m3], 'letrd', 'V <_ ( %s x. %s )' % (Y2, U2))
    KLD = '( ( ( ( %s x. CTau ) x. ( %s x. %s ) ) x. %s ) x. %s )' % (C12, F8, D99, Lg, U2)
    kq = st([st([st([st([d397], 'oveq2d', '( ( %s x. CTau ) x. %s ) = ( ( %s x. CTau ) x. ( %s x. %s ) )' % (C12, D397, C12, F8, D99))], 'oveq1d',
                    '( ( ( %s x. CTau ) x. %s ) x. %s ) = ( ( ( %s x. CTau ) x. ( %s x. %s ) ) x. %s )' % (C12, D397, Lg, C12, F8, D99, Lg))], 'oveq1d', '%s = %s' % (KLC, KLD))], 'eqcomd',
            '%s = %s' % (KLD, KLC))
    rq = ringeq(w, a, '( %s x. %s )' % (Y2, U2), KLD, Closure(w, a, {'CTau': ct, F8: f8r, D99: d99r, Lg: lr, U2: u2r}))
    fin = st([vb, st([rq, kq], 'eqtrd', '( %s x. %s ) = %s' % (Y2, U2, KLC))], 'breqtrd', 'V <_ %s' % KLC)
    w.qed([fin], 'idi', S_['gf2lcv'])
    return w


import gf2_s as GS
HMB = '( ( CTau ^ 2 ) x. ( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) )'
EAC = '( exp ` ( A x. %s ) )' % GS.CLL
KLP = '( ( ( 2 x. %s ) x. %s ) x. ( ( ( %s x. CTau ) x. %s ) x. ( log ` D ) ) )' % (EAC, HMB, C12, D397)
ZL = '( %s + ( _i x. u ) )' % GS.CLL
FRZ = '( ( %s /\\ ( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ ( 2 x. D ) ) /\\ A <_ B )' % HZ2
LPH = '( ( %s /\\ %s ) /\\ u e. RR )' % (GS.MSH, FRZ)
S_['gf2lpt'] = ('( ( ( %s /\\ %s ) /\\ ( Z e. CC /\\ ( Re ` Z ) = %s ) ) -> ( abs ` ( %s ` Z ) ) <_ ( %s x. ( ( abs ` ( _G ` Z ) ) x. '
                '( ( 1 + ( abs ` ( Im ` Z ) ) ) ^ 2 ) ) ) )') % (GS.MSH, FRZ, GS.CLL, GS.GI, KLP)


def gf2lpt():
    w = W('gf2lpt', 'The integrand on the left line ` Re w = -99/100 ` (Lean ` norm_gramInt_left_le ` ): ` | GI ( Z ) | <_ KL | Gamma ( Z ) | ( 1 + | Im Z | ) ^ 2 ` , '
          '` KL = 2 e ^ ( -99/100 A ) CTau ^ 2 R ^ ( 801/400 ) 1200000 CTau D ^ ( 397/800 ) log D ` (~ gf1kb , ~ gf1mhb , ~ gf1hm , ~ gf2lcv ).')
    a = split_imp(S_['gf2lpt'])[0]; c = a; st = mkst(w, a); t = st
    P_ = lambda x: proj(w, a, x)
    zc = P_('Z e. CC'); rz = P_('( Re ` Z ) = %s' % GS.CLL)
    sc = P_('S e. CC'); s0 = P_('0 <_ ( Re ` S )'); s1 = P_('( Re ` S ) <_ ( 1 / ; 5 0 )')
    rs = st([sc], 'recld', '( Re ` S ) e. RR'); rzr = st([zc], 'recld', '( Re ` Z ) e. RR')
    L_ = {'( Re ` S )': rs, '( Re ` Z )': rzr}
    lin_ = lambda hyps, goal, lv=None: lin.linarith(w, a, hyps, goal, leaves=lv or L_)
    c99 = litr(w, a, GS.CLL)
    cl_ = st([c99, st([rz], 'eqcomd', '%s = ( Re ` Z )' % GS.CLL)], 'eqled', '%s <_ ( Re ` Z )' % GS.CLL)
    # Z e. DI (gf2grsd with Re Z = CLL), Z =/= 0 , Z =/= -u S
    gsd = st([P_(GS.GSH), w.inst('gf2grsd')], 'syl', 'A. z e. CC %s' % GS.STRD)
    idz = w.s([], 'id', '( z = Z -> z = Z )')
    bstz, vstz = w.wcongr(GS.STRD, {'z': 'Z'}, 'z = Z', {'z': idz})
    inst = st([bstz, gsd, zc], 'rspcdva', vstz)
    Hp = split_imp(GS.STRD)[0]
    hp = st([st([cl_, lin_([rz], '( Re ` Z ) <_ 1')], 'jca', '( %s <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 1 )' % GS.CLL),
             st([st([rz], 'orcd', '( ( Re ` Z ) = %s \\/ ( Re ` Z ) = 1 )' % GS.CLL)], 'orcd', '( ( ( Re ` Z ) = %s \\/ ( Re ` Z ) = 1 ) \\/ %s <_ ( abs ` ( Im ` Z ) ) )' % (GS.CLL, GS.YS))],
            'jca', split_imp(vstz)[0])
    zdi = st([hp, inst], 'mpd', 'Z e. %s' % GS.DI)
    nsn = st([zdi], 'eldifbd', '-. Z e. { -u S }')
    zns = st([st([nsn, st([zc, w.inst('elsng')], 'syl', '( Z e. { -u S } <-> Z = -u S )')], 'mtbid', '-. Z = -u S')], 'neqned', 'Z =/= -u S')
    c2 = '( %s /\\ Z = 0 )' % a; t2 = mkst(w, c2)
    r00 = t2([t2([t2([], 'simpr', 'Z = 0')], 'fveq2d', '( Re ` Z ) = ( Re ` 0 )'), a1(w, c2, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')], 'eqtrd', '( Re ` Z ) = 0')
    rn0 = st([st([st([lin_([rz], '( Re ` Z ) < 0')], 'ltned', '( Re ` Z ) =/= 0')], 'idi', '( Re ` Z ) =/= 0')], 'neneqd', '-. ( Re ` Z ) = 0')
    z0n = st([w.s([r00, lift(w, rn0, c2)], 'pm2.65da', '( %s -> -. Z = 0 )' % a)], 'neqned', 'Z =/= 0')
    zlo1 = lin_([rz], '-u 1 < ( Re ` Z )')
    # the value of GS.GI and its factorization
    gv, _ = mpv(w, c, 'w', GS.DI, GS.GIB('w'), 'Z', zdi)
    AR = ( proj(w, c, 'A e. RR'), proj(w, c, 'B e. RR'), proj(w, c, 'L e. RR+') )
    g1v = t([t([t([AR[0], AR[1]], 'jca', '( A e. RR /\\ B e. RR )'), AR[2]], 'jca', '( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ )'),
             t([zc, zlo1, z0n], '3jca', '( Z e. CC /\\ -u 1 < ( Re ` Z ) /\\ Z =/= 0 )'), w.inst('gf1g1v')], 'syl2anc', '%s = ( ( _G ` Z ) x. %s )' % (GS.G1w('Z'), G1L.KK('A', 'B', 'L', 'Z')))
    W_ = GS.SP % 'Z'
    Gz = '( _G ` Z )'; Kz = G1L.KK('A', 'B', 'L', 'Z'); Mz = GS.MHs(W_); Ez = '( E ` %s )' % W_; Dn = '( %s - 1 )' % W_
    Qz = '( %s / %s )' % (Ez, Dn)
    c1_ = t([t([], '1cnd', '1 e. CC'), sc], 'addcld', '( 1 + S ) e. CC')
    wc = t([c1_, zc], 'addcld', '%s e. CC' % W_)
    dq = ringeq(w, c, '( Z - -u S )', Dn, Closure(w, c, {'S': sc, 'Z': zc}))
    dn0 = t([dq, t([zc, t([sc], 'negcld', '-u S e. CC'), zns], 'subne0d', '( Z - -u S ) =/= 0')], 'eqnetrrd', '%s =/= 0' % Dn)
    dnc = t([wc, t([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % Dn)
    zdg = t([t([zc, t([zlo1, z0n], 'jca', '( -u 1 < ( Re ` Z ) /\\ Z =/= 0 )')], 'jca', '( Z e. CC /\\ ( -u 1 < ( Re ` Z ) /\\ Z =/= 0 ) )'), w.inst('z6rdg')], 'syl',
             'Z e. ( CC \\ ( ZZ \\ NN ) )')
    gc = t([zdg, w.inst('gamcl')], 'syl', '%s e. CC' % Gz)
    rsz = t([c1_, zc], 'readdd', '( Re ` %s ) = ( ( Re ` ( 1 + S ) ) + ( Re ` Z ) )' % W_)
    r2 = t([t([t([], '1cnd', '1 e. CC'), sc], 'readdd', '( Re ` ( 1 + S ) ) = ( ( Re ` 1 ) + ( Re ` S ) )'),
            t([a1(w, c, w.s([w.s([], '1re', '1 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'oveq1d', '( ( Re ` 1 ) + ( Re ` S ) ) = ( 1 + ( Re ` S ) )')],
           'eqtrd', '( Re ` ( 1 + S ) ) = ( 1 + ( Re ` S ) )')
    rw_ = t([rsz, t([r2], 'oveq1d', '( ( Re ` ( 1 + S ) ) + ( Re ` Z ) ) = ( ( 1 + ( Re ` S ) ) + ( Re ` Z ) )')], 'eqtrd', '( Re ` %s ) = ( ( 1 + ( Re ` S ) ) + ( Re ` Z ) )' % W_)
    rwr = t([wc], 'recld', '( Re ` %s ) e. RR' % W_)
    L3 = dict(L_); L3['( Re ` %s )' % W_] = rwr
    w0 = lin_([rw_, s0, cl_], '0 <_ ( Re ` %s )' % W_, L3)
    w100 = lin_([rw_, s0, cl_], '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W_, L3)
    # E ( W ) e. CC : W e. GS.HPZ
    wpos = lin_([rw_, s0, cl_], '0 < ( Re ` %s )' % W_, L3)
    whz = t([t([wc, wpos], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), t([t([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl',
                                                                                       '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (W_, GS.HPZ, W_, W_))], 'mpbird', '%s e. %s' % (W_, GS.HPZ))
    ecn = proj(w, c, 'E e. ( %s -cn-> CC )' % GS.HPZ)
    ezc = t([t([ecn, w.inst('cncff')], 'syl', 'E : %s --> CC' % GS.HPZ), whz], 'ffvelcdmd', '%s e. CC' % Ez)
    qc = t([ezc, dnc, dn0], 'divcld', '%s e. CC' % Qz)
    # MH bound (gf1mhb, with the k-binder)
    cbj = proj(w, c, GS.CBj)
    idjk = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( C ` j ) = ( C ` k ) )')], 'fveq2d', '( j = k -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` k ) ) )')], 'breq1d',
               '( j = k -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` k ) ) <_ 1 ) )')
    CBk = 'A. k e. NN ( abs ` ( C ` k ) ) <_ 1'
    cbk = t([cbj, w.s([idjk], 'cbvralvw', '( %s <-> %s )' % (GS.CBj, CBk))], 'sylib', CBk)
    mhb = t([t([P_('N e. NN'), P_('R e. RR')], 'jca', '( N e. NN /\\ R e. RR )'), t([P_('C : NN --> CC'), cbk], 'jca', '( C : NN --> CC /\\ %s )' % CBk),
             t([wc, w0], 'jca', '( %s e. CC /\\ 0 <_ ( Re ` %s ) )' % (W_, W_)), w.inst('gf1mhb')], 'syl3anc', '( %s e. CC /\\ ( abs ` %s ) <_ %s )' % (Mz, Mz, GS.HMNR))
    mzc = t([mhb], 'simpld', '%s e. CC' % Mz); mb = t([mhb], 'simprd', '( abs ` %s ) <_ %s' % (Mz, GS.HMNR))
    import gf2_a as GA_
    kzc = GA_.kkcc(w, a, {'A e. RR': AR[0], 'B e. RR': AR[1], 'L e. RR+': AR[2]}, zc, 'Z')
    # algebra: GS.GIB ( Z ) = ( Gz Kz ) ( Qz Mz )
    HB_ = GS.HFB('Z')
    e1 = t([t([t([g1v], 'oveq1d', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (GS.G1w('Z'), Mz, Ez, Gz, Kz, Mz, Ez))], 'oveq1d',
              '( %s / ( Z - -u S ) ) = ( ( ( %s x. %s ) x. ( %s x. %s ) ) / ( Z - -u S ) )' % (HB_, Gz, Kz, Mz, Ez)),
            t([dq], 'oveq2d', '( ( ( %s x. %s ) x. ( %s x. %s ) ) / ( Z - -u S ) ) = ( ( ( %s x. %s ) x. ( %s x. %s ) ) / %s )' % (Gz, Kz, Mz, Ez, Gz, Kz, Mz, Ez, Dn))], 'eqtrd',
           '%s = ( ( ( %s x. %s ) x. ( %s x. %s ) ) / %s )' % (GS.GIB('Z'), Gz, Kz, Mz, Ez, Dn))
    GK = '( %s x. %s )' % (Gz, Kz); ME = '( %s x. %s )' % (Mz, Ez)
    gkc = t([gc, kzc], 'mulcld', '%s e. CC' % GK); mec = t([mzc, ezc], 'mulcld', '%s e. CC' % ME)
    e2 = t([gkc, mec, dnc, dn0], 'divassd', '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (GK, ME, Dn, GK, ME, Dn))
    e3 = t([mzc, ezc, dnc, dn0], 'divassd', '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (Mz, Ez, Dn, Mz, Ez, Dn))
    e4 = t([mzc, qc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (Mz, Qz, Qz, Mz))
    QM = '( %s x. %s )' % (Qz, Mz)
    e34 = t([e3, e4], 'eqtrd', '( %s / %s ) = %s' % (ME, Dn, QM))
    gval = t([t([e1, e2], 'eqtrd', '%s = ( %s x. ( %s / %s ) )' % (GS.GIB('Z'), GK, ME, Dn)), t([e34], 'oveq2d', '( %s x. ( %s / %s ) ) = ( %s x. %s )' % (GK, ME, Dn, GK, QM))], 'eqtrd',
             '%s = ( %s x. %s )' % (GS.GIB('Z'), GK, QM))
    PROD = '( ( ( abs ` %s ) x. ( abs ` %s ) ) x. ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Gz, Kz, Qz, Mz)
    ab = t([t([gkc, t([qc, mzc], 'mulcld', '%s e. CC' % QM)], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GK, QM, GK, QM)),
            t([t([gc, kzc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GK, Gz, Kz)), t([qc, mzc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (QM, Qz, Mz))],
              'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = %s' % (GK, QM, PROD))], 'eqtrd', '( abs ` ( %s x. %s ) ) = %s' % (GK, QM, PROD))
    agr = t([t([t([gv, gval], 'eqtrd', '( %s ` Z ) = ( %s x. %s )' % (GS.GI, GK, QM))], 'fveq2d', '( abs ` ( %s ` Z ) ) = ( abs ` ( %s x. %s ) )' % (GS.GI, GK, QM)), ab], 'eqtrd',
            '( abs ` ( %s ` Z ) ) = %s' % (GS.GI, PROD))
    # KK bound on Re Z <_ 0: e^( B Re Z ) + e^( A Re Z ) <_ 2 e^( A CLL )
    kb0 = st([st([st([st([AR[0], AR[1]], 'jca', '( A e. RR /\\ B e. RR )'), st([P_('0 <_ A'), P_('0 <_ B')], 'jca', '( 0 <_ A /\\ 0 <_ B )')], 'jca',
                     '( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) )'), AR[2], zc, w.inst('gf1kb')], 'syl3anc', tsub(split_imp(G1L.S['gf1kb'])[1], {'W': 'Z'}))],
             'simpld', '( ( Re ` Z ) <_ 0 -> ( ( abs ` %s ) <_ ( ( exp ` ( B x. ( Re ` Z ) ) ) + ( exp ` ( A x. ( Re ` Z ) ) ) ) /\\ ( abs ` %s ) <_ 2 /\\ ( ( abs ` %s ) x. ( L x. ( abs ` Z ) ) ) <_ 4 ) )'
             % (Kz, Kz, Kz))
    kb1 = st([st([lin_([rz], '( Re ` Z ) <_ 0'), kb0], 'mpd', '( ( abs ` %s ) <_ ( ( exp ` ( B x. ( Re ` Z ) ) ) + ( exp ` ( A x. ( Re ` Z ) ) ) ) /\\ ( abs ` %s ) <_ 2 /\\ ( ( abs ` %s ) x. ( L x. ( abs ` Z ) ) ) <_ 4 )' % (Kz, Kz, Kz))],
             'simp1d', '( abs ` %s ) <_ ( ( exp ` ( B x. ( Re ` Z ) ) ) + ( exp ` ( A x. ( Re ` Z ) ) ) )' % Kz)
    EB = '( exp ` ( B x. %s ) )' % GS.CLL
    kb2 = st([kb1, st([st([st([rz], 'oveq2d', '( B x. ( Re ` Z ) ) = ( B x. %s )' % GS.CLL)], 'fveq2d', '( exp ` ( B x. ( Re ` Z ) ) ) = %s' % EB),
                       st([st([rz], 'oveq2d', '( A x. ( Re ` Z ) ) = ( A x. %s )' % GS.CLL)], 'fveq2d', '( exp ` ( A x. ( Re ` Z ) ) ) = %s' % EAC)], 'oveq12d',
                      '( ( exp ` ( B x. ( Re ` Z ) ) ) + ( exp ` ( A x. ( Re ` Z ) ) ) ) = ( %s + %s )' % (EB, EAC))], 'breqtrd', '( abs ` %s ) <_ ( %s + %s )' % (Kz, EB, EAC))
    bcr = st([AR[1], c99], 'remulcld', '( B x. %s ) e. RR' % GS.CLL); acr = st([AR[0], c99], 'remulcld', '( A x. %s ) e. RR' % GS.CLL)
    ble = lin.linarith(w, a, [P_('A <_ B')], '( B x. %s ) <_ ( A x. %s )' % (GS.CLL, GS.CLL), leaves={'A': AR[0], 'B': AR[1]})
    ebe = st([ble, st([bcr, acr, w.inst('efle')], 'syl2anc', '( ( B x. %s ) <_ ( A x. %s ) <-> %s <_ %s )' % (GS.CLL, GS.CLL, EB, EAC))], 'mpbid', '%s <_ %s' % (EB, EAC))
    ebr = st([bcr], 'reefcld', '%s e. RR' % EB); ear = st([acr], 'reefcld', '%s e. RR' % EAC)
    kb3 = lin.linarith(w, a, [kb2, ebe], '( abs ` %s ) <_ ( 2 x. %s )' % (Kz, EAC), leaves={EB: ebr, EAC: ear, '( abs ` %s )' % Kz: st([kzc], 'abscld', '( abs ` %s ) e. RR' % Kz)})
    # MH <_ HMB
    hm = st([P_('N e. NN'), st([P_('R e. RR'), P_('1 <_ R')], 'jca', '( R e. RR /\\ 1 <_ R )'), w.inst('gf1hm')], 'syl2anc', '( 0 <_ %s /\\ %s <_ %s )' % (GS.HMNR, GS.HMNR, HMB))
    ct = ctre(w, a)
    rp_ = st([P_('R e. RR'), lin_([P_('1 <_ R')], '0 < R', {'R': P_('R e. RR')})], 'elrpd', 'R e. RR+')
    hbr = st([st([ct], 'resqcld', '( CTau ^ 2 ) e. RR'), st([st([rp_, litr(w, a, '( ; ; 8 0 1 / ; ; 4 0 0 )')], 'rpcxpcld', '( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR+')], 'rpred',
                                                            '( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) e. RR')], 'remulcld', '%s e. RR' % HMB)
    mr = st([mzc], 'abscld', '( abs ` %s ) e. RR' % Mz)
    mb2 = st([mr, GS.hmreal(w, a, P_), hbr, mb, st([hm], 'simprd', '%s <_ %s' % (GS.HMNR, HMB))], 'letrd', '( abs ` %s ) <_ %s' % (Mz, HMB))
    # the convexity bound at W and gf2lcv
    s02 = lin_([rw_, s1, rz], '( Re ` %s ) <_ ( 3 / ; ; 1 0 0 )' % W_, L3)
    s01 = lin_([rw_, s0, rz], '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W_, L3)
    s200 = lin_([rw_, s0, rz], '( 1 / ; ; 2 0 0 ) <_ ( Re ` %s )' % W_, L3)
    s2_ = lin_([rw_, s1, rz], '( Re ` %s ) <_ 2' % W_, L3)
    wlt = lin_([rw_, s1, rz], '( Re ` %s ) < 1' % W_, L3)
    fvw = w.s([w.s([], 'fveq2', '( %s = 1 -> ( Re ` %s ) = ( Re ` 1 ) )' % (W_, W_)), w.s([], 're1', '( Re ` 1 ) = 1')], 'eqtrdi', '( %s = 1 -> ( Re ` %s ) = 1 )' % (W_, W_))
    wn1 = st([st([rwr, wlt], 'ltned', '( Re ` %s ) =/= 1' % W_), w.s([fvw], 'necon3i', '( ( Re ` %s ) =/= 1 -> %s =/= 1 )' % (W_, W_))], 'syl', '%s =/= 1' % W_)
    CV = split_imp(GS.CVXH[len('A. s e. %s ' % GS.HPZ):])
    cvs = '( ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` s ) /\\ ( Re ` s ) <_ 2 /\\ s =/= 1 ) -> ( abs ` ( ( E ` s ) / ( s - 1 ) ) ) <_ %s )' % GS.CVXB('s')
    idsw = w.s([], 'id', '( s = %s -> s = %s )' % (W_, W_))
    bst, bval = w.wcongr(cvs, {'s': W_}, 's = %s' % W_, {'s': idsw})
    cvw = st([st([s200, s2_, wn1], '3jca', '( ( 1 / ; ; 2 0 0 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 2 /\\ %s =/= 1 )' % (W_, W_, W_)),
              st([bst, P_(GS.CVXH), whz], 'rspcdva', bval)], 'mpd', '( abs ` %s ) <_ %s' % (Qz, GS.CVXB(W_)))
    assert tsub(CVXBW, {'W': W_}) == GS.CVXB(W_), (tsub(CVXBW, {'W': W_}), GS.CVXB(W_))
    qr = st([qc], 'abscld', '( abs ` %s ) e. RR' % Qz)
    LCI = tsub(LCH, {'W': W_, 'V': '( abs ` %s )' % Qz})
    lcf = {x: P_(x) for x in ['D e. RR', '1 < D', '2 <_ ( log ` D )', 'N e. NN', 'S e. CC', '( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ ( 2 x. D )']}
    lcf.update({'%s e. CC' % W_: wc, '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W_: s01, '( Re ` %s ) <_ ( 3 / ; ; 1 0 0 )' % W_: s02, '( abs ` %s ) e. RR' % Qz: qr,
                '( abs ` %s ) <_ %s' % (Qz, GS.CVXB(W_)): cvw})
    lcv = st([build(w, a, LCI, lcf), w.inst('gf2lcv')], 'syl', '( abs ` %s ) <_ %s' % (Qz, tsub(KLC, {'W': W_})))
    # Im W - Im S = Im Z
    IWm = '( Im ` %s )' % W_
    iw1 = st([c1_, zc], 'imaddd', '%s = ( ( Im ` ( 1 + S ) ) + ( Im ` Z ) )' % IWm)
    iw2 = st([st([st([], '1cnd', '1 e. CC'), sc], 'imaddd', '( Im ` ( 1 + S ) ) = ( ( Im ` 1 ) + ( Im ` S ) )'),
              st([st([a1(w, a, w.s([], 'im1', '( Im ` 1 ) = 0'), '( Im ` 1 ) = 0')], 'oveq1d', '( ( Im ` 1 ) + ( Im ` S ) ) = ( 0 + ( Im ` S ) )'),
                  st([st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')], 'addlidd', '( 0 + ( Im ` S ) ) = ( Im ` S )')], 'eqtrd',
                 '( ( Im ` 1 ) + ( Im ` S ) ) = ( Im ` S )')], 'eqtrd', '( Im ` ( 1 + S ) ) = ( Im ` S )')
    iwe = st([iw1, st([iw2], 'oveq1d', '( ( Im ` ( 1 + S ) ) + ( Im ` Z ) ) = ( ( Im ` S ) + ( Im ` Z ) )')], 'eqtrd', '%s = ( ( Im ` S ) + ( Im ` Z ) )' % IWm)
    isc = st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC'); izc = st([st([zc], 'imcld', '( Im ` Z ) e. RR')], 'recnd', '( Im ` Z ) e. CC')
    dd_ = st([st([iwe], 'oveq1d', '( %s - ( Im ` S ) ) = ( ( ( Im ` S ) + ( Im ` Z ) ) - ( Im ` S ) )' % IWm), st([isc, izc], 'pncan2d', '( ( ( Im ` S ) + ( Im ` Z ) ) - ( Im ` S ) ) = ( Im ` Z )')],
             'eqtrd', '( %s - ( Im ` S ) ) = ( Im ` Z )' % IWm)
    U2z = '( ( 1 + ( abs ` ( Im ` Z ) ) ) ^ 2 )'
    KL0 = '( ( ( %s x. CTau ) x. %s ) x. ( log ` D ) )' % (C12, D397)
    u2e = st([st([st([dd_], 'fveq2d', '( abs ` ( %s - ( Im ` S ) ) ) = ( abs ` ( Im ` Z ) )' % IWm)], 'oveq2d',
                 '( 1 + ( abs ` ( %s - ( Im ` S ) ) ) ) = ( 1 + ( abs ` ( Im ` Z ) ) )' % IWm)], 'oveq1d',
             '( ( 1 + ( abs ` ( %s - ( Im ` S ) ) ) ) ^ 2 ) = %s' % (IWm, U2z))
    lcv2 = st([lcv, st([u2e], 'oveq2d', '%s = ( %s x. %s )' % (tsub(KLC, {'W': W_}), KL0, U2z))], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (Qz, KL0, U2z))
    G_ = '( abs ` %s )' % Gz; K_ = '( abs ` %s )' % Kz; Q_ = '( abs ` %s )' % Qz; M_ = '( abs ` %s )' % Mz
    gr = st([gc], 'abscld', '%s e. RR' % G_); g0 = st([gc], 'absge0d', '0 <_ %s' % G_)
    kr = st([kzc], 'abscld', '%s e. RR' % K_); k0 = st([kzc], 'absge0d', '0 <_ %s' % K_)
    q0 = st([qc], 'absge0d', '0 <_ %s' % Q_); m0 = st([mzc], 'absge0d', '0 <_ %s' % M_)
    E2A = '( 2 x. %s )' % EAC
    e2r = st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), ear], 'remulcld', '%s e. RR' % E2A)
    b1 = st([kr, e2r, gr, g0, kb3], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (G_, K_, G_, E2A))
    l2d = P_('2 <_ ( log ` D )'); drp = st([P_('D e. RR'), lin_([P_('1 < D')], '0 < D', {'D': P_('D e. RR')})], 'elrpd', 'D e. RR+')
    kl0r = st([st([st([a1(w, a, num.real(w, C12), '%s e. RR' % C12), ct], 'remulcld', '( %s x. CTau ) e. RR' % C12),
                   st([P_('D e. RR'), st([drp], 'rpge0d', '0 <_ D'), a1(w, a, num.real(w, '( ; ; 3 9 7 / ; ; 8 0 0 )'), '( ; ; 3 9 7 / ; ; 8 0 0 ) e. RR')], 'recxpcld', '%s e. RR' % D397)],
                  'remulcld', '( ( %s x. CTau ) x. %s ) e. RR' % (C12, D397)), st([drp], 'relogcld', '( log ` D ) e. RR')], 'remulcld', '%s e. RR' % KL0)
    iz1 = st([st([], '1red', '1 e. RR'), st([izc], 'abscld', '( abs ` ( Im ` Z ) ) e. RR')], 'readdcld', '( 1 + ( abs ` ( Im ` Z ) ) ) e. RR')
    u2r = st([iz1], 'resqcld', '%s e. RR' % U2z)
    KU = '( %s x. %s )' % (KL0, U2z)
    kur = st([kl0r, u2r], 'remulcld', '%s e. RR' % KU)
    b2 = st([qr, kur, mr, hbr, q0, m0, lcv2, mb2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (Q_, M_, KU, HMB))
    GK_ = '( %s x. %s )' % (G_, K_); QM_ = '( %s x. %s )' % (Q_, M_)
    b3 = st([st([gr, kr], 'remulcld', '%s e. RR' % GK_), st([gr, e2r], 'remulcld', '( %s x. %s ) e. RR' % (G_, E2A)), st([qr, mr], 'remulcld', '%s e. RR' % QM_),
             st([kur, hbr], 'remulcld', '( %s x. %s ) e. RR' % (KU, HMB)), st([gr, kr, g0, k0], 'mulge0d', '0 <_ %s' % GK_), st([qr, mr, q0, m0], 'mulge0d', '0 <_ %s' % QM_), b1, b2],
            'lemul12ad', '( %s x. %s ) <_ ( ( %s x. %s ) x. ( %s x. %s ) )' % (GK_, QM_, G_, E2A, KU, HMB))
    rq = ringeq(w, a, '( ( %s x. %s ) x. ( %s x. %s ) )' % (G_, E2A, KU, HMB), '( %s x. ( %s x. %s ) )' % (KLP, G_, U2z),
                Closure(w, a, {G_: gr, EAC: ear, HMB: hbr, KL0: kl0r, U2z: u2r}))
    fin = st([agr, st([b3, rq], 'breqtrd', '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (GK_, QM_, KLP, G_, U2z))], 'eqbrtrd', split_imp(S_['gf2lpt'])[1])
    w.qed([fin], 'idi', S_['gf2lpt'])
    return w


KGL = '( ( ; 5 0 / ; 4 9 ) x. ( ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) / ( log ` 2 ) ) )'
LEH = '( %s /\\ %s )' % (GS.MSH, FRZ)
S_['gf2left'] = '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (LEH, GS.VLh(GS.GI, GS.CLL), KLP, KGL)


def gf2left():
    w = W('gf2left', 'The remainder line integral is small (Lean ` norm_Brem_le ` before the numerals): ` | int_(-99/100) GI | <_ KL ( 50/49 ) 1024 1632 / log 2 ` '
          '(~ z6vlcvg for its existence, ~ z6lvert , ~ itgabs , ~ itgle with ~ gf2lpt , the moment ~ z6gmoml , ~ z6rlimle ).')
    a = LEH; st = mkst(w, a)
    P_ = lambda x: proj(w, a, x)
    CL = GS.CLL
    c99 = litr(w, a, CL)
    gic = GS.gicont(w, a, P_)
    m5r, ysp = GS.m5ys(w, a, P_)
    ic = a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    # the line lies in DI; the strip bound on the line
    gsd = st([P_(GS.GSH), w.inst('gf2grsd')], 'syl', 'A. z e. CC %s' % GS.STRD)
    gmj = st([P_(GS.MSH), w.inst('gf2grmaj')], 'syl', 'A. z e. CC %s' % GS.STRM)
    au = '( %s /\\ u e. RR )' % a; tu = mkst(w, au)
    ur = tu([], 'simpr', 'u e. RR')
    Z = '( %s + ( _i x. u ) )' % CL
    zc = tu([tu([lift(w, c99, au)], 'recnd', '%s e. CC' % CL), tu([lift(w, ic, au), tu([ur], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')], 'addcld', '%s e. CC' % Z)
    rz = tu([lift(w, c99, au), ur], 'crred', '( Re ` %s ) = %s' % (Z, CL)); iz = tu([lift(w, c99, au), ur], 'crimd', '( Im ` %s ) = u' % Z)
    rzr = tu([zc], 'recld', '( Re ` %s ) e. RR' % Z)
    idz = w.s([], 'id', '( z = %s -> z = %s )' % (Z, Z))
    bsd, vsd = w.wcongr(GS.STRD, {'z': Z}, 'z = %s' % Z, {'z': idz})
    isd = tu([bsd, lift(w, gsd, au), zc], 'rspcdva', vsd)
    hp = tu([tu([tu([lift(w, c99, au), tu([rz], 'eqcomd', '%s = ( Re ` %s )' % (CL, Z))], 'eqled', '%s <_ ( Re ` %s )' % (CL, Z)),
                 lin.linarith(w, au, [rz], '( Re ` %s ) <_ 1' % Z, leaves={'( Re ` %s )' % Z: rzr})], 'jca', '( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 )' % (CL, Z, Z)),
             tu([tu([rz], 'orcd', '( ( Re ` %s ) = %s \\/ ( Re ` %s ) = 1 )' % (Z, CL, Z))], 'orcd', '( ( ( Re ` %s ) = %s \\/ ( Re ` %s ) = 1 ) \\/ %s <_ ( abs ` ( Im ` %s ) ) )' % (Z, CL, Z, GS.YS, Z))],
            'jca', split_imp(vsd)[0])
    zdi = tu([hp, isd], 'mpd', '%s e. %s' % (Z, GS.DI))
    lin_di = st([zdi], 'ralrimiva', 'A. u e. RR %s e. %s' % (Z, GS.DI))
    E4U = '( 2 ^c -u ( ( abs ` u ) / 4 ) )'
    ay = '( %s /\\ %s <_ ( abs ` u ) )' % (au, GS.YS); ty = mkst(w, ay)
    bmj, vmj = w.wcongr(GS.STRM, {'z': Z}, 'z = %s' % Z, {'z': idz})
    imj = ty([bmj, lift(w, gmj, ay), lift(w, zc, ay)], 'rspcdva', vmj)
    aiz = ty([lift(w, iz, ay)], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` u )' % Z)
    hm_ = ty([ty([ty([lift(w, c99, ay), ty([lift(w, rz, ay)], 'eqcomd', '%s = ( Re ` %s )' % (CL, Z))], 'eqled', '%s <_ ( Re ` %s )' % (CL, Z)),
                  lin.linarith(w, ay, [lift(w, rz, ay)], '( Re ` %s ) <_ 1' % Z, leaves={'( Re ` %s )' % Z: lift(w, rzr, ay)})], 'jca', '( %s <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 )' % (CL, Z, Z)),
              ty([ty([], 'simpr', '%s <_ ( abs ` u )' % GS.YS), aiz], 'breqtrrd', '%s <_ ( abs ` ( Im ` %s ) )' % (GS.YS, Z))], 'jca', split_imp(vmj)[0])
    mj1 = ty([hm_, imj], 'mpd', split_imp(vmj)[1])
    E4Z = '( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) )' % Z
    e4eq = ty([ty([ty([aiz], 'oveq1d', '( ( abs ` ( Im ` %s ) ) / 4 ) = ( ( abs ` u ) / 4 )' % Z)], 'negeqd', '-u ( ( abs ` ( Im ` %s ) ) / 4 ) = -u ( ( abs ` u ) / 4 )' % Z)],
              'oveq2d', '%s = %s' % (E4Z, E4U))
    mj2 = ty([mj1, ty([e4eq], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (GS.M5, E4Z, GS.M5, E4U))], 'breqtrd',
             '( abs ` ( %s ` %s ) ) <_ ( %s x. %s )' % (GS.GI, Z, GS.M5, E4U))
    smj = st([w.s([mj2], 'ex', '( %s -> ( %s <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) ) )' % (au, GS.YS, GS.GI, Z, GS.M5, E4U))], 'ralrimiva',
             'A. u e. RR ( %s <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) )' % (GS.YS, GS.GI, Z, GS.M5, E4U))
    VH = '( ( %s e. RR /\\ ( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s ) ) /\\ ( ( %s e. RR /\\ %s e. RR+ ) /\\ A. u e. RR ( %s <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) ) ) )' % (
        CL, GS.GI, GS.DI, Z, GS.DI, GS.M5, GS.YS, GS.YS, GS.GI, Z, GS.M5, E4U)
    VLF_ = GS.VLhF(GS.GI, CL)
    vc = st([st([st([c99, st([gic, lin_di], 'jca', '( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s )' % (GS.GI, GS.DI, Z, GS.DI))], 'jca',
                    '( %s e. RR /\\ ( %s e. ( %s -cn-> CC ) /\\ A. u e. RR %s e. %s ) )' % (CL, GS.GI, GS.DI, Z, GS.DI)),
                 st([st([m5r, ysp], 'jca', '( %s e. RR /\\ %s e. RR+ )' % (GS.M5, GS.YS)), smj], 'jca',
                    '( ( %s e. RR /\\ %s e. RR+ ) /\\ A. u e. RR ( %s <_ ( abs ` u ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. %s ) ) )' % (GS.M5, GS.YS, GS.YS, GS.GI, Z, GS.M5, E4U))],
                'jca', VH), w.inst('z6vlcvg')], 'syl',
            '( %s ~~>r %s /\\ A. h e. RR+ ( %s <_ h -> ( abs ` ( %s - %s ) ) <_ ( ( ( 8 x. %s ) / ( log ` 2 ) ) x. ( 2 ^c -u ( h / 4 ) ) ) ) )' % (
                VLF_, GS.VLh(GS.GI, CL), GS.YS, GS.VLh(GS.GI, CL), GS.LIh(GS.GI, CL), GS.M5))
    cv = st([vc], 'simpld', '%s ~~>r %s' % (VLF_, GS.VLh(GS.GI, CL)))
    # KLP e. RR , 0 <_ KLP
    ct = ctre(w, a)
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    cg0 = w.s([w.s([], '2re', '2 e. RR'), w.s([knn], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.s([], '0le2', '0 <_ 2'), w.inst('expge0')], 'mp3an', '0 <_ ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')
    ct0 = a1(w, a, w.s([cg0, w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')], 'breqtrri', '0 <_ CTau'), '0 <_ CTau')
    ear = st([st([P_('A e. RR'), c99], 'remulcld', '( A x. %s ) e. RR' % CL)], 'rpefcld', '%s e. RR+' % EAC)
    two_r = a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'); two0 = a1(w, a, w.s([], '0le2', '0 <_ 2'), '0 <_ 2')
    e2a = st([two_r, st([ear], 'rpred', '%s e. RR' % EAC)], 'remulcld', '( 2 x. %s ) e. RR' % EAC)
    e2a0 = st([two_r, st([ear], 'rpred', '%s e. RR' % EAC), two0, st([ear], 'rpge0d', '0 <_ %s' % EAC)], 'mulge0d', '0 <_ ( 2 x. %s )' % EAC)
    rp_ = st([P_('R e. RR'), lin.linarith(w, a, [P_('1 <_ R')], '0 < R', leaves={'R': P_('R e. RR')})], 'elrpd', 'R e. RR+')
    R8 = '( R ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) )'
    r8p = st([rp_, litr(w, a, '( ; ; 8 0 1 / ; ; 4 0 0 )')], 'rpcxpcld', '%s e. RR+' % R8)
    hbr = st([st([ct], 'resqcld', '( CTau ^ 2 ) e. RR'), st([r8p], 'rpred', '%s e. RR' % R8)], 'remulcld', '%s e. RR' % HMB)
    hb0 = st([st([ct], 'resqcld', '( CTau ^ 2 ) e. RR'), st([r8p], 'rpred', '%s e. RR' % R8), st([ct], 'sqge0d', '0 <_ ( CTau ^ 2 )'), st([r8p], 'rpge0d', '0 <_ %s' % R8)],
              'mulge0d', '0 <_ %s' % HMB)
    drp = st([P_('D e. RR'), lin.linarith(w, a, [P_('1 < D')], '0 < D', leaves={'D': P_('D e. RR')})], 'elrpd', 'D e. RR+')
    c12r = a1(w, a, num.real(w, C12), '%s e. RR' % C12); c120 = a1(w, a, num.ge0_nat(w, 1200000), '0 <_ %s' % C12)
    C12C = '( %s x. CTau )' % C12
    ccr = st([c12r, ct], 'remulcld', '%s e. RR' % C12C); cc0 = st([c12r, ct, c120, ct0], 'mulge0d', '0 <_ %s' % C12C)
    d3p = st([drp, litr(w, a, '( ; ; 3 9 7 / ; ; 8 0 0 )')], 'rpcxpcld', '%s e. RR+' % D397)
    cd = '( %s x. %s )' % (C12C, D397)
    cdr = st([ccr, st([d3p], 'rpred', '%s e. RR' % D397)], 'remulcld', '%s e. RR' % cd); cd0 = st([ccr, st([d3p], 'rpred', '%s e. RR' % D397), cc0, st([d3p], 'rpge0d', '0 <_ %s' % D397)],
                                                                                             'mulge0d', '0 <_ %s' % cd)
    lgr = st([drp], 'relogcld', '( log ` D ) e. RR'); lg0 = lin.linarith(w, a, [P_('2 <_ ( log ` D )')], '0 <_ ( log ` D )', leaves={'( log ` D )': lgr})
    KL0 = '( %s x. ( log ` D ) )' % cd
    kl0r = st([cdr, lgr], 'remulcld', '%s e. RR' % KL0); kl00 = st([cdr, lgr, cd0, lg0], 'mulge0d', '0 <_ %s' % KL0)
    EH = '( ( 2 x. %s ) x. %s )' % (EAC, HMB)
    ehr = st([e2a, hbr], 'remulcld', '%s e. RR' % EH); eh0 = st([e2a, hbr, e2a0, hb0], 'mulge0d', '0 <_ %s' % EH)
    klpr = st([ehr, kl0r], 'remulcld', '%s e. RR' % KLP); klp0 = st([ehr, kl0r, eh0, kl00], 'mulge0d', '0 <_ %s' % KLP)
    l2p = a1(w, a, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'),
                        w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('loggt0b')], 'ax-mp', '( 0 < ( log ` 2 ) <-> 1 < 2 )')], 'mpbir', '0 < ( log ` 2 )')],
                       'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    kglr = st([a1(w, a, num.real(w, '( ; 5 0 / ; 4 9 )'), '( ; 5 0 / ; 4 9 ) e. RR'),
               st([a1(w, a, w.s([num.real(w, '; ; ; 1 0 2 4'), num.real(w, '; ; ; 1 6 3 2')], 'remulcli', '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) e. RR'), '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) e. RR'),
                   l2p], 'rerpdivcld', '( ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) / ( log ` 2 ) ) e. RR')], 'remulcld', '%s e. RR' % KGL)
    # every height h
    ah = '( %s /\\ h e. RR+ )' % a; th = mkst(w, ah)
    hp_ = th([], 'simpr', 'h e. RR+'); hr_ = th([hp_], 'rpred', 'h e. RR')
    A_ = '( %s + ( _i x. -u h ) )' % CL; B_ = '( %s + ( _i x. h ) )' % CL
    SEGh = '( %s cseg %s )' % (A_, B_)
    c99h = lift(w, c99, ah); ich = lift(w, ic, ah)
    ac = th([th([c99h], 'recnd', '%s e. CC' % CL), th([ich, th([th([hr_], 'renegcld', '-u h e. RR')], 'recnd', '-u h e. CC')], 'mulcld', '( _i x. -u h ) e. CC')], 'addcld', '%s e. CC' % A_)
    bc = th([th([c99h], 'recnd', '%s e. CC' % CL), th([ich, th([hr_], 'recnd', 'h e. CC')], 'mulcld', '( _i x. h ) e. CC')], 'addcld', '%s e. CC' % B_)
    ra = th([c99h, th([hr_], 'renegcld', '-u h e. RR')], 'crred', '( Re ` %s ) = %s' % (A_, CL)); rb = th([c99h, hr_], 'crred', '( Re ` %s ) = %s' % (B_, CL))
    vre = th([ac, bc, th([ra, rb], 'eqtr4d', '( Re ` %s ) = ( Re ` %s )' % (A_, B_)), w.inst('csegvre')], 'syl3anc', 'A. u e. %s ( Re ` u ) = ( Re ` %s )' % (SEGh, A_))
    scc = th([ac, bc, w.inst('csegcl')], 'syl2anc', '%s C_ CC' % SEGh)
    aq = '( %s /\\ q e. %s )' % (ah, SEGh); tq = mkst(w, aq)
    qm = tq([], 'simpr', 'q e. %s' % SEGh)
    qc = tq([lift(w, scc, aq), qm], 'sseldd', 'q e. CC')
    rsp = w.s([w.s([], 'fveq2', '( u = q -> ( Re ` u ) = ( Re ` q ) )')], 'eqeq1d', '( u = q -> ( ( Re ` u ) = ( Re ` %s ) <-> ( Re ` q ) = ( Re ` %s ) ) )' % (A_, A_))
    rq = tq([tq([rsp, lift(w, vre, aq), qm], 'rspcdva', '( Re ` q ) = ( Re ` %s )' % A_), lift(w, ra, aq)], 'eqtrd', '( Re ` q ) = %s' % CL)
    rqr = tq([qc], 'recld', '( Re ` q ) e. RR')
    idq = w.s([], 'id', '( z = q -> z = q )')
    bq, vq = w.wcongr(GS.STRD, {'z': 'q'}, 'z = q', {'z': idq})
    iq = tq([bq, lift(w, gsd, aq), qc], 'rspcdva', vq)
    hpq = tq([tq([tq([lift(w, c99, aq), tq([rq], 'eqcomd', '%s = ( Re ` q )' % CL)], 'eqled', '%s <_ ( Re ` q )' % CL),
                  lin.linarith(w, aq, [rq], '( Re ` q ) <_ 1', leaves={'( Re ` q )': rqr})], 'jca', '( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )' % CL),
              tq([tq([rq], 'orcd', '( ( Re ` q ) = %s \\/ ( Re ` q ) = 1 )' % CL)], 'orcd', '( ( ( Re ` q ) = %s \\/ ( Re ` q ) = 1 ) \\/ %s <_ ( abs ` ( Im ` q ) ) )' % (CL, GS.YS))],
             'jca', split_imp(vq)[0])
    qdi = tq([hpq, iq], 'mpd', 'q e. %s' % GS.DI)
    sdi = th([w.s([qdi], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (ah, SEGh, GS.DI))], 'ssrdv', '%s C_ %s' % (SEGh, GS.DI))
    FI = '( u e. ( -u h (,) h ) |-> ( %s ` %s ) )' % (GS.GI, Z)
    IT = 'S. ( -u h (,) h ) ( %s ` %s ) _d u' % (GS.GI, Z)
    lv = th([th([c99h, hp_], 'jca', '( %s e. RR /\\ h e. RR+ )' % CL), th([lift(w, gic, ah), sdi], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GS.GI, GS.DI, SEGh, GS.DI)),
              w.inst('z6lvert')], 'syl2anc', '( %s e. L^1 /\\ %s = ( _i x. %s ) )' % (FI, GS.LIh(GS.GI, CL), IT))
    fil = th([lv], 'simpld', '%s e. L^1' % FI); lie = th([lv], 'simprd', '%s = ( _i x. %s )' % (GS.LIh(GS.GI, CL), IT))
    ahu = '( %s /\\ u e. ( -u h (,) h ) )' % ah; tv = mkst(w, ahu)
    uio = tv([], 'simpr', 'u e. ( -u h (,) h )')
    urr = tv([uio, w.inst('elioore')], 'syl', 'u e. RR')
    def fromau(stp, concl):
        e = st([w.s([stp], 'ex', '( %s -> ( u e. RR -> %s ) )' % (a, concl))], 'idi', '( u e. RR -> %s )' % concl)
        return tv([urr, lift(w, e, ahu)], 'mpd', concl)
    zcv = fromau(zc, '%s e. CC' % Z); rzv = fromau(rz, '( Re ` %s ) = %s' % (Z, CL)); izv = fromau(iz, '( Im ` %s ) = u' % Z)
    zdv = fromau(zdi, '%s e. %s' % (Z, GS.DI))
    gzc = tv([tv([lift(w, gic, ahu), w.inst('cncff')], 'syl', '%s : %s --> CC' % (GS.GI, GS.DI)), zdv], 'ffvelcdmd', '( %s ` %s ) e. CC' % (GS.GI, Z))
    agz = tv([gzc], 'abscld', '( abs ` ( %s ` %s ) ) e. RR' % (GS.GI, Z))
    # pointwise: | GI Z | <_ KLP g
    lp = tv([tv([proj(w, ahu, LEH), tv([zcv, rzv], 'jca', '( %s e. CC /\\ ( Re ` %s ) = %s )' % (Z, Z, CL))], 'jca', tsub(split_imp(S_['gf2lpt'])[0], {'Z': Z})),
             w.inst('gf2lpt')], 'syl', tsub(split_imp(S_['gf2lpt'])[1], {'Z': Z}))
    G2 = '( ( abs ` ( _G ` %s ) ) x. ( ( 1 + ( abs ` u ) ) ^ 2 ) )' % Z
    G2i = '( ( abs ` ( _G ` %s ) ) x. ( ( 1 + ( abs ` ( Im ` %s ) ) ) ^ 2 ) )' % (Z, Z)
    ge_ = tv([tv([tv([tv([izv], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` u )' % Z)], 'oveq2d', '( 1 + ( abs ` ( Im ` %s ) ) ) = ( 1 + ( abs ` u ) )' % Z)], 'oveq1d',
                 '( ( 1 + ( abs ` ( Im ` %s ) ) ) ^ 2 ) = ( ( 1 + ( abs ` u ) ) ^ 2 )' % Z)], 'oveq2d', '%s = %s' % (G2i, G2))
    lp2 = tv([lp, tv([ge_], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (KLP, G2i, KLP, G2))], 'breqtrd', '( abs ` ( %s ` %s ) ) <_ ( %s x. %s )' % (GS.GI, Z, KLP, G2))
    # G2 real
    rzr2 = tv([zcv], 'recld', '( Re ` %s ) e. RR' % Z)
    zm1 = lin.linarith(w, ahu, [rzv], '-u 1 < ( Re ` %s )' % Z, leaves={'( Re ` %s )' % Z: rzr2})
    rneq = tv([tv([lin.linarith(w, ahu, [rzv], '( Re ` %s ) < 0' % Z, leaves={'( Re ` %s )' % Z: rzr2})], 'ltned', '( Re ` %s ) =/= 0' % Z)], 'neneqd', '-. ( Re ` %s ) = 0' % Z)
    c3 = '( %s /\\ %s = 0 )' % (ahu, Z); t3 = mkst(w, c3)
    r03 = t3([t3([t3([], 'simpr', '%s = 0' % Z)], 'fveq2d', '( Re ` %s ) = ( Re ` 0 )' % Z), a1(w, c3, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')], 'eqtrd', '( Re ` %s ) = 0' % Z)
    zn0 = tv([w.s([r03, lift(w, rneq, c3)], 'pm2.65da', '( %s -> -. %s = 0 )' % (ahu, Z))], 'neqned', '%s =/= 0' % Z)
    zdg = tv([tv([zcv, tv([zm1, zn0], 'jca', '( -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (Z, Z))], 'jca', '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ %s =/= 0 ) )' % (Z, Z, Z)),
              w.inst('z6rdg')], 'syl', '%s e. ( CC \\ ( ZZ \\ NN ) )' % Z)
    agm = tv([tv([zdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % Z)], 'abscld', '( abs ` ( _G ` %s ) ) e. RR' % Z)
    u2 = tv([tv([tv([], '1red', '1 e. RR'), tv([tv([urr], 'recnd', 'u e. CC')], 'abscld', '( abs ` u ) e. RR')], 'readdcld', '( 1 + ( abs ` u ) ) e. RR')], 'resqcld',
            '( ( 1 + ( abs ` u ) ) ^ 2 ) e. RR')
    g2r = tv([agm, u2], 'remulcld', '%s e. RR' % G2)
    kg2r = tv([lift(w, klpr, ahu), g2r], 'remulcld', '( %s x. %s ) e. RR' % (KLP, G2))
    GF = '( u e. ( -u h (,) h ) |-> %s )' % G2
    lo99 = lin.linarith(w, ah, [], '-u ( ; 9 9 / ; ; 1 0 0 ) <_ %s' % CL)
    r98 = a1(w, ah, num.real(w, '; 9 8'), '; 9 8 e. RR'); r99 = a1(w, ah, num.real(w, '; 9 9'), '; 9 9 e. RR')
    r100 = a1(w, ah, num.rp(w, '; ; 1 0 0'), '; ; 1 0 0 e. RR+')
    q98 = th([r98, r100], 'rerpdivcld', '( ; 9 8 / ; ; 1 0 0 ) e. RR'); q99 = th([r99, r100], 'rerpdivcld', '( ; 9 9 / ; ; 1 0 0 ) e. RR')
    l9 = th([a1(w, ah, num.le_lit(w, '; 9 8', '; 9 9'), '; 9 8 <_ ; 9 9'), th([r98, r99, r100], 'lediv1d', '( ; 9 8 <_ ; 9 9 <-> ( ; 9 8 / ; ; 1 0 0 ) <_ ( ; 9 9 / ; ; 1 0 0 ) )')],
            'mpbid', '( ; 9 8 / ; ; 1 0 0 ) <_ ( ; 9 9 / ; ; 1 0 0 )')
    hi98 = th([l9, th([q98, q99], 'lenegd', '( ( ; 9 8 / ; ; 1 0 0 ) <_ ( ; 9 9 / ; ; 1 0 0 ) <-> %s <_ -u ( ; 9 8 / ; ; 1 0 0 ) )' % CL)], 'mpbid', '%s <_ -u ( ; 9 8 / ; ; 1 0 0 )' % CL)
    gmm = th([th([th([c99h, lo99, hi98], '3jca', '( %s e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ %s /\\ %s <_ -u ( ; 9 8 / ; ; 1 0 0 ) )' % (CL, CL, CL)), hp_], 'jca',
                 '( ( %s e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ %s /\\ %s <_ -u ( ; 9 8 / ; ; 1 0 0 ) ) /\\ h e. RR+ )' % (CL, CL, CL)), w.inst('z6gmoml')], 'syl',
              '( %s e. L^1 /\\ S. ( -u h (,) h ) %s _d u <_ %s )' % (GF, G2, KGL))
    gfl = th([gmm], 'simpld', '%s e. L^1' % GF); gmb = th([gmm], 'simprd', 'S. ( -u h (,) h ) %s _d u <_ %s' % (G2, KGL))
    gzv = tv([], 'fvexd', '( %s ` %s ) e. _V' % (GS.GI, Z))
    AF = '( u e. ( -u h (,) h ) |-> ( abs ` ( %s ` %s ) ) )' % (GS.GI, Z)
    afl = w.s([gzv, fil], 'iblabs', '( %s -> %s e. L^1 )' % (ah, AF))
    KF = '( u e. ( -u h (,) h ) |-> ( %s x. %s ) )' % (KLP, G2)
    klc = th([lift(w, klpr, ah)], 'recnd', '%s e. CC' % KLP)
    g2v = tv([], 'ovexd', '%s e. _V' % G2)
    kfl = w.s([klc, g2v, gfl], 'iblmulc2', '( %s -> %s e. L^1 )' % (ah, KF))
    ia = w.s([gzv, fil], 'itgabs', '( %s -> ( abs ` %s ) <_ S. ( -u h (,) h ) ( abs ` ( %s ` %s ) ) _d u )' % (ah, IT, GS.GI, Z))
    il = w.s([afl, kfl, agz, kg2r, lp2], 'itgle', '( %s -> S. ( -u h (,) h ) ( abs ` ( %s ` %s ) ) _d u <_ S. ( -u h (,) h ) ( %s x. %s ) _d u )' % (ah, GS.GI, Z, KLP, G2))
    im = w.s([klc, g2v, gfl], 'itgmulc2', '( %s -> ( %s x. S. ( -u h (,) h ) %s _d u ) = S. ( -u h (,) h ) ( %s x. %s ) _d u )' % (ah, KLP, G2, KLP, G2))
    MG = 'S. ( -u h (,) h ) %s _d u' % G2
    mgr = w.s([g2r, gfl], 'itgrecl', '( %s -> %s e. RR )' % (ah, MG))
    kb_ = th([mgr, lift(w, kglr, ah), lift(w, klpr, ah), lift(w, klp0, ah), gmb], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (KLP, MG, KLP, KGL))
    AI = 'S. ( -u h (,) h ) ( abs ` ( %s ` %s ) ) _d u' % (GS.GI, Z)
    air = w.s([agz, afl], 'itgrecl', '( %s -> %s e. RR )' % (ah, AI))
    KI = 'S. ( -u h (,) h ) ( %s x. %s ) _d u' % (KLP, G2)
    kir = w.s([kg2r, kfl], 'itgrecl', '( %s -> %s e. RR )' % (ah, KI))
    itcc = w.s([gzv, fil], 'itgcl', '( %s -> %s e. CC )' % (ah, IT))
    LI_ = GS.LIh(GS.GI, CL)
    ab = th([th([lie], 'fveq2d', '( abs ` %s ) = ( abs ` ( _i x. %s ) )' % (LI_, IT)),
             th([th([ich, itcc], 'absmuld', '( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (IT, IT)),
                 th([th([a1(w, ah, w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1')], 'oveq1d', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) )' % (IT, IT)),
                     th([th([th([itcc], 'abscld', '( abs ` %s ) e. RR' % IT)], 'recnd', '( abs ` %s ) e. CC' % IT)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (IT, IT))],
                    'eqtrd', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s )' % (IT, IT))], 'eqtrd', '( abs ` ( _i x. %s ) ) = ( abs ` %s )' % (IT, IT))], 'eqtrd',
            '( abs ` %s ) = ( abs ` %s )' % (LI_, IT))
    KB = '( %s x. %s )' % (KLP, KGL)
    itr = th([itcc], 'abscld', '( abs ` %s ) e. RR' % IT)
    kbr = th([lift(w, klpr, ah), lift(w, kglr, ah)], 'remulcld', '%s e. RR' % KB)
    kmg = '( %s x. %s )' % (KLP, MG)
    kmgr = th([lift(w, klpr, ah), mgr], 'remulcld', '%s e. RR' % kmg)
    c1 = th([itr, air, kir, ia, il], 'letrd', '( abs ` %s ) <_ %s' % (IT, KI))
    c2 = th([c1, th([im], 'eqcomd', '%s = %s' % (KI, kmg))], 'breqtrd', '( abs ` %s ) <_ %s' % (IT, kmg))
    c3_ = th([itr, kmgr, kbr, c2, kb_], 'letrd', '( abs ` %s ) <_ %s' % (IT, KB))
    c4 = th([ab, c3_], 'eqbrtrd', '( abs ` %s ) <_ %s' % (LI_, KB))
    rall = st([c4], 'ralrimiva', 'A. h e. RR+ ( abs ` %s ) <_ %s' % (LI_, KB))
    fin = st([cv, st([st([klpr, kglr], 'remulcld', '%s e. RR' % KB), rall], 'jca', '( %s e. RR /\\ A. h e. RR+ ( abs ` %s ) <_ %s )' % (KB, LI_, KB)), w.inst('z6rlimle')],
             'syl2anc', split_imp(S_['gf2left'])[1])
    w.qed([fin], 'idi', S_['gf2left'])
    return w


LD = '( log ` D )'
LM0f = '( log ` ( D ^c ( 3 / 5 ) ) )'
RPf = '( D ^c ( 1 / ; ; 1 0 0 ) )'
KLPf = tsub(KLP, {'A': LM0f, 'R': RPf})
TPIa = '( 2 x. _pi )'
D7 = '( D ^c -u ( 7 / ; ; 1 0 0 ) )'
S_['gf2num'] = '( %s -> ( ( %s x. %s ) / %s ) <_ ( ( %s x. ( %s ^ 3 ) ) x. %s ) )' % (HZ2, KLPf, KGL, TPIa, L_.C11, LD, D7)


def gf2num():
    w = W('gf2num', 'The remainder constant (Lean ` norm_Brem_le ` , ` norm_Brem_le' + "'" + ' ` ): ` KL ( 50/49 ) ( 1024 1632 / log 2 ) / 2 pi <_ C11 ( log D ) ^ 3 D ^ -u ( 7/100 ) ` '
          'at ` A = log D ^ ( 3/5 ) ` , ` R = D ^ ( 1/100 ) ` : the ` D ` -exponent is ` -3109/40000 <_ -7/100 ` , ` 1 / log 2 < 3 ` , ` 2 pi >_ 6 ` , ` log D <_ ( log D ) ^ 3 / 4 ` .')
    a = HZ2; st = mkst(w, a)
    dr = proj(w, a, 'D e. RR'); d1 = proj(w, a, '1 < D'); l2 = proj(w, a, '2 <_ ( log ` D )')
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    dc = st([drp], 'rpcnd', 'D e. CC'); dn0 = st([drp], 'rpne0d', 'D =/= 0')
    ldr = st([drp], 'relogcld', '%s e. RR' % LD)
    CL = GS.CLL
    c99 = litr(w, a, CL)
    q35 = litr(w, a, '( 3 / 5 )')
    lm0 = st([drp, q35], 'logcxpd', '%s = ( ( 3 / 5 ) x. %s )' % (LM0f, LD))
    X1 = '( ( 3 / 5 ) x. %s )' % CL
    x1r = st([q35, c99], 'remulcld', '%s e. RR' % X1)
    e1a = st([st([st([lm0], 'oveq1d', '( %s x. %s ) = ( ( ( 3 / 5 ) x. %s ) x. %s )' % (LM0f, CL, LD, CL)),
                  ringeq(w, a, '( ( ( 3 / 5 ) x. %s ) x. %s )' % (LD, CL), '( %s x. %s )' % (X1, LD), Closure(w, a, {LD: ldr}))], 'eqtrd',
                 '( %s x. %s ) = ( %s x. %s )' % (LM0f, CL, X1, LD))], 'fveq2d', '%s = ( exp ` ( %s x. %s ) )' % (tsub(EAC, {'A': LM0f}), X1, LD))
    e1b = st([dc, dn0, st([x1r], 'recnd', '%s e. CC' % X1)], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (X1, X1, LD))
    e1 = st([e1a, e1b], 'eqtr4d', '%s = ( D ^c %s )' % (tsub(EAC, {'A': LM0f}), X1))
    X2 = '( ( 1 / ; ; 1 0 0 ) x. ( ; ; 8 0 1 / ; ; 4 0 0 ) )'
    e2 = st([st([drp, litr(w, a, '( 1 / ; ; 1 0 0 )'), a1(w, a, num.cc(w, '( ; ; 8 0 1 / ; ; 4 0 0 )'), '( ; ; 8 0 1 / ; ; 4 0 0 ) e. CC'), w.inst('cxpmul')], 'syl3anc',
                '( D ^c %s ) = ( %s ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) )' % (X2, RPf))], 'eqcomd', '( %s ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) ) = ( D ^c %s )' % (RPf, X2))
    X3 = '( ; ; 3 9 7 / ; ; 8 0 0 )'
    x2c = st([litr(w, a, '( 1 / ; ; 1 0 0 )'), litr(w, a, '( ; ; 8 0 1 / ; ; 4 0 0 )')], 'remulcld', '%s e. RR' % X2)
    x3r = litr(w, a, X3)
    E1 = '( D ^c %s )' % X1; E2 = '( D ^c %s )' % X2
    XE = '-u ( ; ; ; 3 1 0 9 / ; ; ; ; 4 0 0 0 0 )'
    ca1 = st([dc, dn0, st([x1r], 'recnd', '%s e. CC' % X1), st([x2c], 'recnd', '%s e. CC' % X2)], 'cxpaddd', '( D ^c ( %s + %s ) ) = ( %s x. %s )' % (X1, X2, E1, E2))
    X12 = '( %s + %s )' % (X1, X2)
    ca2 = st([dc, dn0, st([st([x1r, x2c], 'readdcld', '%s e. RR' % X12)], 'recnd', '%s e. CC' % X12), st([x3r], 'recnd', '%s e. CC' % X3)], 'cxpaddd',
             '( D ^c ( %s + %s ) ) = ( ( D ^c %s ) x. %s )' % (X12, X3, X12, D397))
    P3 = '( ( %s x. %s ) x. %s )' % (E1, E2, D397)
    xe = ringeq(w, a, '( %s + %s )' % (X12, X3), XE, Closure(w, a, {}))
    p3e = st([st([st([xe], 'oveq2d', '( D ^c ( %s + %s ) ) = ( D ^c %s )' % (X12, X3, XE))], 'eqcomd', '( D ^c %s ) = ( D ^c ( %s + %s ) )' % (XE, X12, X3)),
              st([ca2, st([ca1], 'oveq1d', '( ( D ^c %s ) x. %s ) = %s' % (X12, D397, P3))], 'eqtrd', '( D ^c ( %s + %s ) ) = %s' % (X12, X3, P3))], 'eqtrd', '( D ^c %s ) = %s' % (XE, P3))
    d1le = lin.linarith(w, a, [d1], '1 <_ D', leaves={'D': dr})
    p3le = st([st([dr, d1le], 'jca', '( D e. RR /\\ 1 <_ D )'), st([litr(w, a, XE), litr(w, a, '-u ( 7 / ; ; 1 0 0 )')], 'jca', '( %s e. RR /\\ -u ( 7 / ; ; 1 0 0 ) e. RR )' % XE),
               lin.linarith(w, a, [], '%s <_ -u ( 7 / ; ; 1 0 0 )' % XE), w.inst('cxplea')], 'syl3anc', '( D ^c %s ) <_ %s' % (XE, D7))
    p3b = st([st([p3e], 'eqcomd', '%s = ( D ^c %s )' % (P3, XE)), p3le], 'eqbrtrd', '%s <_ %s' % (P3, D7))
    p3p = st([st([st([drp, x1r], 'rpcxpcld', '%s e. RR+' % E1), st([drp, x2c], 'rpcxpcld', '%s e. RR+' % E2)], 'rpmulcld', '( %s x. %s ) e. RR+' % (E1, E2)),
              st([drp, x3r], 'rpcxpcld', '%s e. RR+' % D397)], 'rpmulcld', '%s e. RR+' % P3)
    d7r = st([st([drp, litr(w, a, '-u ( 7 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % D7)], 'rpred', '%s e. RR' % D7)
    # 1 / log 2 < 3 , 1 / 2 pi <_ 1 / 6
    IL = '( 1 / ( log ` 2 ) )'
    zr = a1(w, a, w.s([], 'zrl2', '( ( 1 / 3 ) < ( log ` 2 ) /\\ ( log ` 2 ) < 1 )'), '( ( 1 / 3 ) < ( log ` 2 ) /\\ ( log ` 2 ) < 1 )')
    l2r = a1(w, a, w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'), '( log ` 2 ) e. RR')
    l2p0 = lin.linarith(w, a, [st([zr], 'simpld', '( 1 / 3 ) < ( log ` 2 )')], '0 < ( log ` 2 )', leaves={'( log ` 2 )': l2r})
    q13 = st([st([a1(w, a, num.real(w, '( 1 / 3 )'), '( 1 / 3 ) e. RR'), a1(w, a, num.fact(w, '( 1 / 3 )', 'gt0'), '0 < ( 1 / 3 )')], 'jca', '( ( 1 / 3 ) e. RR /\\ 0 < ( 1 / 3 ) )'),
              st([l2r, l2p0], 'jca', '( ( log ` 2 ) e. RR /\\ 0 < ( log ` 2 ) )'), w.inst('ltrec')], 'syl2anc', '( ( 1 / 3 ) < ( log ` 2 ) <-> %s < ( 1 / ( 1 / 3 ) ) )' % IL)
    rr3 = a1(w, a, w.s([w.s([], '3cn', '3 e. CC'), w.s([], '3ne0', '3 =/= 0'), w.inst('recrec')], 'mp2an', '( 1 / ( 1 / 3 ) ) = 3'), '( 1 / ( 1 / 3 ) ) = 3')
    ilb = st([st([st([zr], 'simpld', '( 1 / 3 ) < ( log ` 2 )'), q13], 'mpbid', '%s < ( 1 / ( 1 / 3 ) )' % IL), rr3], 'breqtrd', '%s < 3' % IL)
    ilr = st([l2r, st([l2p0], 'gt0ne0d', '( log ` 2 ) =/= 0')], 'rereccld', '%s e. RR' % IL)
    il0 = st([l2r, l2p0], 'recgt0d', '0 < %s' % IL)
    IT = '( 1 / %s )' % TPIa
    pir = a1(w, a, w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
    tpr = st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), pir], 'remulcld', '%s e. RR' % TPIa)
    p3_ = a1(w, a, w.s([], 'pige3', '3 <_ _pi'), '3 <_ _pi')
    tp6 = lin.linarith(w, a, [p3_], '6 <_ %s' % TPIa, leaves={'_pi': pir})
    tp0 = lin.linarith(w, a, [p3_], '0 < %s' % TPIa, leaves={'_pi': pir})
    itb = st([tp6, st([st([a1(w, a, w.s([], '6re', '6 e. RR'), '6 e. RR'), a1(w, a, w.s([], '6pos', '0 < 6'), '0 < 6')], 'jca', '( 6 e. RR /\\ 0 < 6 )'),
                       st([tpr, tp0], 'jca', '( %s e. RR /\\ 0 < %s )' % (TPIa, TPIa)), w.inst('lerec')], 'syl2anc', '( 6 <_ %s <-> %s <_ ( 1 / 6 ) )' % (TPIa, IT))], 'mpbid',
             '%s <_ ( 1 / 6 )' % IT)
    itr = st([tpr, st([tp0], 'gt0ne0d', '%s =/= 0' % TPIa)], 'rereccld', '%s e. RR' % IT)
    it0 = st([tpr, tp0], 'recgt0d', '0 < %s' % IT)
    # log D <_ ( log D ) ^ 3 / 4
    ld0 = lin.linarith(w, a, [l2], '0 <_ %s' % LD, leaves={LD: ldr})
    two_r = a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'); two0 = a1(w, a, w.s([], '0le2', '0 <_ 2'), '0 <_ 2')
    sq4 = st([two_r, ldr, two_r, ldr, two0, two0, l2, l2], 'lemul12ad', '( 2 x. 2 ) <_ ( %s x. %s )' % (LD, LD))
    LL = '( %s x. %s )' % (LD, LD)
    llr = st([ldr, ldr], 'remulcld', '%s e. RR' % LL)
    cb = st([st([two_r, two_r], 'remulcld', '( 2 x. 2 ) e. RR'), llr, ldr, ld0, sq4], 'lemul1ad', '( ( 2 x. 2 ) x. %s ) <_ ( %s x. %s )' % (LD, LL, LD))
    L3 = '( %s ^ 3 )' % LD
    l3e = ringeqp(w, a, '( %s x. %s )' % (LL, LD), L3, Closure(w, a, {LD: ldr}))
    l3r = st([ldr, a1(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '%s e. RR' % L3)
    L3Q = '( %s x. ( 1 / 4 ) )' % L3
    cb3 = st([cb, l3e], 'breqtrd', '( ( 2 x. 2 ) x. %s ) <_ %s' % (LD, L3))
    q4 = a1(w, a, num.real(w, '( 1 / 4 )'), '( 1 / 4 ) e. RR'); q40 = a1(w, a, num.fact(w, '( 1 / 4 )', 'ge0'), '0 <_ ( 1 / 4 )')
    FL = '( ( 2 x. 2 ) x. %s )' % LD
    flr = st([st([two_r, two_r], 'remulcld', '( 2 x. 2 ) e. RR'), ldr], 'remulcld', '%s e. RR' % FL)
    lq = st([flr, l3r, q4, q40, cb3], 'lemul1ad', '( %s x. ( 1 / 4 ) ) <_ %s' % (FL, L3Q))
    le_ = ringeq(w, a, LD, '( %s x. ( 1 / 4 ) )' % FL, Closure(w, a, {LD: ldr}))
    ldb = st([le_, lq], 'eqbrtrd', '%s <_ %s' % (LD, L3Q))
    # rewrite the product
    EACf = tsub(EAC, {'A': LM0f})
    RP801 = '( %s ^c ( ; ; 8 0 1 / ; ; 4 0 0 ) )' % RPf
    kr1, KLP1 = w.rewrite(KLPf, {EACf: (E1, e1), RP801: (E2, e2)}, a)
    KGLd = '( ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) / ( log ` 2 ) )'
    k24 = a1(w, a, w.s([num.real(w, '; ; ; 1 0 2 4'), num.real(w, '; ; ; 1 6 3 2')], 'remulcli', '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) e. RR'), '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) e. RR')
    dr_ = st([st([k24], 'recnd', '( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) e. CC'), st([l2r], 'recnd', '( log ` 2 ) e. CC'), st([l2p0], 'gt0ne0d', '( log ` 2 ) =/= 0')], 'divrecd',
             '%s = ( ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) x. %s )' % (KGLd, IL))
    kr2, KGL1 = w.rewrite(KGL, {KGLd: ('( ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) x. %s )' % IL, dr_)}, a)
    ctr = ctre(w, a)
    e1r = st([st([drp, x1r], 'rpcxpcld', '%s e. RR+' % E1)], 'rpred', '%s e. RR' % E1)
    e2r = st([st([drp, x2c], 'rpcxpcld', '%s e. RR+' % E2)], 'rpred', '%s e. RR' % E2)
    e3r = st([st([drp, x3r], 'rpcxpcld', '%s e. RR+' % D397)], 'rpred', '%s e. RR' % D397)
    cl = Closure(w, a, {'CTau': ctr, E1: e1r, E2: e2r, D397: e3r, LD: ldr, IL: ilr, IT: itr})
    Q = '( ( %s x. %s ) / %s )' % (KLPf, KGL, TPIa)
    PR1 = '( %s x. %s )' % (KLP1, KGL1)
    q1 = st([st([kr1, kr2], 'oveq12d', '( %s x. %s ) = %s' % (KLPf, KGL, PR1))], 'oveq1d', '%s = ( %s / %s )' % (Q, PR1, TPIa))
    tpc = st([tpr], 'recnd', '%s e. CC' % TPIa); tpn = st([tp0], 'gt0ne0d', '%s =/= 0' % TPIa)
    q2 = st([cl.mem(PR1, 'CC'), tpc, tpn], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (PR1, TPIa, PR1, IT))
    K0 = '( ( 2 x. %s ) x. ( ( ; 5 0 / ; 4 9 ) x. ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) ) )' % C12
    KK = '( %s x. ( CTau ^ 3 ) )' % K0
    IPIL = '( ( ( %s x. %s ) x. %s ) x. %s )' % (IL, P3, IT, LD)
    q3 = ringeqp(w, a, '( %s x. %s )' % (PR1, IT), '( %s x. %s )' % (KK, IPIL), cl)
    qe = st([st([q1, q2], 'eqtrd', '%s = ( %s x. %s )' % (Q, PR1, IT)), q3], 'eqtrd', '%s = ( %s x. %s )' % (Q, KK, IPIL))
    # the chain
    p3r = st([p3p], 'rpred', '%s e. RR' % P3); p30 = st([p3p], 'rpge0d', '0 <_ %s' % P3)
    three = a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')
    ilt = st([ilr, three, ilb], 'ltled', '%s <_ 3' % IL)
    il00 = st([st([], '0red', '0 e. RR'), ilr, il0], 'ltled', '0 <_ %s' % IL)
    m1 = st([ilr, three, p3r, d7r, il00, p30, ilt, p3b], 'lemul12ad', '( %s x. %s ) <_ ( 3 x. %s )' % (IL, P3, D7))
    IP = '( %s x. %s )' % (IL, P3)
    ipr = st([ilr, p3r], 'remulcld', '%s e. RR' % IP); ip0 = st([ilr, p3r, il00, p30], 'mulge0d', '0 <_ %s' % IP)
    it00 = st([st([], '0red', '0 e. RR'), itr, it0], 'ltled', '0 <_ %s' % IT)
    q6 = a1(w, a, num.real(w, '( 1 / 6 )'), '( 1 / 6 ) e. RR')
    D73 = '( 3 x. %s )' % D7
    d73r = st([three, d7r], 'remulcld', '%s e. RR' % D73)
    m2 = st([ipr, d73r, itr, q6, ip0, it00, m1, itb], 'lemul12ad', '( %s x. %s ) <_ ( %s x. ( 1 / 6 ) )' % (IP, IT, D73))
    IPT = '( %s x. %s )' % (IP, IT); D6 = '( %s x. ( 1 / 6 ) )' % D73
    iptr = st([ipr, itr], 'remulcld', '%s e. RR' % IPT); ipt0 = st([ipr, itr, ip0, it00], 'mulge0d', '0 <_ %s' % IPT)
    d6r = st([d73r, q6], 'remulcld', '%s e. RR' % D6)
    l3qr = st([l3r, q4], 'remulcld', '%s e. RR' % L3Q)
    m3 = st([iptr, d6r, ldr, l3qr, ipt0, ld0, m2, ldb], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (IPT, LD, D6, L3Q))
    k0r = cl.mem(K0, 'RR')
    NUMK = '( ; ; ; ; ; ; ; ; ; ; ; ; ; 2 5 0 6 7 5 2 0 0 0 0 0 0 0 / ; 4 9 )'
    NUMK8 = NUMK
    NK0 = '( ; ; ; ; ; ; ; ; ; ; ; ; ; ; 2 0 0 5 4 0 1 6 0 0 0 0 0 0 0 / ; 4 9 )'
    k0e = ringeq(w, a, K0, NK0, Closure(w, a, {}))
    k00 = st([a1(w, a, num.fact(w, NK0, 'ge0'), '0 <_ %s' % NK0), k0e], 'breqtrrd', '0 <_ %s' % K0)
    c3r = st([ctr, a1(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '( CTau ^ 3 ) e. RR')
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    cg0 = w.s([w.s([], '2re', '2 e. RR'), w.s([knn], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.s([], '0le2', '0 <_ 2'), w.inst('expge0')], 'mp3an', '0 <_ ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')
    ct0 = a1(w, a, w.s([cg0, w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')], 'breqtrri', '0 <_ CTau'), '0 <_ CTau')
    c30 = st([ctr, a1(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0'), ct0], 'expge0d', '0 <_ ( CTau ^ 3 )')
    kkr = st([k0r, c3r], 'remulcld', '%s e. RR' % KK); kk0 = st([k0r, c3r, k00, c30], 'mulge0d', '0 <_ %s' % KK)
    IPL = '( %s x. %s )' % (IPT, LD); DL = '( %s x. %s )' % (D6, L3Q)
    iplr = st([iptr, ldr], 'remulcld', '%s e. RR' % IPL); dlr = st([d6r, l3qr], 'remulcld', '%s e. RR' % DL)
    m4 = st([iplr, dlr, kkr, kk0, m3], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (KK, IPL, KK, DL))
    K08 = '( %s x. ( 1 / 8 ) )' % K0
    L3D = '( %s x. %s )' % (L3, D7)
    cl2 = Closure(w, a, {'CTau': ctr, D7: d7r, LD: ldr})
    fe = ringeqp(w, a, '( %s x. %s )' % (KK, DL), '( ( %s x. ( CTau ^ 3 ) ) x. %s )' % (K08, L3D), cl2)
    C11N = '; ; ; ; ; ; ; ; ; ; ; ; 2 0 0 0 0 0 0 0 0 0 0 0 0'
    k8e = ringeq(w, a, K08, NUMK8, Closure(w, a, {}))
    kb = st([k8e, a1(w, a, num.le_lit(w, NUMK8, C11N), '%s <_ %s' % (NUMK8, C11N))], 'eqbrtrd', '%s <_ %s' % (K08, C11N))
    k08r = cl.mem(K08, 'RR')
    c11r = a1(w, a, num.real(w, C11N), '%s e. RR' % C11N)
    cb1 = st([k08r, c11r, c3r, c30, kb], 'lemul1ad', '( %s x. ( CTau ^ 3 ) ) <_ ( %s x. ( CTau ^ 3 ) )' % (K08, C11N))
    l3d0 = st([l3r, d7r, st([ldr, a1(w, a, w.s([], '3nn0', '3 e. NN0'), '3 e. NN0'), ld0], 'expge0d', '0 <_ %s' % L3),
               st([st([drp, litr(w, a, '-u ( 7 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % D7)], 'rpge0d', '0 <_ %s' % D7)], 'mulge0d', '0 <_ %s' % L3D)
    l3dr = st([l3r, d7r], 'remulcld', '%s e. RR' % L3D)
    cb2 = st([st([k08r, c3r], 'remulcld', '( %s x. ( CTau ^ 3 ) ) e. RR' % K08), st([c11r, c3r], 'remulcld', '%s e. RR' % L_.C11), l3dr, l3d0, cb1], 'lemul1ad',
             '( ( %s x. ( CTau ^ 3 ) ) x. %s ) <_ ( %s x. %s )' % (K08, L3D, L_.C11, L3D))
    ass = st([st([st([st([c11r, c3r], 'remulcld', '%s e. RR' % L_.C11)], 'recnd', '%s e. CC' % L_.C11), st([l3r], 'recnd', '%s e. CC' % L3), st([d7r], 'recnd', '%s e. CC' % D7)],
                 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (L_.C11, L3, D7, L_.C11, L3D))], 'eqcomd', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (L_.C11, L3D, L_.C11, L3, D7))
    ch1 = st([qe, m4], 'eqbrtrd', '%s <_ ( %s x. %s )' % (Q, KK, DL))
    ch2 = st([ch1, fe], 'breqtrd', '%s <_ ( ( %s x. ( CTau ^ 3 ) ) x. %s )' % (Q, K08, L3D))
    qrr = st([qe, st([kkr, iplr], 'remulcld', '( %s x. %s ) e. RR' % (KK, IPL))], 'eqeltrd', '%s e. RR' % Q)
    ch3 = st([qrr, st([st([k08r, c3r], 'remulcld', '( %s x. ( CTau ^ 3 ) ) e. RR' % K08), l3dr], 'remulcld', '( ( %s x. ( CTau ^ 3 ) ) x. %s ) e. RR' % (K08, L3D)),
              st([st([c11r, c3r], 'remulcld', '%s e. RR' % L_.C11), l3dr], 'remulcld', '( %s x. %s ) e. RR' % (L_.C11, L3D)), ch2, cb2], 'letrd', '%s <_ ( %s x. %s )' % (Q, L_.C11, L3D))
    fin = st([ch3, ass], 'breqtrd', split_imp(S_['gf2num'])[1])
    w.qed([fin], 'idi', S_['gf2num'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
