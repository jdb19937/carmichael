"""Sortie ZR, REP: zrwin (window geometry), zrlc1, zrlc0, zrlc (Lean localCount_le and its two engines)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of
from zr_f import sq_mem


def box_facts(w, A, sr, tr, vin, V='V'):
    """from ( A -> V e. BOXR ): V e. CC, S <_ Re V, Re V <_ 1, -u T <_ Im V, Im V <_ T (steps), Re/Im reals"""
    c = Ctx(w, A)
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    CA, CB = '( S + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
    ntr = c([tr], 'renegcld', '-u T e. RR')
    cac = c([c([sr], 'recnd', 'S e. CC'), c([ic, c([ntr], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = c([c([], '1cnd', '1 e. CC'), c([ic, c([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CB)
    RA, RB, IA, IB = '( Re ` %s )' % CA, '( Re ` %s )' % CB, '( Im ` %s )' % CA, '( Im ` %s )' % CB
    ra = c([sr, ntr, w.inst('crre')], 'syl2anc', '%s = S' % RA)
    rb = c([c([], '1red', '1 e. RR'), tr, w.inst('crre')], 'syl2anc', '%s = 1' % RB)
    ia = c([sr, ntr, w.inst('crim')], 'syl2anc', '%s = -u T' % IA)
    ib = c([c([], '1red', '1 e. RR'), tr, w.inst('crim')], 'syl2anc', '%s = T' % IB)
    EL = '( %s e. CC /\\ ( Re ` %s ) e. ( %s [,] %s ) /\\ ( Im ` %s ) e. ( %s [,] %s ) )' % (V, V, RA, RB, V, IA, IB)
    el = c([vin, c([cac, cbc, w.inst('elcrect')], 'syl2anc', '( %s e. ( %s crect %s ) <-> %s )' % (V, CA, CB, EL))], 'mpbid', EL)
    vc = c([el], 'simp1d', '%s e. CC' % V)
    rar, rbr = c([cac], 'recld', '%s e. RR' % RA), c([cbc], 'recld', '%s e. RR' % RB)
    iar, ibr = c([cac], 'imcld', '%s e. RR' % IA), c([cbc], 'imcld', '%s e. RR' % IB)
    RV, IV = '( Re ` %s )' % V, '( Im ` %s )' % V
    e1 = c([c([el], 'simp2d', '%s e. ( %s [,] %s )' % (RV, RA, RB)), c([rar, rbr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (RV, RA, RB, RV, RA, RV, RV, RB))],
           'mpbid', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (RV, RA, RV, RV, RB))
    e2 = c([c([el], 'simp3d', '%s e. ( %s [,] %s )' % (IV, IA, IB)), c([iar, ibr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (IV, IA, IB, IV, IA, IV, IV, IB))],
           'mpbid', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (IV, IA, IV, IV, IB))
    rvr = c([vc], 'recld', '%s e. RR' % RV); ivr = c([vc], 'imcld', '%s e. RR' % IV)
    lv = {RA: rar, RB: rbr, IA: iar, IB: ibr, RV: rvr, IV: ivr, 'S': sr, 'T': tr}
    f1 = lin8(w, A, [ra, c([e1], 'simp2d', '%s <_ %s' % (RA, RV))], 'S <_ %s' % RV, lv)
    f2 = lin8(w, A, [rb, c([e1], 'simp3d', '%s <_ %s' % (RV, RB))], '%s <_ 1' % RV, lv)
    f3 = lin8(w, A, [ia, c([e2], 'simp2d', '%s <_ %s' % (IA, IV))], '-u T <_ %s' % IV, lv)
    f4 = lin8(w, A, [ib, c([e2], 'simp3d', '%s <_ %s' % (IV, IB))], '%s <_ T' % IV, lv)
    return vc, rvr, ivr, f1, f2, f3, f4


def gen_win():
    w = W('zrwin', 'Lean ` dist_le_eta ` , ` mem_closedBall_two_of_dist_le ` : a point of the box ` [ S , 1 ] x. [ - T , T ] ` within ` E <_ 1 / 25 ` of the height ` U ` lies in the square ` SQ ( 2 + i U , 13 / 8 ) ` , within ` ( 1 - S ) + E ` of ` 1 + i U ` .')
    A0 = ante_of(S['zrwin'])[0]
    c = Ctx(w, A0)
    sr, s99, tr, ur, er, e25, vin, vim = [c.g(x) for x in ('S e. RR', '( ; 9 9 / ; ; 1 0 0 ) <_ S', 'T e. RR', 'U e. RR', 'E e. RR', 'E <_ ( 1 / ; 2 5 )', 'V e. %s' % BOXR,
                                                          '( abs ` ( ( Im ` V ) - U ) ) <_ E')]
    vc, rvr, ivr, f1, f2, f3, f4 = box_facts(w, A0, sr, tr, vin)
    RV, IV = '( Re ` V )', '( Im ` V )'
    IU = '( %s - U )' % IV
    iur = c([ivr, ur], 'resubcld', '%s e. RR' % IU)
    ab = c([vim, c([iur, er], 'absled', '( ( abs ` %s ) <_ E <-> ( -u E <_ %s /\\ %s <_ E ) )' % (IU, IU, IU))], 'mpbid', '( -u E <_ %s /\\ %s <_ E )' % (IU, IU))
    a1, a2 = c([ab], 'simpld', '-u E <_ %s' % IU), c([ab], 'simprd', '%s <_ E' % IU)
    lv = {RV: rvr, IV: ivr, 'S': sr, 'U': ur, 'E': er}
    sq0 = sq_memU(w, A0, ur, RV, rvr, IV, ivr, [s99, f1, f2, a1, a2, e25], lv)
    rp = c([vc, w.inst('replim')], 'syl', 'V = ( %s + ( _i x. %s ) )' % (RV, IV))
    sq1 = c([c([rp], 'eleq1d', '( V e. %s <-> ( %s + ( _i x. %s ) ) e. %s )' % (SQ13('U'), RV, IV, SQ13('U'))), sq0], 'mpbird', 'V e. %s' % SQ13('U'))
    # distance
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    cl = Closure(w, A0, {RV: ('CC', c([rvr], 'recnd', '%s e. CC' % RV)), IV: ('CC', c([ivr], 'recnd', '%s e. CC' % IV)), 'U': ('CC', c([ur], 'recnd', 'U e. CC')), '_i': ('CC', ic)})
    for a_ in (RV, IV, 'U', '_i'):
        cl.atom(a_)
    R1, R2 = '( %s - 1 )' % RV, IU
    dq = c([c([rp], 'oveq1d', '( V - ( 1 + ( _i x. U ) ) ) = ( ( %s + ( _i x. %s ) ) - ( 1 + ( _i x. U ) ) )' % (RV, IV)),
            ringeq(w, A0, '( ( %s + ( _i x. %s ) ) - ( 1 + ( _i x. U ) ) )' % (RV, IV), '( %s + ( _i x. %s ) )' % (R1, R2), cl)], 'eqtrd', '( V - ( 1 + ( _i x. U ) ) ) = ( %s + ( _i x. %s ) )' % (R1, R2))
    r1c, r2c = cl.mem(R1, 'CC'), cl.mem(R2, 'CC')
    at = c([r1c, c([ic, r2c], 'mulcld', '( _i x. %s ) e. CC' % R2)], 'abstrid', '( abs ` ( %s + ( _i x. %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( _i x. %s ) ) )' % (R1, R2, R1, R2))
    am = c([ic, r2c], 'absmuld', '( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) )' % (R2, R2))
    ai = c.a1(w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1')
    r1r = c([rvr, c([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % R1)
    oms = c([c([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR')
    a1b = c([c([lin8(w, A0, [f1, f2], '-u ( 1 - S ) <_ %s' % R1, lv), lin8(w, A0, [f1, f2, s99], '%s <_ ( 1 - S )' % R1, lv)], 'jca', '( -u ( 1 - S ) <_ %s /\\ %s <_ ( 1 - S ) )' % (R1, R1)),
             c([r1r, oms], 'absled', '( ( abs ` %s ) <_ ( 1 - S ) <-> ( -u ( 1 - S ) <_ %s /\\ %s <_ ( 1 - S ) ) )' % (R1, R1, R1))], 'mpbird', '( abs ` %s ) <_ ( 1 - S )' % R1)
    AV = '( abs ` ( V - ( 1 + ( _i x. U ) ) ) )'
    lvd = {AV: c([c([vc, cl.mem('( 1 + ( _i x. U ) )', 'CC')], 'subcld', '( V - ( 1 + ( _i x. U ) ) ) e. CC')], 'abscld', '%s e. RR' % AV),
           '( abs ` ( %s + ( _i x. %s ) ) )' % (R1, R2): c([c([r1c, c([ic, r2c], 'mulcld', '( _i x. %s ) e. CC' % R2)], 'addcld', '( %s + ( _i x. %s ) ) e. CC' % (R1, R2))], 'abscld', '( abs ` ( %s + ( _i x. %s ) ) ) e. RR' % (R1, R2)),
           '( abs ` %s )' % R1: c([r1c], 'abscld', '( abs ` %s ) e. RR' % R1), '( abs ` ( _i x. %s ) )' % R2: c([c([ic, r2c], 'mulcld', '( _i x. %s ) e. CC' % R2)], 'abscld', '( abs ` ( _i x. %s ) ) e. RR' % R2),
           '( abs ` _i )': c([ic], 'abscld', '( abs ` _i ) e. RR'), '( abs ` %s )' % R2: c([r2c], 'abscld', '( abs ` %s ) e. RR' % R2), 'S': sr, 'E': er}
    ad = c([dq], 'fveq2d', '%s = ( abs ` ( %s + ( _i x. %s ) ) )' % (AV, R1, R2))
    ar2 = c([r2c], 'abscld', '( abs ` %s ) e. RR' % R2)
    am2 = c([am, c([c([ai], 'oveq1d', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) )' % (R2, R2)), c([c([ar2], 'recnd', '( abs ` %s ) e. CC' % R2)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (R2, R2))],
                    'eqtrd', '( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s )' % (R2, R2))], 'eqtrd', '( abs ` ( _i x. %s ) ) = ( abs ` %s )' % (R2, R2))
    dist = lin8(w, A0, [ad, at, am2, a1b, vim], '%s <_ ( ( 1 - S ) + E )' % AV, lvd, products=True)
    hp = c([c([vc, lin8(w, A0, [f1, s99], '0 < %s' % RV, lv)], 'jca', '( V e. CC /\\ 0 < %s )' % RV), c([c([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( V e. %s <-> ( V e. CC /\\ 0 < %s ) )' % (HP0, RV))],
           'mpbird', 'V e. %s' % HP0)
    fin = c([sq1, dist, hp], '3jca', ante_of(S['zrwin'])[1])
    w.qed([fin], 'idi', S['zrwin'])
    return run8(w)


def sq_memU(w, A, ur, X, xr, Y, yr, hyps, lv):
    """( A -> ( X + ( _i x. Y ) ) e. SQ13(U) )"""
    c = Ctx(w, A)
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    cl = Closure(w, A, {'U': ('RR', ur), '_i': ('CC', ic)})
    cl.atom('U'); cl.atom('_i')
    SA = '( %s - ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('U')
    SB = '( %s + ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) )' % C2T('U')
    FA, FB = '( ( 3 / 8 ) + ( _i x. ( U - ( ; 1 3 / 8 ) ) ) )', '( ( ; 2 9 / 8 ) + ( _i x. ( U + ( ; 1 3 / 8 ) ) ) )'
    ea = ringeq(w, A, SA, FA, cl); eb = ringeq(w, A, SB, FB, cl)
    c38, c298 = numst8(w, A, '( 3 / 8 )', 'RR'), numst8(w, A, '( ; 2 9 / 8 )', 'RR')
    tm = c([ur, numst8(w, A, '( ; 1 3 / 8 )', 'RR')], 'resubcld', '( U - ( ; 1 3 / 8 ) ) e. RR')
    tp = c([ur, numst8(w, A, '( ; 1 3 / 8 )', 'RR')], 'readdcld', '( U + ( ; 1 3 / 8 ) ) e. RR')
    ra = c([c([ea], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (SA, FA)), c([c38, tm, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 3 / 8 )' % FA)], 'eqtrd', '( Re ` %s ) = ( 3 / 8 )' % SA)
    rb = c([c([eb], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (SB, FB)), c([c298, tp, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( ; 2 9 / 8 )' % FB)], 'eqtrd', '( Re ` %s ) = ( ; 2 9 / 8 )' % SB)
    ia = c([c([ea], 'fveq2d', '( Im ` %s ) = ( Im ` %s )' % (SA, FA)), c([c38, tm, w.inst('crim')], 'syl2anc', '( Im ` %s ) = ( U - ( ; 1 3 / 8 ) )' % FA)], 'eqtrd', '( Im ` %s ) = ( U - ( ; 1 3 / 8 ) )' % SA)
    ib = c([c([eb], 'fveq2d', '( Im ` %s ) = ( Im ` %s )' % (SB, FB)), c([c298, tp, w.inst('crim')], 'syl2anc', '( Im ` %s ) = ( U + ( ; 1 3 / 8 ) )' % FB)], 'eqtrd', '( Im ` %s ) = ( U + ( ; 1 3 / 8 ) )' % SB)
    sac, sbc = cl.mem(SA, 'CC'), cl.mem(SB, 'CC')
    RA, RB, IA, IB = ['( %s ` %s )' % (f, x) for f, x in (('Re', SA), ('Re', SB), ('Im', SA), ('Im', SB))]
    rar, rbr = c([sac], 'recld', '%s e. RR' % RA), c([sbc], 'recld', '%s e. RR' % RB)
    iar, ibr = c([sac], 'imcld', '%s e. RR' % IA), c([sbc], 'imcld', '%s e. RR' % IB)
    lv2 = dict(lv); lv2.update({RA: rar, RB: rbr, IA: iar, IB: ibr, 'U': ur, X: xr, Y: yr})
    i1 = c([c([xr, lin8(w, A, [ra] + hyps, '%s <_ %s' % (RA, X), lv2), lin8(w, A, [rb] + hyps, '%s <_ %s' % (X, RB), lv2)], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (X, RA, X, X, RB)),
            c([rar, rbr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (X, RA, RB, X, RA, X, X, RB))], 'mpbird', '%s e. ( %s [,] %s )' % (X, RA, RB))
    i2 = c([c([yr, lin8(w, A, [ia] + hyps, '%s <_ %s' % (IA, Y), lv2), lin8(w, A, [ib] + hyps, '%s <_ %s' % (Y, IB), lv2)], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (Y, IA, Y, Y, IB)),
            c([iar, ibr, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (Y, IA, IB, Y, IA, Y, Y, IB))], 'mpbird', '%s e. ( %s [,] %s )' % (Y, IA, IB))
    P = '( %s + ( _i x. %s ) )' % (X, Y)
    return c([c([c([sac, sbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), c([i1, i2], 'jca', '( %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) )' % (X, RA, RB, Y, IA, IB))], 'jca',
                 '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) ) )' % (SA, SB, X, RA, RB, Y, IA, IB)), w.inst('crectpt')], 'syl', '%s e. %s' % (P, SQ13('U')))


GENS = {'zrwin': gen_win}


LFNX = '( s e. ( `\' Re " ( 0 (,) +oo ) ) |-> sum_ k e. NN ( sum_ i e. ( 1 ... k ) ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` i ) ) x. ( ( k ^c -u s ) - ( ( k + 1 ) ^c -u s ) ) ) )'


def eta_facts(w, A0, sr, s99, s1, lr, lp, l25):
    """eta = ( 1 - S ) + ( 1 / LD ): ( A0 -> eta e. RR+ ), eta <_ 1/20, ( 1 / LD ) <_ 1 / 25, ( 1 / LD ) x. LD = 1, 1 / LD real"""
    c = Ctx(w, A0)
    IL = '( 1 / %s )' % LD
    l0 = c([lp], 'gt0ne0d', '%s =/= 0' % LD)
    ilr = c([c([], '1red', '1 e. RR'), lr, l0], 'redivcld', '%s e. RR' % IL)
    ill = c([c([], '1cnd', '1 e. CC'), c([lr], 'recnd', '%s e. CC' % LD), l0], 'divcan1d', '( %s x. %s ) = 1' % (IL, LD))
    # 1 / LD <_ 1 / 25
    lrp = c([lr, lp], 'elrpd', '%s e. RR+' % LD)
    i25 = c([numst8(w, A0, '; 2 5', 'RR+'), lrp, c([], '1red', '1 e. RR'), lin8(w, A0, [], '0 <_ 1', {}), l25], 'lediv2ad', '%s <_ ( 1 / ; 2 5 )' % IL)
    ilp = c([c([], '1red', '1 e. RR'), lrp, lin8(w, A0, [], '0 <_ 1', {})], 'divge0d', '0 <_ %s' % IL)
    ilpp = c([lrp], 'rpreccld', '%s e. RR+' % IL)
    er = c([c([c([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR'), ilr], 'readdcld', '%s e. RR' % ETAW)
    lv = {'S': sr, IL: ilr}
    ep = c([er, lin8(w, A0, [s1, c([ilpp], 'rpgt0d', '0 < %s' % IL)], '0 < %s' % ETAW, lv)], 'elrpd', '%s e. RR+' % ETAW)
    e20 = lin8(w, A0, [s99, i25], '%s <_ ( 1 / ; 2 0 )' % ETAW, lv)
    return IL, ilr, ill, i25, ilp, er, ep, e20, lrp


def gen_lc1():
    from ef4_g import elrab_unpack, elrab_pack
    from zr_i import scale_facts
    w = W('zrlc1', 'Lean ` localCount_le_of_ne_one ` : for ` chi =/= 1 ` the zeros in the box within ` 1 / L ` of the height ` U ` number at most ` 6 + 7 . 10 ^ 7 ( 1 + ( 1 - S ) L ) ` , ` L = log ( N ( T + 2 ) ) ` ( ~ sdzc at radius ` ( 1 - S ) + 1 / L ` , ~ zrwin , ~ zc1eord ).')
    A0 = ante_of(S['zrlc1'])[0]
    c = Ctx(w, A0)
    nn_, xb, x0, sr, s99, s1, tr, t0, l25, ur, ut = [c.g(x) for x in ('N e. NN', 'X e. ( Base ` ( DChr ` N ) )', 'X =/= ( 0g ` ( DChr ` N ) )', 'S e. RR',
                                                                    '( ; 9 9 / ; ; 1 0 0 ) <_ S', 'S <_ 1', 'T e. RR', '0 <_ T', '; 2 5 <_ %s' % LD, 'U e. RR', '( abs ` U ) <_ T')]
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    IL, ilr, ill, i25, ilp, er, ep, e20, lrp = eta_facts(w, A0, sr, s99, s1, lr, lp, l25)
    NXX = '( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ X =/= ( 0g ` ( DChr ` N ) ) )'
    nxx = c([c([nn_, xb], 'jca', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'), x0], 'jca', NXX)
    ZSL = '{ r e. %s | ( %s ` r ) = 0 }' % (SQ13('U'), LFNX)
    DSK1 = '{ p e. %s | ( abs ` ( p - ( 1 + ( _i x. U ) ) ) ) <_ %s }' % (ZSL, ETAW)
    sd = c([c([nxx, c([ur, c([ep, e20], 'jca', '( %s e. RR+ /\\ %s <_ ( 1 / ; 2 0 ) )' % (ETAW, ETAW))], 'jca', '( U e. RR /\\ ( %s e. RR+ /\\ %s <_ ( 1 / ; 2 0 ) ) )' % (ETAW, ETAW))], 'jca',
               ante_of(tsub(stmt('sdzc'), {'T': 'U', 'W': ETAW}))[0]), w.inst('sdzc')], 'syl', ante_of(tsub(stmt('sdzc'), {'T': 'U', 'W': ETAW}))[1])
    lz = c([c([nxx, ur], 'jca', '( %s /\\ U e. RR )' % NXX), w.inst('lchrzc8')], 'syl', ante_of(tsub(stmt('lchrzc8'), {'T': 'U'}))[1])
    zfin = c([lz], 'simp1d', '%s e. Fin' % ZSL)
    zal = c([lz], 'simp2d', 'A. q e. %s ( %s holord q ) e. NN' % (ZSL, LFNX))
    dss = c.a1(w.s([], 'ssrab2', '%s C_ %s' % (DSK1, ZSL)), '%s C_ %s' % (DSK1, ZSL))
    dfin = c([zfin, dss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % DSK1)
    WIN = '{ v e. %s | ( abs ` ( ( Im ` v ) - U ) ) <_ %s }' % (ZFX('X'), IL)
    # WIN C_ DSK1, with orders
    Av = '( %s /\\ q e. %s )' % (A0, WIN)
    cv = Ctx(w, Av)
    qw = cv([], 'simpr', 'q e. %s' % WIN)
    qz, qim, _ = elrab_unpack(w, Av, 'v', ZFX('X'), '( abs ` ( ( Im ` v ) - U ) ) <_ %s' % IL, 'q', qw)
    qb, qp, _ = elrab_unpack(w, Av, 'r', BOXR, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX('X'), 'q', qz)
    qn1 = cv([qp], 'simpld', 'q =/= 1'); qe0 = cv([qp], 'simprd', '( %s ` q ) = 0' % EX('X'))
    L_ = lambda st: lift(w, st, Av)
    WA = ante_of(tsub(S['zrwin'], {'E': IL, 'V': 'q'}))
    wn = cv([cv([cv([L_(sr), L_(s99)], 'jca', top_and(WA[0])[0]), cv([L_(tr), L_(ur), L_(ilr)], '3jca', top_and(WA[0])[1]), cv([L_(i25), cv([qb, qim], 'jca', top_and(top_and(WA[0])[2])[1])], 'jca', top_and(WA[0])[2])],
                 '3jca', WA[0]), w.inst('zrwin')], 'syl', WA[1])
    qsq = cv([wn], 'simp1d', 'q e. %s' % SQ13('U')); qds = cv([wn], 'simp2d', '( abs ` ( q - ( 1 + ( _i x. U ) ) ) ) <_ %s' % ETAW); qh = cv([wn], 'simp3d', 'q e. %s' % HP0)
    EO = ante_of(tsub(stmt('zc1eord'), {'P': 'q'}))
    eo = cv([cv([L_(nxx), cv([qh, qn1], 'jca', '( q e. %s /\\ q =/= 1 )' % HP0)], 'jca', EO[0]), w.inst('zc1eord')], 'syl', EO[1])
    oq = cv([eo], 'simpld', '( %s holord q ) = ( %s holord q )' % (EX('X'), LFNX))
    lq0 = cv([qe0, cv([eo], 'simprd', '( ( %s ` q ) = 0 <-> ( %s ` q ) = 0 )' % (EX('X'), LFNX))], 'mpbid', '( %s ` q ) = 0' % LFNX)
    qzl = elrab_pack(w, Av, 'r', SQ13('U'), '( %s ` r ) = 0' % LFNX, 'q', qsq, lq0)
    qdk = elrab_pack(w, Av, 'p', ZSL, '( abs ` ( p - ( 1 + ( _i x. U ) ) ) ) <_ %s' % ETAW, 'q', qzl, qds)
    wss = c([w.s([qdk], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, WIN, DSK1))], 'ssrdv', '%s C_ %s' % (WIN, DSK1))
    OL = '( %s holord q )' % LFNX
    se = c([oq], 'sumeq2dv', '%s = sum_ q e. %s %s' % (LCX('X', 'U'), WIN, OL))
    Ad = '( %s /\\ q e. %s )' % (A0, DSK1)
    cd = Ctx(w, Ad)
    qzl2 = cd([cd([], 'simpr', 'q e. %s' % DSK1), w.inst('elrabi')], 'syl', 'q e. %s' % ZSL)
    Az = '( %s /\\ q e. %s )' % (A0, ZSL)
    zn = w.s([zal], 'r19.21bi', '( %s -> %s e. NN )' % (Az, OL))
    zn2 = cd([cd([cd.g(A0), qzl2], 'jca', Az), zn], 'syl', '%s e. NN' % OL)
    fl = c([dfin, cd([zn2], 'nnred', '%s e. RR' % OL), cd([cd([zn2], 'nnnn0d', '%s e. NN0' % OL)], 'nn0ge0d', '0 <_ %s' % OL), wss],
           'fsumless', 'sum_ q e. %s %s <_ sum_ q e. %s %s' % (WIN, OL, DSK1, OL))
    LNU = '( log ` ( N x. ( ( abs ` U ) + 2 ) ) )'
    NU = '( N x. ( ( abs ` U ) + 2 ) )'
    uc = c([ur], 'recnd', 'U e. CC')
    aur = c([uc], 'abscld', '( abs ` U ) e. RR')
    nr = c([nn_], 'nnred', 'N e. RR')
    nur = c([nr, c([aur, numst8(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` U ) + 2 ) e. RR')], 'remulcld', '%s e. RR' % NU)
    hnu = c([nr, c([tr, aur], 'resubcld', '( T - ( abs ` U ) ) e. RR'), lin8(w, A0, [c([nn_], 'nnge1d', '1 <_ N')], '0 <_ N', {'N': nr}), lin8(w, A0, [ut], '0 <_ ( T - ( abs ` U ) )', {'( abs ` U )': aur, 'T': tr})],
            'mulge0d', '0 <_ ( N x. ( T - ( abs ` U ) ) )')
    nule = lin8(w, A0, [hnu], '%s <_ ( N x. ( T + 2 ) )' % NU, {'N': nr, '( abs ` U )': aur, 'T': tr}, products=True)
    hnp = c([nr, c([aur, numst8(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` U ) + 2 ) e. RR'), lin8(w, A0, [c([nn_], 'nnge1d', '1 <_ N')], '0 < N', {'N': nr}),
             lin8(w, A0, [c([uc], 'absge0d', '0 <_ ( abs ` U )')], '0 < ( ( abs ` U ) + 2 )', {'( abs ` U )': aur})], 'mulgt0d', '0 < %s' % NU)
    nup = c([nur, hnp], 'elrpd', '%s e. RR+' % NU)
    ll = c([nule, c([nup, c([dr, lin8(w, A0, [d2], '0 < ( N x. ( T + 2 ) )', {'( N x. ( T + 2 ) )': dr})], 'elrpd', '( N x. ( T + 2 ) ) e. RR+'), w.inst('logleb')], 'syl2anc',
                   '( %s <_ ( N x. ( T + 2 ) ) <-> %s <_ %s )' % (NU, LNU, LD))], 'mpbid', '%s <_ %s' % (LNU, LD))
    lnur = c([nup], 'relogcld', '%s e. RR' % LNU)
    hh = c([er, c([lr, lnur], 'resubcld', '( %s - %s ) e. RR' % (LD, LNU)), c([ep], 'rpge0d', '0 <_ %s' % ETAW), lin8(w, A0, [ll], '0 <_ ( %s - %s )' % (LD, LNU), {LD: lr, LNU: lnur})],
           'mulge0d', '0 <_ ( %s x. ( %s - %s ) )' % (ETAW, LD, LNU))
    S1 = 'sum_ q e. %s %s' % (WIN, OL); S2 = 'sum_ q e. %s %s' % (DSK1, OL)
    wfin = c([dfin, wss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % WIN)
    Aw = '( %s /\\ q e. %s )' % (A0, WIN)
    cw = Ctx(w, Aw)
    wq_d = cw([cw.g(A0), cw([lift(w, wss, Aw), cw([], 'simpr', 'q e. %s' % WIN)], 'sseldd', 'q e. %s' % DSK1)], 'jca', Ad)
    s1r = c([wfin, w.s([wq_d, cd([zn2], 'nnred', '%s e. RR' % OL)], 'syl', '( %s -> %s e. RR )' % (Aw, OL))], 'fsumrecl', '%s e. RR' % S1)
    s2r = c([dfin, cd([zn2], 'nnred', '%s e. RR' % OL)], 'fsumrecl', '%s e. RR' % S2)
    lcr = c([se, s1r], 'eqeltrd', '%s e. RR' % LCX('X', 'U'))
    lv = {LCX('X', 'U'): lcr, S1: s1r, S2: s2r, LD: lr, LNU: lnur, IL: ilr, 'S': sr}
    fin = lin8(w, A0, [se, fl, sd, hh, ill], ante_of(S['zrlc1'])[1], lv, products=True)
    w.qed([fin], 'idi', S['zrlc1'])
    return run8(w)


GENS['zrlc1'] = gen_lc1


def gen_lc0():
    from ef4_g import elrab_unpack, elrab_pack
    from zr_i import scale_facts
    from zr_f import e12
    w = W('zrlc0', 'Lean ` localCount_le_of_eq_one ` : for the principal character the zeros in the box within ` 1 / L ` of the height ` U ` number at most ` 12 + 4 K ( 1 + ( 1 - S ) L ) ` ( ~ zc1tord , ~ zc1ezt , ~ zrsdz ).')
    A0 = ante_of(S['zrlc0'])[0]
    c = Ctx(w, A0)
    nn_, xb, x0, sr, s99, s1, tr, t0, l25, ur, ut = [c.g(x) for x in ('N e. NN', 'X e. ( Base ` ( DChr ` N ) )', 'X = ( 0g ` ( DChr ` N ) )', 'S e. RR',
                                                                    '( ; 9 9 / ; ; 1 0 0 ) <_ S', 'S <_ 1', 'T e. RR', '0 <_ T', '; 2 5 <_ %s' % LD, 'U e. RR', '( abs ` U ) <_ T')]
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    IL, ilr, ill, i25, ilp, er, ep, e20, lrp = eta_facts(w, A0, sr, s99, s1, lr, lp, l25)
    NXX = '( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ X = ( 0g ` ( DChr ` N ) ) )'
    nxx = c([c([nn_, xb], 'jca', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'), x0], 'jca', NXX)
    DSK = DISK('U', ETAW)
    sd = c([c([ur, c([ep, e20], 'jca', '( %s e. RR+ /\\ %s <_ ( 1 / ; 2 0 ) )' % (ETAW, ETAW))], 'jca', ante_of(tsub(S['zrsdz'], {'T': 'U', 'W': ETAW}))[0]), w.inst('zrsdz')], 'syl',
           ante_of(tsub(S['zrsdz'], {'T': 'U', 'W': ETAW}))[1])
    fz = c([ur, w.inst('etazc')], 'syl', tsub(ante_of(stmt('etazc'))[1], {'T': 'U'}))
    zfin = c([fz], 'simp1d', '%s e. Fin' % ZSE('U'))
    dss = c.a1(w.s([], 'ssrab2', '%s C_ %s' % (DSK, ZSE('U'))), '%s C_ %s' % (DSK, ZSE('U')))
    dfin = c([zfin, dss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % DSK)
    WIN = '{ v e. %s | ( abs ` ( ( Im ` v ) - U ) ) <_ %s }' % (ZFX('X'), IL)
    Av = '( %s /\\ q e. %s )' % (A0, WIN)
    cv = Ctx(w, Av)
    qw = cv([], 'simpr', 'q e. %s' % WIN)
    qz, qim, _ = elrab_unpack(w, Av, 'v', ZFX('X'), '( abs ` ( ( Im ` v ) - U ) ) <_ %s' % IL, 'q', qw)
    qb, qp, _ = elrab_unpack(w, Av, 'r', BOXR, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX('X'), 'q', qz)
    qn1 = cv([qp], 'simpld', 'q =/= 1'); qe0 = cv([qp], 'simprd', '( %s ` q ) = 0' % EX('X'))
    L_ = lambda st: lift(w, st, Av)
    WA = ante_of(tsub(S['zrwin'], {'E': IL, 'V': 'q'}))
    wn = cv([cv([cv([L_(sr), L_(s99)], 'jca', top_and(WA[0])[0]), cv([L_(tr), L_(ur), L_(ilr)], '3jca', top_and(WA[0])[1]), cv([L_(i25), cv([qb, qim], 'jca', top_and(top_and(WA[0])[2])[1])], 'jca', top_and(WA[0])[2])],
                 '3jca', WA[0]), w.inst('zrwin')], 'syl', WA[1])
    qsq = cv([wn], 'simp1d', 'q e. %s' % SQ13('U')); qds = cv([wn], 'simp2d', '( abs ` ( q - ( 1 + ( _i x. U ) ) ) ) <_ %s' % ETAW); qh = cv([wn], 'simp3d', 'q e. %s' % HP0)
    TO = ante_of(tsub(stmt('zc1tord'), {'P': 'q'}))
    to = cv([cv([L_(nxx), qh], 'jca', TO[0]), w.inst('zc1tord')], 'syl', TO[1])
    oq = cv([to], 'simpld', '( %s holord q ) = ( %s holord q )' % (EX('X'), E1))
    e1z = cv([qe0, cv([to], 'simprd', '( ( %s ` q ) = 0 <-> ( %s ` q ) = 0 )' % (EX('X'), E1))], 'mpbid', '( %s ` q ) = 0' % E1)
    ZT = ante_of(tsub(stmt('zc1ezt'), {'P': 'q'}))
    zt = cv([cv([qh, qn1], 'jca', ZT[0]), w.inst('zc1ezt')], 'syl', ZT[1])
    etz = cv([e1z, cv([zt], 'simprd', '( ( %s ` q ) = 0 -> ( %s ` q ) = 0 )' % (E1, ETA))], 'mpd', '( %s ` q ) = 0' % ETA)
    qzl = elrab_pack(w, Av, 'r', SQ13('U'), '( %s ` r ) = 0' % ETA, 'q', qsq, etz)
    qdk = elrab_pack(w, Av, 'p', ZSE('U'), '( abs ` ( p - ( 1 + ( _i x. U ) ) ) ) <_ %s' % ETAW, 'q', qzl, qds)
    wss = c([w.s([qdk], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, WIN, DSK))], 'ssrdv', '%s C_ %s' % (WIN, DSK))
    OL = '( %s holord q )' % E1
    se = c([oq], 'sumeq2dv', '%s = sum_ q e. %s %s' % (LCX('X', 'U'), WIN, OL))
    Ad = '( %s /\\ q e. %s )' % (A0, DSK)
    cd = Ctx(w, Ad)
    qzl2 = cd([cd([], 'simpr', 'q e. %s' % DSK), w.inst('elrabi')], 'syl', 'q e. %s' % ZSE('U'))
    zs = cd([cd([lift(w, ur, Ad), qzl2], 'jca', '( U e. RR /\\ q e. %s )' % ZSE('U')), w.inst('zrzs')], 'syl', tsub(ante_of(S['zrzs'])[1], {'T': 'U', 'Q': 'q'}))
    qh2 = cd([cd([zs], 'simp1d', '( q e. %s /\\ ( %s ` q ) = 0 )' % (HP0, ETA))], 'simpld', 'q e. %s' % HP0)
    od = cd([cd([cd([lift(w, hol_e1(w, A0), Ad), lift(w, e12(w, A0), Ad)], 'jca', '( %s /\\ ( %s ` 2 ) =/= 0 )' % (HOLF(E1, HP0), E1)), qh2], 'jca',
                 '( ( %s /\\ ( %s ` 2 ) =/= 0 ) /\\ q e. %s )' % (HOLF(E1, HP0), E1, HP0)), w.inst('zrord')], 'syl', tsub(ante_of(S['zrord'])[1], {'F': E1, 'P': 'q'}))
    on0 = cd([od], 'simpld', '%s e. NN0' % OL)
    fl = c([dfin, cd([on0], 'nn0red', '%s e. RR' % OL), cd([on0], 'nn0ge0d', '0 <_ %s' % OL), wss], 'fsumless', 'sum_ q e. %s %s <_ sum_ q e. %s %s' % (WIN, OL, DSK, OL))
    LNU = LT2('U')
    uc = c([ur], 'recnd', 'U e. CC')
    aur = c([uc], 'abscld', '( abs ` U ) e. RR')
    nr = c([nn_], 'nnred', 'N e. RR')
    U2 = '( ( abs ` U ) + 2 )'
    u2r = c([aur, numst8(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % U2)
    hnu = c([c([nr, c([], '1red', '1 e. RR')], 'resubcld', '( N - 1 ) e. RR'), c([tr, numst8(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'),
             lin8(w, A0, [c([nn_], 'nnge1d', '1 <_ N')], '0 <_ ( N - 1 )', {'N': nr}), lin8(w, A0, [t0], '0 <_ ( T + 2 )', {'T': tr})], 'mulge0d', '0 <_ ( ( N - 1 ) x. ( T + 2 ) )')
    nule = lin8(w, A0, [hnu, ut], '%s <_ ( N x. ( T + 2 ) )' % U2, {'N': nr, '( abs ` U )': aur, 'T': tr}, products=True)
    u2p = c([u2r, lin8(w, A0, [c([uc], 'absge0d', '0 <_ ( abs ` U )')], '0 < %s' % U2, {'( abs ` U )': aur})], 'elrpd', '%s e. RR+' % U2)
    ll = c([nule, c([u2p, c([dr, lin8(w, A0, [d2], '0 < ( N x. ( T + 2 ) )', {'( N x. ( T + 2 ) )': dr})], 'elrpd', '( N x. ( T + 2 ) ) e. RR+'), w.inst('logleb')], 'syl2anc',
                   '( %s <_ ( N x. ( T + 2 ) ) <-> %s <_ %s )' % (U2, LNU, LD))], 'mpbid', '%s <_ %s' % (LNU, LD))
    lnur = c([u2p], 'relogcld', '%s e. RR' % LNU)
    hh = c([er, c([lr, lnur], 'resubcld', '( %s - %s ) e. RR' % (LD, LNU)), c([ep], 'rpge0d', '0 <_ %s' % ETAW), lin8(w, A0, [ll], '0 <_ ( %s - %s )' % (LD, LNU), {LD: lr, LNU: lnur})],
           'mulge0d', '0 <_ ( %s x. ( %s - %s ) )' % (ETAW, LD, LNU))
    S1 = 'sum_ q e. %s %s' % (WIN, OL); S2 = 'sum_ q e. %s %s' % (DSK, OL)
    wfin = c([dfin, wss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % WIN)
    Aw = '( %s /\\ q e. %s )' % (A0, WIN)
    cw = Ctx(w, Aw)
    wq_d = cw([cw.g(A0), cw([lift(w, wss, Aw), cw([], 'simpr', 'q e. %s' % WIN)], 'sseldd', 'q e. %s' % DSK)], 'jca', Ad)
    s1r = c([wfin, w.s([wq_d, cd([on0], 'nn0red', '%s e. RR' % OL)], 'syl', '( %s -> %s e. RR )' % (Aw, OL))], 'fsumrecl', '%s e. RR' % S1)
    s2r = c([dfin, cd([on0], 'nn0red', '%s e. RR' % OL)], 'fsumrecl', '%s e. RR' % S2)
    lcr = c([se, s1r], 'eqeltrd', '%s e. RR' % LCX('X', 'U'))
    lv = {LCX('X', 'U'): lcr, S1: s1r, S2: s2r, LD: lr, LNU: lnur, IL: ilr, 'S': sr}
    fin = lin8(w, A0, [se, fl, sd, hh, ill], ante_of(S['zrlc0'])[1], lv, products=True)
    w.qed([fin], 'idi', S['zrlc0'])
    return run8(w)


GENS['zrlc0'] = gen_lc0


def gen_lc():
    from zr_i import scale_facts
    w = W('zrlc', 'Lean ` localCount_le ` (blueprint Lemma 7.1, log-free): for every character the zeros in ` [ S , 1 ] x. [ U - 1 / L , U + 1 / L ] ` number at most ` Cloc ( 1 + ( 1 - S ) L ) ` , ` Cloc = 5 ( 3 + K ) ` ( ~ zrlc1 , ~ zrlc0 ).')
    A0 = ante_of(S['zrlc'])[0]
    c = Ctx(w, A0)
    nn_, sr, s1, tr, t0 = c.g('N e. NN'), c.g('S e. RR'), c.g('S <_ 1'), c.g('T e. RR'), c.g('0 <_ T')
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    lam0 = c([c([c([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR'), lr, lin8(w, A0, [s1], '0 <_ ( 1 - S )', {'S': sr}), c([lp], 'ltled', '0 <_ %s' % LD)], 'mulge0d', '0 <_ %s' % LAM)
    P = top_and(A0)
    GOAL = ante_of(S['zrlc'])[1]
    res = []
    for lab, cond in (('zrlc0', 'X = ( 0g ` ( DChr ` N ) )'), ('zrlc1', 'X =/= ( 0g ` ( DChr ` N ) )')):
        Ac = '( %s /\\ %s )' % (A0, cond)
        cc = Ctx(w, Ac)
        A1 = ante_of(S[lab])[0]
        Q = top_and(A1)
        st = cc([cc([cc([cc.g('N e. NN'), cc.g('X e. ( Base ` ( DChr ` N ) )')], 'jca', top_and(Q[0])[0]), cc([], 'simpr', cond)], 'jca', Q[0]), cc.g(Q[1]), cc.g(Q[2])], '3jca', A1)
        bd = cc([st, w.inst(lab)], 'syl', ante_of(S[lab])[1])
        LC = LCX('X', 'U')
        res.append((Ac, bd))
    # both cases by lin
    LC = LCX('X', 'U')
    outs = []
    for Ac, bd in res:
        cc = Ctx(w, Ac)
        outs.append(lin8(w, Ac, [bd, lift(w, lam0, Ac)], GOAL, {LC: lc_real(w, Ac), LD: lift(w, lr, Ac), 'S': lift(w, sr, Ac)}, products=True))
    fin = c([outs[0], outs[1]], 'pm2.61dane', GOAL)
    w.qed([fin], 'idi', S['zrlc'])
    return run8(w)


def lc_real(w, A):
    """( A -> LCX ( X , U ) e. RR ) under an antecedent carrying NX, the box parameters and U"""
    c = Ctx(w, A)
    WIN = '{ v e. %s | ( abs ` ( ( Im ` v ) - U ) ) <_ ( 1 / %s ) }' % (ZFX('X'), LD)
    nxb = c([c.g('N e. NN'), c.g('X e. ( Base ` ( DChr ` N ) )')], 'jca', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )')
    hol = c([nxb, w.inst('zl1ehol')], 'syl', HOLF(EX('X'), HP0))
    e2 = c([c([nxb, c([], '0red', '0 e. RR')], 'jca', '( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ 0 e. RR )'), w.inst('ectr')], 'syl', '( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % EX('X'))
    from zr_e import f2ne0
    f2 = f2ne0(w, A, EX('X'), None, '( 1 / 2 )', bstep=e2)
    sr, tr = c.g('S e. RR'), c.g('T e. RR')
    s0 = lin8(w, A, [c.g('( ; 9 9 / ; ; 1 0 0 ) <_ S')], '0 < S', {'S': sr})
    ZA = ante_of(tsub(stmt('zffin'), {'F': EX('X'), 'A': 'S'}))
    zf = c([c([c([hol, f2], 'jca', top_and(ZA[0])[0]), c([c([sr, s0, c.g('S <_ 1')], '3jca', '( S e. RR /\\ 0 < S /\\ S <_ 1 )'), tr], 'jca', top_and(ZA[0])[1])], 'jca', ZA[0]), w.inst('zffin')], 'syl', ZA[1])
    zfin = c([zf], 'simpld', '%s e. Fin' % ZFX('X'))
    wfin = c([zfin, c.a1(w.s([], 'ssrab2', '%s C_ %s' % (WIN, ZFX('X'))), '%s C_ %s' % (WIN, ZFX('X'))), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % WIN)
    Aq = '( %s /\\ q e. %s )' % (A, ZFX('X'))
    alq = c([zf], 'simprd', 'A. q e. %s %s e. NN' % (ZFX('X'), ORDX('X', 'q')))
    on = w.s([alq], 'r19.21bi', '( %s -> %s e. NN )' % (Aq, ORDX('X', 'q')))
    Aw = '( %s /\\ q e. %s )' % (A, WIN)
    cw = Ctx(w, Aw)
    br = cw([cw.g(A), cw([cw([], 'simpr', 'q e. %s' % WIN), w.inst('elrabi')], 'syl', 'q e. %s' % ZFX('X'))], 'jca', Aq)
    onw = cw([br, on], 'syl', '%s e. NN' % ORDX('X', 'q'))
    return c([wfin, cw([onw], 'nnred', '%s e. RR' % ORDX('X', 'q'))], 'fsumrecl', '%s e. RR' % LCX('X', 'U'))


GENS['zrlc'] = gen_lc
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
