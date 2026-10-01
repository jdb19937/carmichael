"""Sortie ZR: zrzf (Lean zeta_zero_re_lt, the zeta zero-free region with an existential constant)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of


def logge1(w, A, xr, xge, X):
    """( A -> 1 <_ ( log ` X ) ) from xr : X e. RR and xge : 3 <_ X (via e < 3)"""
    c = Ctx(w, A)
    ep = c.a1(w.s([], 'epr', '_e e. RR+'), '_e e. RR+')
    er = c([ep], 'rpred', '_e e. RR')
    e3 = c.a1(w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3'), '_e < 3')
    xp = c([xr, lin8(w, A, [xge], '0 < %s' % X, {X: xr})], 'elrpd', '%s e. RR+' % X)
    le = lin8(w, A, [e3, xge], '_e <_ %s' % X, {X: xr, '_e': er})
    la = c([le, c([ep, xp, w.inst('logleb')], 'syl2anc', '( _e <_ %s <-> ( log ` _e ) <_ ( log ` %s ) )' % (X, X))], 'mpbid', '( log ` _e ) <_ ( log ` %s )' % X)
    lr = c([xp], 'relogcld', '( log ` %s ) e. RR' % X)
    return lin8(w, A, [la, c.a1(w.s([], 'loge', '( log ` _e ) = 1'), '( log ` _e ) = 1')], '1 <_ ( log ` %s )' % X,
                {'( log ` %s )' % X: lr, '( log ` _e )': c([ep], 'relogcld', '( log ` _e ) e. RR')}), lr, xp


def gen_zf():
    w = W('zrzf', 'Lean ` zeta_zero_re_lt ` (I5): there is ` 0 < c <_ 1 / 2 ` with ` Re r < 1 - c / log ( abs Im r + 3 ) ` for every zero ` r ` of zeta; '
             '` c = zfE ( 1 - u ) ` with ` u ` from the box clearance ( ~ zrbox at height ` 2 ` , ~ zrhi above it).')
    A0 = '2 e. RR+'
    c = Ctx(w, A0)
    zb = c([c([], 'id', A0), w.inst('zrbox')], 'syl', ante_of(tsub(S['zrbox'], {'V': '2'}))[1])
    BOXB = ante_of(tsub(S['zrbox'], {'V': '2'}))[1]
    PSI = BOXB[len('E. u e. RR '):]
    G = S['zrzf']
    Au0 = '( %s /\\ u e. RR )' % A0
    Au = '( %s /\\ %s )' % (Au0, PSI)
    cu = Ctx(w, Au)
    ur = cu.g('u e. RR'); uh = cu.g('( 1 / 2 ) <_ u'); u1 = cu.g('u < 1')
    ALS = top_and(PSI)[1]
    als = cu.g(ALS)
    D31 = '( ; 3 1 x. %s )' % ZFK
    d31r = cu([numst8(w, Au, '; 3 1', 'RR'), numst8(w, Au, ZFK, 'RR')], 'remulcld', '%s e. RR' % D31)
    d31p = lin8(w, Au, [], '1 < %s' % D31, {})
    zer = cu([cu([], '1red', '1 e. RR'), d31r, cu([lin8(w, Au, [], '0 < %s' % D31, {})], 'gt0ne0d', '%s =/= 0' % D31)], 'redivcld', '%s e. RR' % ZFE)
    ze1 = cu([d31p, cu([d31r, lin8(w, Au, [], '0 < %s' % D31, {}), w.inst('recgt1')], 'syl2anc', '( 1 < %s <-> %s < 1 )' % (D31, ZFE))], 'mpbid', '%s < 1' % ZFE)
    ze0 = cu([cu([cu([d31r, lin8(w, Au, [], '0 < %s' % D31, {})], 'elrpd', '%s e. RR+' % D31)], 'rpreccld', '%s e. RR+' % ZFE)], 'rpgt0d', '0 < %s' % ZFE)
    OU = '( 1 - u )'
    our = cu([cu([], '1red', '1 e. RR'), ur], 'resubcld', '%s e. RR' % OU)
    C = '( %s x. %s )' % (ZFE, OU)
    cr = cu([zer, our], 'remulcld', '%s e. RR' % C)
    lvu = {ZFE: zer, 'u': ur}
    cp = cu([zer, our, ze0, lin8(w, Au, [u1], '0 < %s' % OU, lvu)], 'mulgt0d', '0 < %s' % C)
    hq = cu([zer, our, cu([ze0], 'ltled', '0 <_ %s' % ZFE), lin8(w, Au, [u1], '0 <_ %s' % OU, lvu)], 'mulge0d', '0 <_ ( %s x. %s )' % (ZFE, OU))
    h2 = cu([our, cu([cu([], '1red', '1 e. RR'), zer], 'resubcld', '( 1 - %s ) e. RR' % ZFE), lin8(w, Au, [u1], '0 <_ %s' % OU, lvu), lin8(w, Au, [ze1], '0 <_ ( 1 - %s )' % ZFE, lvu)],
            'mulge0d', '0 <_ ( %s x. ( 1 - %s ) )' % (OU, ZFE))
    lvC = {ZFE: zer, 'u': ur}
    c_ou = lin8(w, Au, [h2], '%s <_ %s' % (C, OU), lvC, products=True)
    c_h = lin8(w, Au, [c_ou, uh], '%s <_ ( 1 / 2 )' % C, lvC, products=True)
    h4 = cu([zer, cu([numst8(w, Au, '( 1 / 2 )', 'RR'), our], 'resubcld', '( ( 1 / 2 ) - %s ) e. RR' % OU), cu([ze0], 'ltled', '0 <_ %s' % ZFE), lin8(w, Au, [uh], '0 <_ ( ( 1 / 2 ) - %s )' % OU, lvu)],
            'mulge0d', '0 <_ ( %s x. ( ( 1 / 2 ) - %s ) )' % (ZFE, OU))
    c_z = lin8(w, Au, [h4, ze0], '%s < %s' % (C, ZFE), lvC, products=True)
    # a zero r
    Ar = '( ( %s /\\ r e. CC ) /\\ ( %s ` r ) = 0 )' % (Au, E1)
    cr_ = Ctx(w, Ar)
    L_ = lambda st: lift(w, st, Ar)
    rc = cr_.g('r e. CC'); rz = cr_.g('( %s ` r ) = 0' % E1)
    RR_, IR_ = '( Re ` r )', '( Im ` r )'
    rrr = cr_([rc], 'recld', '%s e. RR' % RR_); irr = cr_([rc], 'imcld', '%s e. RR' % IR_)
    AI = '( abs ` %s )' % IR_
    air = cr_([cr_([irr], 'recnd', '%s e. CC' % IR_)], 'abscld', '%s e. RR' % AI)
    ai0 = cr_([cr_([irr], 'recnd', '%s e. CC' % IR_)], 'absge0d', '0 <_ %s' % AI)
    X3 = '( %s + 3 )' % AI
    x3r = cr_([air, numst8(w, Ar, '3', 'RR')], 'readdcld', '%s e. RR' % X3)
    l3, l3r, x3p = logge1(w, Ar, x3r, lin8(w, Ar, [ai0], '3 <_ %s' % X3, {AI: air}), X3)
    L3 = '( log ` %s )' % X3
    l3p = cr_([l3r, lin8(w, Ar, [l3], '0 < %s' % L3, {L3: l3r})], 'elrpd', '%s e. RR+' % L3)
    Q3 = '( %s / %s )' % (C, L3)
    q3r = cr_([L_(cr), l3r, cr_([l3p], 'rpne0d', '%s =/= 0' % L3)], 'redivcld', '%s e. RR' % Q3)
    q3c = cr_([numst8(w, Ar, '1', 'RR+'), l3p, L_(cr), cr_([L_(cp)], 'ltled', '0 <_ %s' % C), l3], 'lediv2ad', '%s <_ ( %s / 1 )' % (Q3, C))
    q3c2 = cr_([q3c, cr_([cr_([L_(cr)], 'recnd', '%s e. CC' % C)], 'div1d', '( %s / 1 ) = %s' % (C, C))], 'breqtrd', '%s <_ %s' % (Q3, C))
    GR = '%s < ( 1 - %s )' % (RR_, Q3)
    # Re r <_ 1
    A1 = '( %s /\\ 1 < %s )' % (Ar, RR_)
    n1 = w.s([lift(w, rc, A1), w.s([], 'simpr', '( %s -> 1 < %s )' % (A1, RR_)), w.inst('zre1n')], 'syl2anc', '( %s -> ( %s ` r ) =/= 0 )' % (A1, E1))
    nb = cr_([lift(w, rz, A1), w.s([n1], 'neneqd', '( %s -> -. ( %s ` r ) = 0 )' % (A1, E1))], 'pm2.65da', '-. 1 < %s' % RR_)
    rl1 = cr_([nb, cr_([rrr, cr_([], '1red', '1 e. RR')], 'lenltd', '( %s <_ 1 <-> -. 1 < %s )' % (RR_, RR_))], 'mpbird', '%s <_ 1' % RR_)
    lvr = {RR_: rrr, Q3: q3r, C: L_(cr), 'u': L_(ur), ZFE: L_(zer), AI: air}
    # case A: abs Im r <_ 2
    Aa = '( %s /\\ %s <_ 2 )' % (Ar, AI)
    ca = Ctx(w, Aa)
    La = lambda st: lift(w, st, Aa)
    Ab_ = '( %s /\\ u <_ %s )' % (Aa, RR_)
    bs = ante_of(tsub(ALS[len('A. s e. CC '):], {}))
    body_s = ALS[len('A. s e. CC '):]
    ins, news = ral_at(w, Ab_, lift(w, als, Ab_), 's', 'r', body_s, lift(w, rc, Ab_))
    hh = w.s([w.s([w.s([], 'simpr', '( %s -> u <_ %s )' % (Ab_, RR_)), lift(w, rl1, Ab_)], 'jca', '( %s -> ( u <_ %s /\\ %s <_ 1 ) )' % (Ab_, RR_, RR_)), lift(w, ca.g('%s <_ 2' % AI), Ab_)], 'jca', '( %s -> %s )' % (Ab_, ante_of(news)[0]))
    nz = w.s([hh, ins], 'mpd', '( %s -> ( %s ` r ) =/= 0 )' % (Ab_, E1))
    nu = ca([lift(w, rz, Ab_), w.s([nz], 'neneqd', '( %s -> -. ( %s ` r ) = 0 )' % (Ab_, E1))], 'pm2.65da', '-. u <_ %s' % RR_)
    rlu = ca([nu, ca([La(rrr), La(ur)], 'ltnled', '( %s < u <-> -. u <_ %s )' % (RR_, RR_))], 'mpbird', '%s < u' % RR_)
    fa = lin8(w, Aa, [rlu, La(q3c2), La(c_ou)], GR, {k_: La(v_) for k_, v_ in lvr.items()})
    # case B: 2 < abs Im r
    Ab = '( %s /\\ -. %s <_ 2 )' % (Ar, AI)
    cb = Ctx(w, Ab)
    Lb = lambda st: lift(w, st, Ab)
    a2 = cb([cb([], 'simpr', '-. %s <_ 2' % AI), cb([numst8(w, Ab, '2', 'RR'), Lb(air)], 'ltnled', '( 2 < %s <-> -. %s <_ 2 )' % (AI, AI))], 'mpbird', '2 < %s' % AI)
    Ab1 = '( %s /\\ %s < ( 3 / 8 ) )' % (Ab, RR_)
    lvb1 = {k_: lift(w, v_, Ab1) for k_, v_ in lvr.items()}
    fb1 = lin8(w, Ab1, [w.s([], 'simpr', '( %s -> %s < ( 3 / 8 ) )' % (Ab1, RR_)), lift(w, q3c2, Ab1), lift(w, c_h, Ab1)], GR, lvb1)
    Ab2 = '( %s /\\ -. %s < ( 3 / 8 ) )' % (Ab, RR_)
    c2 = Ctx(w, Ab2)
    L2_ = lambda st: lift(w, st, Ab2)
    b38 = c2([c2([], 'simpr', '-. %s < ( 3 / 8 )' % RR_), c2([numst8(w, Ab2, '( 3 / 8 )', 'RR'), L2_(rrr)], 'lenltd', '( ( 3 / 8 ) <_ %s <-> -. %s < ( 3 / 8 ) )' % (RR_, RR_))], 'mpbird', '( 3 / 8 ) <_ %s' % RR_)
    HI = ante_of(tsub(S['zrhi'], {'R': 'r'}))
    zh = c2([c2([c2([L2_(rc), L2_(rz)], 'jca', top_and(HI[0])[0]), c2([c2([L2_(a2)], 'ltled', '2 <_ %s' % AI), b38], 'jca', top_and(HI[0])[1])], 'jca', HI[0]), w.inst('zrhi')], 'syl', HI[1])
    X2 = '( %s + 2 )' % AI
    x2r = c2([L2_(air), numst8(w, Ab2, '2', 'RR')], 'readdcld', '%s e. RR' % X2)
    l2, l2r, x2p = logge1(w, Ab2, x2r, lin8(w, Ab2, [L2_(a2)], '3 <_ %s' % X2, {AI: L2_(air)}), X2)
    L2 = '( log ` %s )' % X2
    l2p = c2([l2r, lin8(w, Ab2, [l2], '0 < %s' % L2, {L2: l2r})], 'elrpd', '%s e. RR+' % L2)
    lle = c2([lin8(w, Ab2, [], '%s <_ %s' % (X2, X3), {AI: L2_(air)}), c2([x2p, L2_(x3p), w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> %s <_ %s )' % (X2, X3, L2, L3))], 'mpbid', '%s <_ %s' % (L2, L3))
    q32 = c2([l2p, L2_(l3p), L2_(cr), c2([L2_(cp)], 'ltled', '0 <_ %s' % C), lle], 'lediv2ad', '%s <_ ( %s / %s )' % (Q3, C, L2))
    cz = c2([L2_(c_z), c2([L2_(cr), L2_(zer), l2p], 'ltdiv1d', '( %s < %s <-> ( %s / %s ) < ( %s / %s ) )' % (C, ZFE, C, L2, ZFE, L2))], 'mpbid', '( %s / %s ) < ( %s / %s )' % (C, L2, ZFE, L2))
    lvb2 = {k_: L2_(v_) for k_, v_ in lvr.items()}
    lvb2['( %s / %s )' % (C, L2)] = c2([L2_(cr), l2r, c2([l2p], 'rpne0d', '%s =/= 0' % L2)], 'redivcld', '( %s / %s ) e. RR' % (C, L2))
    lvb2['( %s / %s )' % (ZFE, L2)] = c2([L2_(zer), l2r, c2([l2p], 'rpne0d', '%s =/= 0' % L2)], 'redivcld', '( %s / %s ) e. RR' % (ZFE, L2))
    fb2 = lin8(w, Ab2, [zh, q32, cz], GR, lvb2)
    fb = cb([fb1, fb2], 'pm2.61dan', GR)
    fr = cr_([fa, fb], 'pm2.61dan', GR)
    Arc = '( %s /\\ r e. CC )' % Au
    alr = cu([w.s([fr], 'ex', '( %s -> ( ( %s ` r ) = 0 -> %s ) )' % (Arc, E1, GR))], 'ralrimiva', 'A. r e. CC ( ( %s ` r ) = 0 -> %s )' % (E1, GR))
    body = G[len('E. c e. RR '):]
    eqx, newx = w.wcongr(body, {'c': C}, 'c = %s' % C, {'c': w.s([], 'id', '( c = %s -> c = %s )' % (C, C))})
    Ac = '( %s /\\ c = %s )' % (Au, C)
    at = cu([cu([cp, c_h], 'jca', top_and(newx)[0]), alr], 'jca', newx)
    gc = cu([cr, w.s([eqx], 'adantl', '( %s -> ( %s <-> %s ) )' % (Ac, body, newx)), at], 'rspcedvd', G)
    rl = c([w.s([gc], 'ex', '( %s -> ( %s -> %s ) )' % (Au0, PSI, G))], 'rexlimdva', '( %s -> %s )' % (BOXB, G))
    g = c([zb, rl], 'mpd', G)
    w.qed([w.s([], '2rp', '2 e. RR+'), g], 'ax-mp', G)
    return run8(w)


GENS = {'zrzf': gen_zf}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
