"""Sortie EF3: the box zeros (ef3fib, ef3bz: Lean finite_boxZeroSet), ef3zbz (box filter = rectangle zeros)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
from c10_f import crfacts
import lin
lin.FASTPATH = True

BA, BB = '( ( 1 / 2 ) + ( _i x. -u U ) )', '( ( 3 / 2 ) + ( _i x. U ) )'
BOX = '( %s crect %s )' % (BA, BB)
JQ = '( |_ ` ( 2 x. ( ( Im ` Q ) + U ) ) )'
NB = '( ( |_ ` ( 4 x. U ) ) + 1 )'
TJ = lambda j: '( ( -u U + ( %s / 2 ) ) + ( 1 / 4 ) )' % j
S['ef3fib'] = '( ( U e. RR /\\ Q e. %s ) -> ( %s e. ( 0 ..^ %s ) /\\ Q e. %s ) )' % (BZ(), JQ, NB, ZS('F', TJ(JQ)))


def box_unpack(w, A, U, ur, Q, qbz):
    """from qbz : ( A -> Q e. BZ(F,U) ): dict cc, fz, hy (Re Q in [1/2,3/2], Im Q in [-U,U] and corner eqs), lv"""
    s = St(w, A)
    ba, bb = BA.replace('U', U) if U != 'U' else BA, BB.replace('U', U) if U != 'U' else BB
    el, _ = elrab_(w, 'r', '( %s crect %s )' % (ba, bb), '( F ` r ) = 0', Q)
    both = s([qbz, el], 'sylib', '( %s e. ( %s crect %s ) /\\ ( F ` %s ) = 0 )' % (Q, ba, bb, Q))
    qb, fz = conj_split(w, A, both)
    nu = s([ur], 'renegcld', '-u %s e. RR' % U)
    ac, are, aim = crfacts(w, A, '( 1 / 2 )', '-u %s' % U, numst(w, A, '( 1 / 2 )', 'RR'), nu)
    bc, bre, bim = crfacts(w, A, '( 3 / 2 )', U, numst(w, A, '( 3 / 2 )', 'RR'), ur)
    d = crect_bounds(w, A, ac, bc, qb, ba, bb, Q)
    lv = dict(d['cl']); lv[U] = ur
    return {'cc': d['cc'], 'fz': fz, 'hy': d['le'] + [are, aim, bre, bim], 'lv': lv}


def gen_fib():
    w = W('ef3fib', 'A zero of the box ` [ 1 / 2 , 3 / 2 ] x. [ - U , U ] ` lies in the ` 13 / 8 ` -square about the centre of its half-unit fibre ` floor ( 2 ( Im q + U ) ) ` .')
    A0, G = ante_of(S['ef3fib'])
    s = St(w, A0)
    ur = s([], 'simpl', 'U e. RR'); qbz = s([], 'simpr', 'Q e. %s' % BZ())
    b = box_unpack(w, A0, 'U', ur, 'Q', qbz)
    lv = b['lv']; hy = b['hy']
    imq = lv['( Im ` Q )']
    Y2 = '( 2 x. ( ( Im ` Q ) + U ) )'
    y2r = s([numst(w, A0, '2', 'RR'), s([imq, ur], 'readdcld', '( ( Im ` Q ) + U ) e. RR')], 'remulcld', '%s e. RR' % Y2)
    jz = s([y2r], 'flcld', '%s e. ZZ' % JQ); jr = s([jz], 'zred', '%s e. RR' % JQ)
    lv2 = dict(lv); lv2[JQ] = jr; lv2[Y2] = y2r
    fl1 = s([y2r, w.inst('flle')], 'syl', '%s <_ %s' % (JQ, Y2))
    fl2 = s([y2r, w.inst('flltp1')], 'syl', '%s < ( %s + 1 )' % (Y2, JQ))
    lvl = {'( Im ` Q )': imq, 'U': ur, JQ: jr, '( Re ` Q )': lv['( Re ` Q )']}
    for k, v in lv.items():
        lvl.setdefault(k, v)
    y0 = lin8(w, A0, hy, '0 <_ %s' % Y2, dict(lvl, **{Y2: y2r}) if False else lvl) if False else None
    im_lo = lin8(w, A0, hy, '-u U <_ ( Im ` Q )', lvl)
    im_hi = lin8(w, A0, hy, '( Im ` Q ) <_ U', lvl)
    y0 = lin8(w, A0, [im_lo], '0 <_ %s' % Y2, lvl)
    jn = s([y2r, y0, w.inst('flge0nn0')], 'syl2anc', '%s e. NN0' % JQ)
    F4 = '( 4 x. U )'
    f4r = s([numst(w, A0, '4', 'RR'), ur], 'remulcld', '%s e. RR' % F4)
    u0 = lin8(w, A0, [im_lo, im_hi], '0 <_ %s' % F4, lvl)
    f4n = s([f4r, u0, w.inst('flge0nn0')], 'syl2anc', '( |_ ` %s ) e. NN0' % F4)
    nbn = s([f4n, w.inst('nn0p1nn')], 'syl', '%s e. NN' % NB)
    j4 = lin8(w, A0, [fl1, im_hi], '%s <_ %s' % (JQ, F4), lvl)
    j4f = s([j4, s([f4r, jz, w.inst('flge')], 'syl2anc', '( %s <_ %s <-> %s <_ ( |_ ` %s ) )' % (JQ, F4, JQ, F4))], 'mpbid', '%s <_ ( |_ ` %s )' % (JQ, F4))
    f4fr = s([s([f4n], 'nn0zd', '( |_ ` %s ) e. ZZ' % F4)], 'zred', '( |_ ` %s ) e. RR' % F4)
    jlt = lin8(w, A0, [j4f], '%s < %s' % (JQ, NB), dict(lvl, **{'( |_ ` %s )' % F4: f4fr}))
    jin = s([s([jn, nbn, jlt], '3jca', '( %s e. NN0 /\\ %s e. NN /\\ %s < %s )' % (JQ, NB, JQ, NB)), w.s([], 'elfzo0', '( %s e. ( 0 ..^ %s ) <-> ( %s e. NN0 /\\ %s e. NN /\\ %s < %s ) )' % (JQ, NB, JQ, NB, JQ, NB))],
            'sylibr', '%s e. ( 0 ..^ %s )' % (JQ, NB))
    T0_ = TJ(JQ)
    t0r = s([s([s([ur], 'renegcld', '-u U e. RR'), s([jr, numst(w, A0, '2', 'RR+')], 'rerpdivcld', '( %s / 2 ) e. RR' % JQ)], 'readdcld', '( -u U + ( %s / 2 ) ) e. RR' % JQ), numst(w, A0, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % T0_)
    qz = zs_mem(w, A0, 'F', T0_, t0r, 'Q', b['cc'], hy + [fl1, fl2], lvl, b['fz'])
    w.qed([jin, qz], 'jca', S['ef3fib'])
    return run8(w)


def gen_bz():
    w = W('ef3bz', 'Lean ` finite_boxZeroSet ` : the zeros of a ` DiskData ` function in the box ` [ 1 / 2 , 3 / 2 ] x. [ - U , U ] ` form a finite set, and their orders are positive integers.')
    A0, G = ante_of(S['ef3bz'])
    s = St(w, A0)
    dd = s([], 'simpl', DD()); ur = s([], 'simpr', 'U e. RR')
    IX = '( 0 ..^ %s )' % NB
    ZJ = ZS('F', TJ('j'))
    A1 = '( %s /\\ j e. %s )' % (A0, IX)
    s1 = St(w, A1)
    jr = s1([s1([s1([], 'simpr', 'j e. %s' % IX), w.inst('elfzonn0')], 'syl', 'j e. NN0')], 'nn0red', 'j e. RR')
    u1 = lift(w, ur, A1)
    t0r = s1([s1([s1([u1], 'renegcld', '-u U e. RR'), s1([jr, numst(w, A1, '2', 'RR+')], 'rerpdivcld', '( j / 2 ) e. RR')], 'readdcld', '( -u U + ( j / 2 ) ) e. RR'), numst(w, A1, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % TJ('j'))
    zsj = tsub(ante_of(stmt('ef2zs'))[1], {'T': TJ('j')})
    z1 = s1([s1([lift(w, dd, A1), t0r], 'jca', '( %s /\\ %s e. RR )' % (DD(), TJ('j'))), w.inst('ef2zs')], 'syl', zsj)
    zf = s1([z1, w.inst('simp1')], 'syl', '%s e. Fin' % ZJ)
    al = s([zf], 'ralrimiva', 'A. j e. %s %s e. Fin' % (IX, ZJ))
    IU = 'U_ j e. %s %s' % (IX, ZJ)
    iuf = s([s([], 'fzofi', '%s e. Fin' % IX) if False else s([w.s([], 'fzofi', '%s e. Fin' % IX)], 'a1i', '%s e. Fin' % IX), al, w.inst('iunfi')], 'syl2anc', '%s e. Fin' % IU)
    # cover
    A2 = '( %s /\\ y e. %s )' % (A0, BZ())
    s2 = St(w, A2)
    JY = JQ.replace('Q', 'y')
    fb = s2([s2([lift(w, ur, A2), s2([], 'simpr', 'y e. %s' % BZ())], 'jca', '( U e. RR /\\ y e. %s )' % BZ()), w.inst('ef3fib')], 'syl', tsub(ante_of(S['ef3fib'])[1], {'Q': 'y'}))
    jyin, yzs = conj_split(w, A2, fb)
    eqj, _ = w.wcongr('y e. %s' % ZJ, {'j': JY}, 'j = %s' % JY, {'j': w.s([], 'id', '( j = %s -> j = %s )' % (JY, JY))})
    ex = s2([eqj, jyin, yzs], 'rspcedv' if False else 'rspcedvd', 'E. j e. %s y e. %s' % (IX, ZJ)) if False else \
        s2([s2([jyin, yzs], 'jca', '( %s e. %s /\\ y e. %s )' % (JY, IX, tsub(ZJ, {'j': JY}))), w.s([eqj], 'rspcev', '( ( %s e. %s /\\ y e. %s ) -> E. j e. %s y e. %s )' % (JY, IX, tsub(ZJ, {'j': JY}), IX, ZJ))], 'syl', 'E. j e. %s y e. %s' % (IX, ZJ))
    yiu = s2([ex, w.s([], 'eliun', '( y e. %s <-> E. j e. %s y e. %s )' % (IU, IX, ZJ))], 'sylibr', 'y e. %s' % IU)
    ss = s([w.s([yiu], 'ex', '( %s -> ( y e. %s -> y e. %s ) )' % (A0, BZ(), IU))], 'ssrdv', '%s C_ %s' % (BZ(), IU))
    bf = s([iuf, ss], 'ssfid', '%s e. Fin' % BZ())
    # orders
    A3 = '( %s /\\ y e. %s )' % (A0, BZ())
    s3 = St(w, A3)
    JQq = JQ.replace('Q', 'y')
    fq = s3([s3([lift(w, ur, A3), s3([], 'simpr', 'y e. %s' % BZ())], 'jca', '( U e. RR /\\ y e. %s )' % BZ()), w.inst('ef3fib')], 'syl', tsub(ante_of(S['ef3fib'])[1], {'Q': 'y'}))
    jqin, qzs = conj_split(w, A3, fq)
    TQ = TJ(JQq)
    jqr = s3([s3([jqin, w.inst('elfzonn0')], 'syl', '%s e. NN0' % JQq)], 'nn0red', '%s e. RR' % JQq)
    u3 = lift(w, ur, A3)
    tqr = s3([s3([s3([u3], 'renegcld', '-u U e. RR'), s3([jqr, numst(w, A3, '2', 'RR+')], 'rerpdivcld', '( %s / 2 ) e. RR' % JQq)], 'readdcld', '( -u U + ( %s / 2 ) ) e. RR' % JQq), numst(w, A3, '( 1 / 4 )', 'RR')], 'readdcld', '%s e. RR' % TQ)
    zsq = tsub(ante_of(stmt('ef2zs'))[1], {'T': TQ})
    z3 = s3([s3([lift(w, dd, A3), tqr], 'jca', '( %s /\\ %s e. RR )' % (DD(), TQ)), w.inst('ef2zs')], 'syl', zsq)
    ZQ = ZS('F', TQ)
    alo = s3([z3, w.inst('simp2')], 'syl', 'A. q e. %s ( F holord q ) e. NN' % ZQ)
    hq = w.s([w.s([], 'oveq2', '( q = y -> ( F holord q ) = ( F holord y ) )')], 'eleq1d', '( q = y -> ( ( F holord q ) e. NN <-> ( F holord y ) e. NN ) )')
    oq = s3([hq, alo, qzs], 'rspcdva', '( F holord y ) e. NN')
    ay = s([oq], 'ralrimiva', 'A. y e. %s ( F holord y ) e. NN' % BZ())
    cb = w.s([w.s([w.s([], 'oveq2', '( y = q -> ( F holord y ) = ( F holord q ) )')], 'eleq1d', '( y = q -> ( ( F holord y ) e. NN <-> ( F holord q ) e. NN ) )')], 'cbvralvw',
             '( A. y e. %s ( F holord y ) e. NN <-> A. q e. %s ( F holord q ) e. NN )' % (BZ(), BZ()))
    ao = s([ay, cb], 'sylib', 'A. q e. %s ( F holord q ) e. NN' % BZ())
    w.qed([bf, ao], 'jca', S['ef3bz'])
    return run8(w)


def gen_zbz():
    w = W('ef3zbz', 'The zeros of the box strictly inside the rectangle ` [ S , C ] x. [ L , H ] ` inside the box are the zeros of the rectangle strictly inside it (Lean ` chain_sum_eq_box ` reads the filtered box set).')
    A0, G = ante_of(S['ef3zbz'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); h3 = s([], 'simp3', H3)
    ur, lh = conj_split(w, A0, h1); lr, hr = conj_split(w, A0, lh)
    sc, so = conj_split(w, A0, h2); sr, cr = conj_split(w, A0, sc); s12, c32 = conj_split(w, A0, so)
    ul, hu = conj_split(w, A0, h3)
    SINy = SIN('y')
    RA, RB = '( S + ( _i x. L ) )', '( C + ( _i x. H ) )'
    RECT = '( %s crect %s )' % (RA, RB)
    L1, _ = elrab_(w, 'p', BZ(), SIN('p'), 'y')
    L2, _ = elrab_(w, 'r', BOX, '( F ` r ) = 0', 'y')
    L3 = w.s([L2], 'anbi1i', '( ( y e. %s /\\ %s ) <-> ( ( y e. %s /\\ ( F ` y ) = 0 ) /\\ %s ) )' % (BZ(), SINy, BOX, SINy))
    LL = w.s([L1, L3], 'bitri', '( y e. { p e. %s | %s } <-> ( ( y e. %s /\\ ( F ` y ) = 0 ) /\\ %s ) )' % (BZ(), SIN('p'), BOX, SINy))
    R1, _ = elrab_(w, 'p', RECT, '( ( F ` p ) = 0 /\\ %s )' % SIN('p'), 'y')
    PL = '( ( y e. %s /\\ ( F ` y ) = 0 ) /\\ %s )' % (BOX, SINy)
    PR = '( y e. %s /\\ ( ( F ` y ) = 0 /\\ %s ) )' % (RECT, SINy)

    def corners(A):
        L = lambda st: lift(w, st, A)
        nu = w.s([L(ur)], 'renegcld', '( %s -> -u U e. RR )' % A)
        ba = crfacts(w, A, '( 1 / 2 )', '-u U', numst(w, A, '( 1 / 2 )', 'RR'), nu)
        bb = crfacts(w, A, '( 3 / 2 )', 'U', numst(w, A, '( 3 / 2 )', 'RR'), L(ur))
        ra = crfacts(w, A, 'S', 'L', L(sr), L(lr))
        rb = crfacts(w, A, 'C', 'H', L(cr), L(hr))
        return ba, bb, ra, rb
    # ->
    A1 = '( %s /\\ %s )' % (A0, PL)
    s1 = St(w, A1)
    L = lambda st: lift(w, st, A1)
    ba, bb, ra, rb = corners(A1)
    pl = s1([], 'simpr', PL)
    bf, sin_ = conj_split(w, A1, pl)
    yb, fz = conj_split(w, A1, bf)
    r_, i_ = conj_split(w, A1, sin_)
    rl, rh = conj_split(w, A1, r_); il, ih = conj_split(w, A1, i_)
    d = crect_bounds(w, A1, ba[0], bb[0], yb, BA, BB, 'y')
    lv = dict(d['cl']); lv.update({'S': L(sr), 'C': L(cr), 'L': L(lr), 'H': L(hr), 'U': L(ur)})
    hy = [rl, rh, il, ih, ra[1], ra[2], rb[1], rb[2]]
    yr = crect_in(w, A1, RA, RB, ra[0], rb[0], 'y', d['cc'], hy, lv)
    right = s1([yr, s1([fz, sin_], 'jca', '( ( F ` y ) = 0 /\\ %s )' % SINy)], 'jca', PR)
    # <-
    A2 = '( %s /\\ %s )' % (A0, PR)
    s2 = St(w, A2)
    L = lambda st: lift(w, st, A2)
    ba, bb, ra, rb = corners(A2)
    pr_ = s2([], 'simpr', PR)
    yrr, fs = conj_split(w, A2, pr_)
    fz2, sin2 = conj_split(w, A2, fs)
    r_, i_ = conj_split(w, A2, sin2)
    rl, rh = conj_split(w, A2, r_); il, ih = conj_split(w, A2, i_)
    d = crect_bounds(w, A2, ra[0], rb[0], yrr, RA, RB, 'y')
    lv = dict(d['cl']); lv.update({'S': L(sr), 'C': L(cr), 'L': L(lr), 'H': L(hr), 'U': L(ur)})
    hy = [rl, rh, il, ih, L(s12), L(c32), L(ul), L(hu), ba[1], ba[2], bb[1], bb[2]]
    yb2 = crect_in(w, A2, BA, BB, ba[0], bb[0], 'y', d['cc'], hy, lv)
    left = s2([s2([yb2, fz2], 'jca', '( y e. %s /\\ ( F ` y ) = 0 )' % BOX), sin2], 'jca', PL)
    core = s([right, left], 'impbida', '( %s <-> %s )' % (PL, PR))
    ee = s([core, LL, R1], '3bitr4g', '( y e. { p e. %s | %s } <-> y e. %s )' % (BZ(), SIN('p'), ZR()))
    w.qed([ee], 'eqrdv', S['ef3zbz'])
    return run8(w)


S['ef3zrf'] = ('( ( %s /\\ ( ( S e. RR /\\ C e. RR ) /\\ ( ( 1 / 2 ) <_ S /\\ C <_ ( 3 / 2 ) ) ) /\\ ( L e. RR /\\ H e. RR ) ) -> '
               '( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN ) )') % (DD(), ZR(), ZR())


def gen_zrf():
    w = W('ef3zrf', 'The zeros of a ` DiskData ` function strictly inside a rectangle ` [ S , C ] x. [ L , H ] ` with ` 1 / 2 <_ S ` , ` C <_ 3 / 2 ` form a finite set with orders in ` NN ` (they lie in a box).')
    A0, G = ante_of(S['ef3zrf'])
    s = St(w, A0)
    dd, sc, lh = top_and(A0)
    dd = s([], 'simp1', dd); scs = s([], 'simp2', sc); lhs = s([], 'simp3', lh)
    lr, hr = conj_split(w, A0, lhs)
    U2 = '( ( abs ` L ) + ( abs ` H ) )'
    al = s([s([lr], 'recnd', 'L e. CC')], 'abscld', '( abs ` L ) e. RR'); ah = s([s([hr], 'recnd', 'H e. CC')], 'abscld', '( abs ` H ) e. RR')
    ur = s([al, ah], 'readdcld', '%s e. RR' % U2)
    lv = {'L': lr, 'H': hr, '( abs ` L )': al, '( abs ` H )': ah}
    f1 = s([lr, w.inst('leabs')], 'syl', 'L <_ ( abs ` L )'); f2 = s([hr, w.inst('leabs')], 'syl', 'H <_ ( abs ` H )')
    f3 = s([s([lr], 'recnd', 'L e. CC')], 'absge0d', '0 <_ ( abs ` L )'); f4 = s([s([hr], 'recnd', 'H e. CC')], 'absge0d', '0 <_ ( abs ` H )')
    nl = s([s([s([lr], 'renegcld', '-u L e. RR'), w.inst('leabs')], 'syl', '-u L <_ ( abs ` -u L )'), s([s([lr], 'recnd', 'L e. CC')], 'absnegd', '( abs ` -u L ) = ( abs ` L )')], 'breqtrd', '-u L <_ ( abs ` L )')
    hy = [f1, f2, f3, f4, nl]
    a1 = lin8(w, A0, hy, '-u %s <_ L' % U2, lv); a2 = lin8(w, A0, hy, 'H <_ %s' % U2, lv)
    za = s([s([ur, lhs], 'jca', '( %s e. RR /\\ ( L e. RR /\\ H e. RR ) )' % U2), scs, s([a1, a2], 'jca', '( -u %s <_ L /\\ H <_ %s )' % (U2, U2))], '3jca',
           tsub(ante_of(S['ef3zbz'])[0], {'U': U2}))
    zb = s([za, w.inst('ef3zbz')], 'syl', tsub(ante_of(S['ef3zbz'])[1], {'U': U2}))
    B2 = BZ('F', U2)
    bz = s([s([dd, ur], 'jca', '( %s /\\ %s e. RR )' % (DD(), U2)), w.inst('ef3bz')], 'syl', '( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN )' % (B2, B2))
    bf, bo = conj_split(w, A0, bz)
    FL = '{ p e. %s | %s }' % (B2, SIN('p'))
    ss = s([zb, s([w.s([], 'ssrab2', '%s C_ %s' % (FL, B2))], 'a1i', '%s C_ %s' % (FL, B2))], 'eqsstrrd', '%s C_ %s' % (ZR(), B2))
    zf = s([bf, ss], 'ssfid', '%s e. Fin' % ZR())
    zo = s([bo, s([ss, w.inst('ssralv')], 'syl', '( A. q e. %s ( F holord q ) e. NN -> A. q e. %s ( F holord q ) e. NN )' % (B2, ZR()))], 'mpd', 'A. q e. %s ( F holord q ) e. NN' % ZR())
    w.qed([zf, zo], 'jca', S['ef3zrf'])
    return run8(w)


if __name__ == '__main__':
    gen_fib()
    gen_bz()
    gen_zbz()
    gen_zrf()
