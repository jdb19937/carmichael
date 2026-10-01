"""Sortie EF3: one strip in rectangle-zero form (ef3cs: Lean mem_closedBall_of_strip; ef3c1: rectInt_strip with the
frame facts of rectInt_chain), the step (ef3cstep) and the chain (ef3chain: rectInt_chain + chain_sum_eq_box)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
from c10_f import crfacts
import lin
import ef3_a, ef3_c
lin.FASTPATH = True

RA, RB = '( S + ( _i x. L ) )', '( C + ( _i x. H ) )'
RECT = '( %s crect %s )' % (RA, RB)
TM = '( ( L + H ) / 2 )'
ZSM = ZS('F', TM)
S['ef3cs'] = ('( ( ( ( S e. RR /\\ C e. RR ) /\\ ( ( 9 / ; 1 6 ) <_ S /\\ C <_ ( 5 / 4 ) ) ) /\\ ( ( L e. RR /\\ H e. RR ) /\\ ( L < H /\\ ( H - L ) <_ 1 ) ) ) -> '
              '{ p e. %s | %s } = %s )') % (ZSM, SIN('p'), ZR())
SCH1 = '( ( S e. RR /\\ C e. RR ) /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S < C ) /\\ ( 1 < C /\\ C <_ ( 5 / 4 ) ) )'
LN = lambda h: 'A. x e. ( S [,] C ) ( F ` ( x + ( _i x. %s ) ) ) =/= 0' % h
LE = lambda a, b: 'A. t e. ( %s [,] %s ) ( F ` ( S + ( _i x. t ) ) ) =/= 0' % (a, b)
S['ef3c1'] = ('( ( ( %s /\\ ( Y e. RR /\\ 1 < Y ) /\\ %s ) /\\ ( ( L e. RR /\\ H e. RR ) /\\ ( L < H /\\ ( H - L ) <_ 1 ) ) /\\ '
              '( ( %s /\\ %s ) /\\ %s ) ) -> ( %s rectint <. %s , %s >. ) = ( %s x. sum_ q e. %s %s ) )') % (
    DD(), SCH1, LN('L'), LN('H'), LE('L', 'H'), LDI(), RA, RB, TPI, ZR(), RSUM())


def gen_cs():
    w = W('ef3cs', 'Lean ` mem_closedBall_of_strip ` : a zero strictly inside a strip ` [ S , C ] x. [ L , H ] ` ( ` 9 / 16 <_ S ` , ` C <_ 5 / 4 ` , ` H - L <_ 1 ` ) lies in the ` 13 / 8 ` -square about ` 2 + i ( L + H ) / 2 ` , so the filtered square zeros are the rectangle zeros strictly inside.')
    A0, G = ante_of(S['ef3cs'])
    s = St(w, A0)
    H1, H2 = top_and(A0)
    h1 = s([], 'simpl', H1); h2 = s([], 'simpr', H2)
    sc, so = conj_split(w, A0, h1); sr, cr = conj_split(w, A0, sc); s9, c54 = conj_split(w, A0, so)
    lh, lo = conj_split(w, A0, h2); lr, hr = conj_split(w, A0, lh); llh, hl1 = conj_split(w, A0, lo)
    SINy = SIN('y')
    L1, _ = elrab_(w, 'p', ZSM, SIN('p'), 'y')
    R1, _ = elrab_(w, 'p', RECT, '( ( F ` p ) = 0 /\\ %s )' % SIN('p'), 'y')
    PL = '( y e. %s /\\ %s )' % (ZSM, SINy)
    PR = '( y e. %s /\\ ( ( F ` y ) = 0 /\\ %s ) )' % (RECT, SINy)

    def base(A):
        L = lambda st: lift(w, st, A)
        ra = crfacts(w, A, 'S', 'L', L(sr), L(lr)); rb = crfacts(w, A, 'C', 'H', L(cr), L(hr))
        tm = w.s([w.s([L(lr), L(hr)], 'readdcld', '( %s -> ( L + H ) e. RR )' % A), numst(w, A, '2', 'RR+')], 'rerpdivcld', '( %s -> %s e. RR )' % (A, TM))
        lv = {'S': L(sr), 'C': L(cr), 'L': L(lr), 'H': L(hr)}
        return L, ra, rb, tm, lv
    A1 = '( %s /\\ %s )' % (A0, PL)
    s1 = St(w, A1)
    L, ra, rb, tm, lv = base(A1)
    pl = s1([], 'simpr', PL)
    yz, sin_ = conj_split(w, A1, pl)
    r_, i_ = conj_split(w, A1, sin_)
    rl, rh = conj_split(w, A1, r_); il, ih = conj_split(w, A1, i_)
    z = zs_unpack(w, A1, 'F', TM, tm, 'y', yz)
    lv1 = dict(lv); lv1.update(z['lv'])
    yr = crect_in(w, A1, RA, RB, ra[0], rb[0], 'y', z['cc'], [rl, rh, il, ih, ra[1], ra[2], rb[1], rb[2]], lv1)
    right = s1([yr, s1([z['fz'], sin_], 'jca', '( ( F ` y ) = 0 /\\ %s )' % SINy)], 'jca', PR)
    A2 = '( %s /\\ %s )' % (A0, PR)
    s2 = St(w, A2)
    L, ra, rb, tm, lv = base(A2)
    pr_ = s2([], 'simpr', PR)
    yrr, fs = conj_split(w, A2, pr_)
    fz2, sin2 = conj_split(w, A2, fs)
    r_, i_ = conj_split(w, A2, sin2)
    rl, rh = conj_split(w, A2, r_); il, ih = conj_split(w, A2, i_)
    d = crect_bounds(w, A2, ra[0], rb[0], yrr, RA, RB, 'y')
    lv2 = dict(lv); lv2.update(d['cl'])
    yzs = zs_mem(w, A2, 'F', TM, tm, 'y', d['cc'], [rl, rh, il, ih, L(s9), L(c54), L(hl1), L(llh)], lv2, fz2)
    left = s2([yzs, sin2], 'jca', PL)
    core = s([right, left], 'impbida', '( %s <-> %s )' % (PL, PR))
    ee = s([core, L1, R1], '3bitr4g', '( y e. { p e. %s | %s } <-> y e. %s )' % (ZSM, SIN('p'), ZR()))
    w.qed([ee], 'eqrdv', S['ef3cs'])
    return run8(w)


def inst_all(w, A, al, var, val, valin, body):
    """( A -> body[var:=val] ) from al : ( A -> A. var e. X body ) and valin : ( A -> val e. X )"""
    eq, new = w.wcongr(body, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
    return w.s([eq, al, valin], 'rspcdva', '( %s -> %s )' % (A, new))


def gen_c1():
    w = W('ef3c1', 'One strip of Lean ` rectInt_chain ` : ` rectInt_strip ` with its frame hypothesis derived from the horizontal lines, the left edge and ` 1 < C ` , summed over the rectangle zeros strictly inside.')
    A0, G = ante_of(S['ef3c1'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); h3 = s([], 'simp3', H3)
    dd, yh, sch = conj_split(w, A0, h1)
    scr, so, c1 = conj_split(w, A0, sch)
    sr, cr = conj_split(w, A0, scr); s9, slc = conj_split(w, A0, so); c1g, c54 = conj_split(w, A0, c1)
    lhr, lho = conj_split(w, A0, h2); lr, hr = conj_split(w, A0, lhr); llh, hl1 = conj_split(w, A0, lho)
    lns, le = conj_split(w, A0, h3); lnl, lnh = conj_split(w, A0, lns)
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    A1 = '( %s /\\ p e. %s )' % (A0, RECT)
    A2 = '( %s /\\ ( F ` p ) = 0 )' % A1
    s2 = St(w, A2)
    L = lambda st: lift(w, st, A2)
    ra = crfacts(w, A2, 'S', 'L', L(sr), L(lr)); rb = crfacts(w, A2, 'C', 'H', L(cr), L(hr))
    pin = lift(w, w.s([], 'simpr', '( %s -> p e. %s )' % (A1, RECT)), A2)
    fz = s2([], 'simpr', '( F ` p ) = 0')
    d = crect_bounds(w, A2, ra[0], rb[0], pin, RA, RB, 'p')
    lv = dict(d['cl']); lv.update({'S': L(sr), 'C': L(cr), 'L': L(lr), 'H': L(hr)})
    hy = d['le'] + [ra[1], ra[2], rb[1], rb[2]]
    rep = s2([d['cc'], w.inst('replim')], 'syl', 'p = ( ( Re ` p ) + ( _i x. ( Im ` p ) ) )')
    rpr, ipr = lv['( Re ` p )'], lv['( Im ` p )']
    from ef3_a import icc_mem

    def neq(tag, lhs, val):
        A3 = '( %s /\\ %s = %s )' % (A2, lhs, val)
        s3 = St(w, A3)
        L3 = lambda st: lift(w, st, A3)
        eqv = s3([], 'simpr', '%s = %s' % (lhs, val))
        hy3 = [L3(h) for h in hy]
        lv3 = {k: L3(v) for k, v in lv.items()}
        if tag == 'S':
            pe = s3([L3(rep), s3([eqv], 'oveq1d', '( ( Re ` p ) + ( _i x. ( Im ` p ) ) ) = ( S + ( _i x. ( Im ` p ) ) )')], 'eqtrd', 'p = ( S + ( _i x. ( Im ` p ) ) )')
            imi = icc_mem(w, A3, '( Im ` p )', 'L', 'H', L3(ipr), L3(lr) if False else lv3['L'], lv3['H'], lin8(w, A3, hy3, 'L <_ ( Im ` p )', lv3), lin8(w, A3, hy3, '( Im ` p ) <_ H', lv3))
            nz = inst_all(w, A3, lift(w, le, A3), 't', '( Im ` p )', imi, '( F ` ( S + ( _i x. t ) ) ) =/= 0')
            fne = s3([s3([pe], 'fveq2d', '( F ` p ) = ( F ` ( S + ( _i x. ( Im ` p ) ) ) )'), nz], 'eqnetrd', '( F ` p ) =/= 0')
        elif tag == 'C':
            cgt = s3([L3(c1g), eqv], 'breqtrrd', '1 < ( Re ` p )') if False else s3([L3(c1g), s3([eqv], 'eqcomd', 'C = ( Re ` p )')], 'breqtrd', '1 < ( Re ` p )')
            e2 = s3([s3([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( p e. %s <-> ( p e. CC /\\ 0 < ( Re ` p ) ) )' % HP0)
            php = s3([s3([L3(d['cc']), lin8(w, A3, [cgt], '0 < ( Re ` p )', lv3)], 'jca', '( p e. CC /\\ 0 < ( Re ` p ) )'), e2], 'mpbird', 'p e. %s' % HP0)
            im = inst_all(w, A3, lift(w, nzw, A3), 'w', 'p', php, '( 1 < ( Re ` w ) -> ( F ` w ) =/= 0 )')
            fne = s3([cgt, im], 'mpd', '( F ` p ) =/= 0')
        else:
            h_ = tag
            pe = s3([L3(rep), s3([s3([eqv], 'oveq2d', '( _i x. ( Im ` p ) ) = ( _i x. %s )' % h_)], 'oveq2d', '( ( Re ` p ) + ( _i x. ( Im ` p ) ) ) = ( ( Re ` p ) + ( _i x. %s ) )' % h_)], 'eqtrd', 'p = ( ( Re ` p ) + ( _i x. %s ) )' % h_)
            rei = icc_mem(w, A3, '( Re ` p )', 'S', 'C', lv3['( Re ` p )'], lv3['S'], lv3['C'], lin8(w, A3, hy3, 'S <_ ( Re ` p )', lv3), lin8(w, A3, hy3, '( Re ` p ) <_ C', lv3))
            nz = inst_all(w, A3, lift(w, lnl if h_ == 'L' else lnh, A3), 'x', '( Re ` p )', rei, '( F ` ( x + ( _i x. %s ) ) ) =/= 0' % h_)
            fne = s3([s3([pe], 'fveq2d', '( F ` p ) = ( F ` ( ( Re ` p ) + ( _i x. %s ) ) )' % h_), nz], 'eqnetrd', '( F ` p ) =/= 0')
        nn = s3([fne], 'neneqd', '-. ( F ` p ) = 0')
        im2 = w.s([nn], 'ex', '( %s -> ( %s = %s -> -. ( F ` p ) = 0 ) )' % (A2, lhs, val))
        return s2([fz, s2([im2], 'necon2ad', '( ( F ` p ) = 0 -> %s =/= %s )' % (lhs, val))], 'mpd', '%s =/= %s' % (lhs, val))
    nS = neq('S', '( Re ` p )', 'S'); nC = neq('C', '( Re ` p )', 'C'); nL = neq('L', '( Im ` p )', 'L'); nH = neq('H', '( Im ` p )', 'H')
    def strict(a, b, ar_, br_, le_, ne_):
        return s2([le_, ne_, s2([ar_, br_], 'ltlend', '( %s < %s <-> ( %s <_ %s /\\ %s =/= %s ) )' % (a, b, a, b, b, a))], 'mpbir2and', '%s < %s' % (a, b))
    t1 = strict('S', '( Re ` p )', lv['S'], rpr, lin8(w, A2, hy, 'S <_ ( Re ` p )', lv), nS)
    t2 = strict('( Re ` p )', 'C', rpr, lv['C'], lin8(w, A2, hy, '( Re ` p ) <_ C', lv), s2([nC], 'necomd', 'C =/= ( Re ` p )'))
    t3 = strict('L', '( Im ` p )', lv['L'], ipr, lin8(w, A2, hy, 'L <_ ( Im ` p )', lv), nL)
    t4 = strict('( Im ` p )', 'H', ipr, lv['H'], lin8(w, A2, hy, '( Im ` p ) <_ H', lv), s2([nH], 'necomd', 'H =/= ( Im ` p )'))
    sin_ = s2([s2([t1, t2], 'jca', '( S < ( Re ` p ) /\\ ( Re ` p ) < C )'), s2([t3, t4], 'jca', '( L < ( Im ` p ) /\\ ( Im ` p ) < H )')], 'jca', SIN('p'))
    e1 = w.s([sin_], 'ex', '( %s -> ( ( F ` p ) = 0 -> %s ) )' % (A1, SIN('p')))
    frh = s([e1], 'ralrimiva', 'A. p e. %s ( ( F ` p ) = 0 -> %s )' % (RECT, SIN('p')))
    SH = ante_of(stmt('ef2strip'))[0]
    _, shf, _ = top_and(SH)
    so3 = s([s9, slc, c54], '3jca', '( ( 9 / ; 1 6 ) <_ S /\\ S < C /\\ C <_ ( 5 / 4 ) )')
    shs = s([yh, s([scr, so3], 'jca', '( ( S e. RR /\\ C e. RR ) /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S < C /\\ C <_ ( 5 / 4 ) ) )'), h2], '3jca', shf)
    stp = s([s([dd, shs, frh], '3jca', SH), w.inst('ef2strip')], 'syl', ante_of(stmt('ef2strip'))[1])
    csa = s([s([scr, s([s9, c54], 'jca', '( ( 9 / ; 1 6 ) <_ S /\\ C <_ ( 5 / 4 ) )')], 'jca', '( ( S e. RR /\\ C e. RR ) /\\ ( ( 9 / ; 1 6 ) <_ S /\\ C <_ ( 5 / 4 ) ) )'), h2], 'jca', ante_of(S['ef3cs'])[0])
    cs = s([csa, w.inst('ef3cs')], 'syl', ante_of(S['ef3cs'])[1])
    ZI_ = '{ p e. %s | %s }' % (ZSM, SIN('p'))
    se = s([s([cs], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (ZI_, RSUM(), ZR(), RSUM()))], 'oveq2d', '( %s x. sum_ q e. %s %s ) = ( %s x. sum_ q e. %s %s )' % (TPI, ZI_, RSUM(), TPI, ZR(), RSUM()))
    w.qed([stp, se], 'eqtrd', S['ef3c1'])
    return run8(w)


ZRX = lambda a, b: ZR('S', 'C', a, b)
S['ef3zrm'] = ('( ( ( S e. RR /\\ C e. RR ) /\\ ( L e. RR /\\ H e. RR ) ) -> ( X e. %s <-> ( X e. CC /\\ ( ( F ` X ) = 0 /\\ %s ) ) ) )') % (ZR(), SIN('X'))


def gen_zrm():
    w = W('ef3zrm', 'Membership in the set of zeros strictly inside a rectangle.')
    A0, G = ante_of(S['ef3zrm'])
    s = St(w, A0)
    sc, lh = top_and(A0)
    sc = s([], 'simpl', sc); lh = s([], 'simpr', lh)
    sr, cr = conj_split(w, A0, sc); lr, hr = conj_split(w, A0, lh)
    Q = '( ( F ` X ) = 0 /\\ %s )' % SIN('X')
    el, _ = elrab_(w, 'p', RECT, '( ( F ` p ) = 0 /\\ %s )' % SIN('p'), 'X')
    P1 = '( X e. %s /\\ %s )' % (RECT, Q)
    P2 = '( X e. CC /\\ %s )' % Q
    def base(A):
        L = lambda st: lift(w, st, A)
        ra = crfacts(w, A, 'S', 'L', L(sr), L(lr)); rb = crfacts(w, A, 'C', 'H', L(cr), L(hr))
        return L, ra, rb
    A1 = '( %s /\\ %s )' % (A0, P1)
    s1 = St(w, A1)
    L, ra, rb = base(A1)
    x1, q1 = conj_split(w, A1, s1([], 'simpr', P1))
    d = crect_bounds(w, A1, ra[0], rb[0], x1, RA, RB, 'X')
    r1 = s1([d['cc'], q1], 'jca', P2)
    A2 = '( %s /\\ %s )' % (A0, P2)
    s2 = St(w, A2)
    L, ra, rb = base(A2)
    xc, q2 = conj_split(w, A2, s2([], 'simpr', P2))
    fz, sn = conj_split(w, A2, q2)
    r_, i_ = conj_split(w, A2, sn)
    rl, rh = conj_split(w, A2, r_); il, ih = conj_split(w, A2, i_)
    lv = {'S': L(sr), 'C': L(cr), 'L': L(lr), 'H': L(hr), '( Re ` X )': s2([xc], 'recld', '( Re ` X ) e. RR'), '( Im ` X )': s2([xc], 'imcld', '( Im ` X ) e. RR')}
    xr = crect_in(w, A2, RA, RB, ra[0], rb[0], 'X', xc, [rl, rh, il, ih, ra[1], ra[2], rb[1], rb[2]], lv)
    r2 = s2([xr, q2], 'jca', P1)
    core = s([r1, r2], 'impbida', '( %s <-> %s )' % (P1, P2))
    w.qed([s([el], 'a1i', '( X e. %s <-> %s )' % (ZR(), P1)), core], 'bitrd', S['ef3zrm'])
    return run8(w)


S['ef3zsp'] = ('( ( ( ( S e. RR /\\ C e. RR ) /\\ ( V e. RR /\\ L e. RR /\\ H e. RR ) ) /\\ ( V < L /\\ L < H ) /\\ %s ) -> '
               '( %s = ( %s u. %s ) /\\ ( %s i^i %s ) = (/) ) )') % (LN('L'), ZRX('V', 'H'), ZRX('V', 'L'), ZRX('L', 'H'), ZRX('V', 'L'), ZRX('L', 'H'))


def gen_zsp():
    w = W('ef3zsp', 'Cutting a rectangle at a zero-free height ` L ` splits its interior zeros into the two parts (Lean ` chain_sum_eq_box ` , inductive step).')
    A0, G = ante_of(S['ef3zsp'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); o = s([], 'simp2', H2); ln = s([], 'simp3', H3)
    sc, vlh = conj_split(w, A0, h1); sr, cr = conj_split(w, A0, sc); vr, lr, hr = conj_split(w, A0, vlh)
    vl, lh = conj_split(w, A0, o)
    from ef3_a import icc_mem
    def mem(A, a, b, ar_, br_, y='y'):
        """closed-in-A biconditional ( y e. ZR(a,b) <-> ( y e. CC /\\ ( F y = 0 /\\ SIN ) ) )"""
        L = lambda st: lift(w, st, A)
        hyp = w.s([w.s([L(sr), L(cr)], 'jca', '( %s -> ( S e. RR /\\ C e. RR ) )' % A), w.s([ar_, br_], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (A, a, b))], 'jca', '( %s -> ( ( S e. RR /\\ C e. RR ) /\\ ( %s e. RR /\\ %s e. RR ) ) )' % (A, a, b))
        return w.s([hyp, w.inst('ef3zrm')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( ( F ` %s ) = 0 /\\ %s ) ) ) )' % (A, y, ZRX(a, b), y, y, SIN(y, 'S', 'C', a, b)))
    Pf = lambda a, b: '( y e. CC /\\ ( ( F ` y ) = 0 /\\ %s ) )' % SIN('y', 'S', 'C', a, b)
    P1, P2, P3 = Pf('V', 'H'), Pf('V', 'L'), Pf('L', 'H')
    def unpack(A, st):
        yc, q = conj_split(w, A, st); fz, sn = conj_split(w, A, q); r_, i_ = conj_split(w, A, sn)
        rl, rh = conj_split(w, A, r_); il, ih = conj_split(w, A, i_)
        return yc, fz, [rl, rh, il, ih]
    def pack(A, yc, fz, bnds, a, b, lv):
        sn = w.s([w.s([lin8(w, A, bnds, 'S < ( Re ` y )', lv), lin8(w, A, bnds, '( Re ` y ) < C', lv)], 'jca', '( %s -> ( S < ( Re ` y ) /\\ ( Re ` y ) < C ) )' % A),
                  w.s([lin8(w, A, bnds, '%s < ( Im ` y )' % a, lv), lin8(w, A, bnds, '( Im ` y ) < %s' % b, lv)], 'jca', '( %s -> ( %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) )' % (A, a, b))],
                 'jca', '( %s -> %s )' % (A, SIN('y', 'S', 'C', a, b)))
        return w.s([yc, w.s([fz, sn], 'jca', '( %s -> ( ( F ` y ) = 0 /\\ %s ) )' % (A, SIN('y', 'S', 'C', a, b)))], 'jca', '( %s -> %s )' % (A, Pf(a, b)))
    def lvs(A, yc):
        L = lambda st: lift(w, st, A)
        return {'S': L(sr), 'C': L(cr), 'V': L(vr), 'L': L(lr), 'H': L(hr), '( Re ` y )': w.s([yc], 'recld', '( %s -> ( Re ` y ) e. RR )' % A), '( Im ` y )': w.s([yc], 'imcld', '( %s -> ( Im ` y ) e. RR )' % A)}
    # -> : P1 gives P2 or P3
    A1 = '( %s /\\ %s )' % (A0, P1)
    s1 = St(w, A1)
    L1 = lambda st: lift(w, st, A1)
    yc, fz, bn = unpack(A1, s1([], 'simpr', P1))
    lv = lvs(A1, yc)
    # Im y =/= L
    A3 = '( %s /\\ ( Im ` y ) = L )' % A1
    s3 = St(w, A3)
    L3 = lambda st: lift(w, st, A3)
    lv3 = {k: L3(v) for k, v in lv.items()}
    eqv = s3([], 'simpr', '( Im ` y ) = L')
    pe = s3([s3([L3(yc), w.inst('replim')], 'syl', 'y = ( ( Re ` y ) + ( _i x. ( Im ` y ) ) )'), s3([s3([eqv], 'oveq2d', '( _i x. ( Im ` y ) ) = ( _i x. L )')], 'oveq2d', '( ( Re ` y ) + ( _i x. ( Im ` y ) ) ) = ( ( Re ` y ) + ( _i x. L ) )')], 'eqtrd', 'y = ( ( Re ` y ) + ( _i x. L ) )')
    rei = icc_mem(w, A3, '( Re ` y )', 'S', 'C', lv3['( Re ` y )'], lv3['S'], lv3['C'], lin8(w, A3, [L3(b) for b in bn], 'S <_ ( Re ` y )', lv3), lin8(w, A3, [L3(b) for b in bn], '( Re ` y ) <_ C', lv3))
    nz = inst_all(w, A3, L3(ln), 'x', '( Re ` y )', rei, '( F ` ( x + ( _i x. L ) ) ) =/= 0')
    fne = s3([s3([pe], 'fveq2d', '( F ` y ) = ( F ` ( ( Re ` y ) + ( _i x. L ) ) )'), nz], 'eqnetrd', '( F ` y ) =/= 0')
    im3 = w.s([s3([fne], 'neneqd', '-. ( F ` y ) = 0')], 'ex', '( %s -> ( ( Im ` y ) = L -> -. ( F ` y ) = 0 ) )' % A1)
    ne = s1([fz, s1([im3], 'necon2ad', '( ( F ` y ) = 0 -> ( Im ` y ) =/= L )')], 'mpd', '( Im ` y ) =/= L')
    tri = s1([lv['( Im ` y )'], L1(lr), w.inst('lelttric')], 'syl2anc', '( ( Im ` y ) <_ L \\/ L < ( Im ` y ) )')
    A4 = '( %s /\\ ( Im ` y ) <_ L )' % A1
    L4 = lambda st: lift(w, st, A4)
    lv4 = {k: L4(v) for k, v in lv.items()}
    ile = St(w, A4)([], 'simpr', '( Im ` y ) <_ L')
    ilt = St(w, A4)([ile, L4(ne), St(w, A4)([lv4['( Im ` y )'], lv4['L']], 'ltlend', '( ( Im ` y ) < L <-> ( ( Im ` y ) <_ L /\\ L =/= ( Im ` y ) ) )') if False else None], 'id', 'x') if False else None
    ne4 = St(w, A4)([L4(ne)], 'necomd', 'L =/= ( Im ` y )')
    ilt = St(w, A4)([ile, ne4, St(w, A4)([lv4['( Im ` y )'], lv4['L']], 'ltlend', '( ( Im ` y ) < L <-> ( ( Im ` y ) <_ L /\\ L =/= ( Im ` y ) ) )')], 'mpbir2and', '( Im ` y ) < L')
    p2 = pack(A4, L4(yc), L4(fz), [L4(b) for b in bn] + [ilt], 'V', 'L', lv4)
    c1 = w.s([St(w, A4)([p2], 'orcd', '( %s \\/ %s )' % (P2, P3))], 'ex', '( %s -> ( ( Im ` y ) <_ L -> ( %s \\/ %s ) ) )' % (A1, P2, P3))
    A5 = '( %s /\\ L < ( Im ` y ) )' % A1
    L5 = lambda st: lift(w, st, A5)
    lv5 = {k: L5(v) for k, v in lv.items()}
    p3 = pack(A5, L5(yc), L5(fz), [L5(b) for b in bn] + [St(w, A5)([], 'simpr', 'L < ( Im ` y )')], 'L', 'H', lv5)
    c2 = w.s([St(w, A5)([p3], 'olcd', '( %s \\/ %s )' % (P2, P3))], 'ex', '( %s -> ( L < ( Im ` y ) -> ( %s \\/ %s ) ) )' % (A1, P2, P3))
    fw = s1([c1, c2, tri], 'mpjaod', '( %s \\/ %s )' % (P2, P3))
    # <-
    bk = []
    for (a, b), extra in ((('V', 'L'), 'lh'), (('L', 'H'), 'vl')):
        A6 = '( %s /\\ %s )' % (A0, Pf(a, b))
        L6 = lambda st: lift(w, st, A6)
        yc6, fz6, bn6 = unpack(A6, St(w, A6)([], 'simpr', Pf(a, b)))
        lv6 = lvs(A6, yc6)
        bk.append(pack(A6, yc6, fz6, bn6 + [L6(vl), L6(lh)], 'V', 'H', lv6))
    back = w.s(bk, 'jaodan', '( ( %s /\\ ( %s \\/ %s ) ) -> %s )' % (A0, P2, P3, P1))
    core = s([fw, back], 'impbida', '( %s <-> ( %s \\/ %s ) )' % (P1, P2, P3))
    m1 = mem(A0, 'V', 'H', vr, hr); m2 = mem(A0, 'V', 'L', vr, lr); m3 = mem(A0, 'L', 'H', lr, hr)
    orb = s([m2, m3], 'orbi12d', '( ( y e. %s \\/ y e. %s ) <-> ( %s \\/ %s ) )' % (ZRX('V', 'L'), ZRX('L', 'H'), P2, P3))
    elu = s([w.s([], 'elun', '( y e. ( %s u. %s ) <-> ( y e. %s \\/ y e. %s ) )' % (ZRX('V', 'L'), ZRX('L', 'H'), ZRX('V', 'L'), ZRX('L', 'H')))], 'a1i',
            '( y e. ( %s u. %s ) <-> ( y e. %s \\/ y e. %s ) )' % (ZRX('V', 'L'), ZRX('L', 'H'), ZRX('V', 'L'), ZRX('L', 'H')))
    un = s([elu, orb], 'bitrd', '( y e. ( %s u. %s ) <-> ( %s \\/ %s ) )' % (ZRX('V', 'L'), ZRX('L', 'H'), P2, P3))
    eqb = s([s([m1, core], 'bitrd', '( y e. %s <-> ( %s \\/ %s ) )' % (ZRX('V', 'H'), P2, P3)), un], 'bitr4d', '( y e. %s <-> y e. ( %s u. %s ) )' % (ZRX('V', 'H'), ZRX('V', 'L'), ZRX('L', 'H')))
    eq = s([eqb], 'eqrdv', '%s = ( %s u. %s )' % (ZRX('V', 'H'), ZRX('V', 'L'), ZRX('L', 'H')))
    # disjoint
    A7 = '( %s /\\ y e. %s )' % (A0, ZRX('V', 'L'))
    s7 = St(w, A7)
    L7 = lambda st: lift(w, st, A7)
    p7 = s7([s7([], 'simpr', 'y e. %s' % ZRX('V', 'L')), L7(m2)], 'mpbid', P2)
    yc7, fz7, bn7 = unpack(A7, p7)
    lv7 = lvs(A7, yc7)
    A8 = '( %s /\\ y e. %s )' % (A7, ZRX('L', 'H'))
    s8 = St(w, A8)
    p8 = s8([s8([], 'simpr', 'y e. %s' % ZRX('L', 'H')), lift(w, m3, A8)], 'mpbid', P3)
    _, _, bn8 = unpack(A8, p8)
    im8 = w.s([bn8[2]], 'ex', '( %s -> ( y e. %s -> L < ( Im ` y ) ) )' % (A7, ZRX('L', 'H')))
    nl = s7([s7([lv7['( Im ` y )'], lv7['L'], w.inst('ltnsym')], 'syl2anc', '( ( Im ` y ) < L -> -. L < ( Im ` y ) )'), bn7[3]], 'mpd', '-. L < ( Im ` y )') if False else \
        s7([bn7[3], s7([lv7['( Im ` y )'], lv7['L'], w.inst('ltnsym')], 'syl2anc', '( ( Im ` y ) < L -> -. L < ( Im ` y ) )')], 'mpd', '-. L < ( Im ` y )')
    ny = s7([nl, im8], 'mtod', '-. y e. %s' % ZRX('L', 'H'))
    dj = s([s([ny], 'ralrimiva', 'A. y e. %s -. y e. %s' % (ZRX('V', 'L'), ZRX('L', 'H'))), w.s([], 'disj', '( ( %s i^i %s ) = (/) <-> A. y e. %s -. y e. %s )' % (ZRX('V', 'L'), ZRX('L', 'H'), ZRX('V', 'L'), ZRX('L', 'H')))],
           'sylibr', '( %s i^i %s ) = (/)' % (ZRX('V', 'L'), ZRX('L', 'H')))
    w.qed([eq, dj], 'jca', S['ef3zsp'])
    return run8(w)


SCB = '( ( S e. RR /\\ C e. RR ) /\\ ( ( 1 / 2 ) <_ S /\\ C <_ ( 3 / 2 ) ) )'
S['ef3zsum'] = ('( ( ( %s /\\ Y e. RR+ /\\ %s ) /\\ ( ( V e. RR /\\ L e. RR /\\ H e. RR ) /\\ ( V < L /\\ L < H ) ) /\\ %s ) -> '
                '( sum_ q e. %s %s = ( sum_ q e. %s %s + sum_ q e. %s %s ) /\\ sum_ q e. %s %s e. CC /\\ sum_ q e. %s %s e. CC ) )') % (
    DD(), SCB, LN('L'), ZRX('V', 'H'), RSUM(), ZRX('V', 'L'), RSUM(), ZRX('L', 'H'), RSUM(), ZRX('V', 'L'), RSUM(), ZRX('L', 'H'), RSUM())


def rsum_cc(w, A, st_zrm, ordnn, yp, sr, s12):
    """( A -> RSUM(q) e. CC ) from st_zrm : ( A -> ( q e. CC /\\ ( F q = 0 /\\ SIN ) ) ), ordnn : ( A -> ( F holord q ) e. NN ), Y e. RR+, S e. RR, 1/2 <_ S"""
    s_ = St(w, A)
    qc, rest = conj_split(w, A, st_zrm)
    fz, sn = conj_split(w, A, rest); r_, _ = conj_split(w, A, sn); rl, _ = conj_split(w, A, r_)
    rer = s_([qc], 'recld', '( Re ` q ) e. RR')
    rp = lin8(w, A, [rl, s12], '0 < ( Re ` q )', {'S': sr, '( Re ` q )': rer})
    r0 = w.s([w.s([], 'fveq2', '( q = 0 -> ( Re ` q ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( q = 0 -> ( Re ` q ) = 0 )')
    qn = s_([s_([rp], 'gt0ne0d', '( Re ` q ) =/= 0'), w.s([r0], 'necon3i', '( ( Re ` q ) =/= 0 -> q =/= 0 )')], 'syl', 'q =/= 0')
    yc = s_([s_([yp], 'rpcnd', 'Y e. CC'), qc], 'cxpcld', '( Y ^c q ) e. CC')
    return s_([s_([ordnn], 'nncnd', '( F holord q ) e. CC'), s_([yc, qc, qn], 'divcld', '( ( Y ^c q ) / q ) e. CC')], 'mulcld', '%s e. CC' % RSUM())


def gen_zsum():
    w = W('ef3zsum', 'The residue sum of a rectangle cut at a zero-free height is the sum of the residue sums of the two parts.')
    A0, G = ante_of(S['ef3zsum'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); ln = s([], 'simp3', H3)
    dd, yp, scb = conj_split(w, A0, h1)
    sc, sb = conj_split(w, A0, scb); sr, cr = conj_split(w, A0, sc); s12, c32 = conj_split(w, A0, sb)
    vlh, o = conj_split(w, A0, h2); vr, lr, hr = conj_split(w, A0, vlh)
    zsp = s([s([s([sc, vlh], 'jca', '( ( S e. RR /\\ C e. RR ) /\\ ( V e. RR /\\ L e. RR /\\ H e. RR ) )'), o, ln], '3jca', ante_of(S['ef3zsp'])[0]), w.inst('ef3zsp')], 'syl', ante_of(S['ef3zsp'])[1])
    eq, dj = conj_split(w, A0, zsp)
    def part(a, b, ar_, br_):
        zrf = s([s([dd, scb, s([ar_, br_], 'jca', '( %s e. RR /\\ %s e. RR )' % (a, b))], '3jca', tsub(ante_of(S['ef3zrf'])[0], {'L': a, 'H': b})), w.inst('ef3zrf')], 'syl', tsub(ante_of(S['ef3zrf'])[1], {'L': a, 'H': b}))
        zf, zo = conj_split(w, A0, zrf)
        A1 = '( %s /\\ q e. %s )' % (A0, ZRX(a, b))
        L = lambda st: lift(w, st, A1)
        qin = St(w, A1)([], 'simpr', 'q e. %s' % ZRX(a, b))
        zrm = St(w, A1)([qin, St(w, A1)([St(w, A1)([L(sc), St(w, A1)([L(ar_), L(br_)], 'jca', '( %s e. RR /\\ %s e. RR )' % (a, b))], 'jca', '( ( S e. RR /\\ C e. RR ) /\\ ( %s e. RR /\\ %s e. RR ) )' % (a, b)), w.inst('ef3zrm')], 'syl',
                        '( q e. %s <-> ( q e. CC /\\ ( ( F ` q ) = 0 /\\ %s ) ) )' % (ZRX(a, b), SIN('q', 'S', 'C', a, b)))], 'mpbid', '( q e. CC /\\ ( ( F ` q ) = 0 /\\ %s ) )' % SIN('q', 'S', 'C', a, b))
        onn = St(w, A1)([L(zo), qin, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
        cc = rsum_cc(w, A1, zrm, onn, L(yp), L(sr), L(s12))
        return zf, cc
    zf, cc = part('V', 'H', vr, hr)
    spl = s([dj, eq, zf, cc], 'fsumsplit', 'sum_ q e. %s %s = ( sum_ q e. %s %s + sum_ q e. %s %s )' % (ZRX('V', 'H'), RSUM(), ZRX('V', 'L'), RSUM(), ZRX('L', 'H'), RSUM()))
    zf1, cc1 = part('V', 'L', vr, lr)
    zf2, cc2 = part('L', 'H', lr, hr)
    c1 = s([zf1, cc1], 'fsumcl', 'sum_ q e. %s %s e. CC' % (ZRX('V', 'L'), RSUM()))
    c2 = s([zf2, cc2], 'fsumcl', 'sum_ q e. %s %s e. CC' % (ZRX('L', 'H'), RSUM()))
    w.qed([spl, c1, c2], '3jca', S['ef3zsum'])
    return run8(w)


RVL = lambda a, b: '( %s rectint <. %s , %s >. )' % (LDI(), '( S + ( _i x. %s ) )' % a, '( C + ( _i x. %s ) )' % b)
RHSX = lambda a, b: '( %s x. sum_ q e. %s %s )' % (TPI, ZRX(a, b), RSUM())
S['ef3cstep'] = ('( ( ( %s /\\ ( Y e. RR /\\ 1 < Y ) /\\ %s ) /\\ ( ( V e. RR /\\ L e. RR /\\ H e. RR ) /\\ ( V < L /\\ L < H /\\ ( H - L ) <_ 1 ) ) /\\ '
                 '( ( %s /\\ %s /\\ %s ) /\\ %s /\\ %s = %s ) ) -> %s = %s )') % (
    DD(), SCH1, LN('V'), LN('L'), LN('H'), LE('V', 'H'), RVL('V', 'L'), RHSX('V', 'L'), RVL('V', 'H'), RHSX('V', 'H'))


def ld0_in(w, A, z, zc, rep, fnz):
    """( A -> z e. LD0 ) from z e. CC, ( A -> 0 < ( Re ` z ) ), ( A -> ( F ` z ) =/= 0 )"""
    s_ = St(w, A)
    e2 = s_([s_([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (z, HP0, z, z))
    zh = s_([s_([zc, rep], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (z, z)), e2], 'mpbird', '%s e. %s' % (z, HP0))
    el, _ = elrab_(w, 'v', HP0, '( F ` v ) =/= 0', z)
    return s_([s_([zh, fnz], 'jca', '( %s e. %s /\\ ( F ` %s ) =/= 0 )' % (z, HP0, z)), el], 'sylibr', '%s e. %s' % (z, LD0))


def gen_cstep():
    from ef3_a import icc_mem
    w = W('ef3cstep', 'The induction step of Lean ` rectInt_chain ` fused with ` chain_sum_eq_box ` : adding the strip ` [ L , H ] ` on top of the rectangle ` [ S , C ] x. [ V , L ] ` .')
    A0, G = ante_of(S['ef3cstep'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); h3 = s([], 'simp3', H3)
    dd, yh, sch = conj_split(w, A0, h1)
    yr, y1 = conj_split(w, A0, yh)
    scr, so, c1 = conj_split(w, A0, sch)
    sr, cr = conj_split(w, A0, scr); s9, slc = conj_split(w, A0, so); c1g, c54 = conj_split(w, A0, c1)
    vlh, o3 = conj_split(w, A0, h2); vr, lr, hr = conj_split(w, A0, vlh); vl, lh, hl1 = conj_split(w, A0, o3)
    lns, le, ih = conj_split(w, A0, h3); lnv, lnl, lnh = conj_split(w, A0, lns)
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    lv = {'S': sr, 'C': cr, 'V': vr, 'L': lr, 'H': hr, 'Y': yr}
    yp = s([yr, lin8(w, A0, [y1], '0 < Y', lv)], 'elrpd', 'Y e. RR+')
    ldc = s([s([hol, yp], 'jca', '( %s /\\ Y e. RR+ )' % HOLF('F', HP0)), w.inst('ef3ldc')], 'syl', '%s e. ( %s -cn-> CC )' % (LDI(), LD0))
    def ralcb(A, al_y, var, I, body_y):
        """from al_y : ( A -> A. y e. I body_y ): ( A -> A. var e. I body_y[y:=var] )"""
        eq, new = w.wcongr(body_y, {'y': var}, 'y = %s' % var, {'y': w.s([], 'id', '( y = %s -> y = %s )' % (var, var))})
        cb = w.s([eq], 'cbvralvw', '( A. y e. %s %s <-> A. %s e. %s %s )' % (I, body_y, var, I, new))
        return St(w, A)([al_y, cb], 'sylib', 'A. %s e. %s %s' % (var, I, new))
    # vertical lines in LD0
    IV = '( V [,] H )'
    A1 = '( %s /\\ y e. %s )' % (A0, IV)
    s1 = St(w, A1)
    L1 = lambda st: lift(w, st, A1)
    tin = s1([], 'simpr', 'y e. %s' % IV)
    tr = s1([s1([L1(vr), L1(hr)], 'iccssred', '%s C_ RR' % IV), tin], 'sseldd', 'y e. RR')
    sp = crfacts(w, A1, 'S', 'y', L1(sr), tr); cp = crfacts(w, A1, 'C', 'y', L1(cr), tr)
    fs = inst_all(w, A1, L1(le), 't', 'y', tin, '( F ` ( S + ( _i x. t ) ) ) =/= 0')
    rs = s1([lin8(w, A1, [L1(s9)], '0 < S', {'S': L1(sr)}), sp[1]], 'breqtrrd', '0 < ( Re ` ( S + ( _i x. y ) ) )')
    sin_ = ld0_in(w, A1, '( S + ( _i x. y ) )', sp[0], rs, fs)
    cgt = s1([L1(c1g), s1([cp[1]], 'eqcomd', 'C = ( Re ` ( C + ( _i x. y ) ) )')], 'breqtrd', '1 < ( Re ` ( C + ( _i x. y ) ) )')
    rc = s1([lin8(w, A1, [L1(c1g)], '0 < C', {'C': L1(cr)}), cp[1]], 'breqtrrd', '0 < ( Re ` ( C + ( _i x. y ) ) )')
    e2 = s1([s1([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( ( C + ( _i x. y ) ) e. %s <-> ( ( C + ( _i x. y ) ) e. CC /\\ 0 < ( Re ` ( C + ( _i x. y ) ) ) ) )' % HP0)
    chp = s1([s1([cp[0], rc], 'jca', '( ( C + ( _i x. y ) ) e. CC /\\ 0 < ( Re ` ( C + ( _i x. y ) ) ) )'), e2], 'mpbird', '( C + ( _i x. y ) ) e. %s' % HP0)
    fc = s1([cgt, inst_all(w, A1, L1(nzw), 'w', '( C + ( _i x. y ) )', chp, '( 1 < ( Re ` w ) -> ( F ` w ) =/= 0 )')], 'mpd', '( F ` ( C + ( _i x. y ) ) ) =/= 0')
    cin = ld0_in(w, A1, '( C + ( _i x. y ) )', cp[0], rc, fc)
    BV = '( ( S + ( _i x. y ) ) e. %s /\\ ( C + ( _i x. y ) ) e. %s )' % (LD0, LD0)
    alv = ralcb(A0, s([s1([sin_, cin], 'jca', BV)], 'ralrimiva', 'A. y e. %s %s' % (IV, BV)), 't', IV, BV)
    # horizontal lines in LD0
    IH = '( S [,] C )'
    A2 = '( %s /\\ y e. %s )' % (A0, IH)
    s2 = St(w, A2)
    L2 = lambda st: lift(w, st, A2)
    xin = s2([], 'simpr', 'y e. %s' % IH)
    xr = s2([s2([L2(sr), L2(cr)], 'iccssred', '%s C_ RR' % IH), xin], 'sseldd', 'y e. RR')
    e3 = s2([L2(sr), L2(cr), w.inst('elicc2')], 'syl2anc', '( y e. %s <-> ( y e. RR /\\ S <_ y /\\ y <_ C ) )' % IH)
    xs = s2([s2([xin, e3], 'mpbid', '( y e. RR /\\ S <_ y /\\ y <_ C )'), w.inst('simp2')], 'syl', 'S <_ y')
    hs = []
    for h_, lnh_ in (('V', lnv), ('L', lnl), ('H', lnh)):
        xp = crfacts(w, A2, 'y', h_, xr, L2(lv[h_]))
        fx = inst_all(w, A2, L2(lnh_), 'x', 'y', xin, '( F ` ( x + ( _i x. %s ) ) ) =/= 0' % h_)
        rx = s2([lin8(w, A2, [xs, L2(s9)], '0 < y', {'S': L2(sr), 'y': xr}), xp[1]], 'breqtrrd', '0 < ( Re ` ( y + ( _i x. %s ) ) )' % h_)
        hs.append(ld0_in(w, A2, '( y + ( _i x. %s ) )' % h_, xp[0], rx, fx))
    H3F = '( ( y + ( _i x. V ) ) e. %s /\\ ( y + ( _i x. L ) ) e. %s /\\ ( y + ( _i x. H ) ) e. %s )' % (LD0, LD0, LD0)
    alh = ralcb(A0, s([s2(hs, '3jca', H3F)], 'ralrimiva', 'A. y e. %s %s' % (IH, H3F)), 'x', IH, H3F)
    VA = tsub(ante_of(S['ef3vsp'])[0], {'F': LDI(), 'D': LD0, 'P': 'S', 'Q': 'C', 'L': 'V', 'M': 'L'})
    VC = tsub(ante_of(S['ef3vsp'])[1], {'F': LDI(), 'D': LD0, 'P': 'S', 'Q': 'C', 'L': 'V', 'M': 'L'})
    Va, Vb, Vc = top_and(VA)
    va = s([ldc, s([s([sr, cr], 'jca', '( S e. RR /\\ C e. RR )'), lin8(w, A0, [slc], 'S <_ C', lv)], 'jca', '( ( S e. RR /\\ C e. RR ) /\\ S <_ C )')], 'jca', Va)
    vb = s([s([vr, hr, lr], '3jca', '( V e. RR /\\ H e. RR /\\ L e. RR )'), s([lin8(w, A0, [vl], 'V <_ L', lv), lin8(w, A0, [lh], 'L <_ H', lv), lin8(w, A0, [vl, lh], 'V < H', lv)], '3jca', '( V <_ L /\\ L <_ H /\\ V < H )')], 'jca', Vb)
    vsp = s([s([va, vb, s([alv, alh], 'jca', Vc)], '3jca', VA), w.inst('ef3vsp')], 'syl', VC)
    # upper strip
    IL = '( L [,] H )'
    A3 = '( %s /\\ y e. %s )' % (A0, IL)
    s3 = St(w, A3)
    L3 = lambda st: lift(w, st, A3)
    t3 = s3([], 'simpr', 'y e. %s' % IL)
    e4 = s3([L3(lr), L3(hr), w.inst('elicc2')], 'syl2anc', '( y e. %s <-> ( y e. RR /\\ L <_ y /\\ y <_ H ) )' % IL)
    tt = s3([t3, e4], 'mpbid', '( y e. RR /\\ L <_ y /\\ y <_ H )')
    tr3, tl3, th3 = conj_split(w, A3, tt)
    tv = icc_mem(w, A3, 'y', 'V', 'H', tr3, L3(vr), L3(hr), lin8(w, A3, [tl3, L3(vl)], 'V <_ y', {'V': L3(vr), 'L': L3(lr), 'y': tr3}), th3)
    BY = '( F ` ( S + ( _i x. y ) ) ) =/= 0'
    lelh = ralcb(A0, s([inst_all(w, A3, L3(le), 't', 'y', tv, '( F ` ( S + ( _i x. t ) ) ) =/= 0')], 'ralrimiva', 'A. y e. %s %s' % (IL, BY)), 't', IL, BY)
    CA = ante_of(S['ef3c1'])[0]
    ca1, ca2, ca3 = top_and(CA)
    c1s = s([h1, s([s([lr, hr], 'jca', '( L e. RR /\\ H e. RR )'), s([lh, hl1], 'jca', '( L < H /\\ ( H - L ) <_ 1 )')], 'jca', ca2), s([s([lnl, lnh], 'jca', '( %s /\\ %s )' % (LN('L'), LN('H'))), lelh], 'jca', ca3)], '3jca', CA)
    up = s([c1s, w.inst('ef3c1')], 'syl', ante_of(S['ef3c1'])[1])
    # sums
    ZA = ante_of(S['ef3zsum'])[0]
    za1, za2, za3 = top_and(ZA)
    scb = s([scr, s([lin8(w, A0, [s9], '( 1 / 2 ) <_ S', lv), lin8(w, A0, [c54], 'C <_ ( 3 / 2 )', lv)], 'jca', '( ( 1 / 2 ) <_ S /\\ C <_ ( 3 / 2 ) )')], 'jca', '( ( S e. RR /\\ C e. RR ) /\\ ( ( 1 / 2 ) <_ S /\\ C <_ ( 3 / 2 ) ) )')
    zs = s([s([s([dd, yp, scb], '3jca', za1), s([vlh, s([vl, lh], 'jca', '( V < L /\\ L < H )')], 'jca', za2), lnl], '3jca', ZA), w.inst('ef3zsum')], 'syl', ante_of(S['ef3zsum'])[1])
    SVL, SLH, SVH = ['sum_ q e. %s %s' % (ZRX(a, b), RSUM()) for a, b in (('V', 'L'), ('L', 'H'), ('V', 'H'))]
    def zcl(a, b, ar_, br_):
        zr = s([s([dd, scb, s([ar_, br_], 'jca', '( %s e. RR /\\ %s e. RR )' % (a, b))], '3jca', tsub(ante_of(S['ef3zrf'])[0], {'L': a, 'H': b})), w.inst('ef3zrf')], 'syl', tsub(ante_of(S['ef3zrf'])[1], {'L': a, 'H': b}))
        return conj_split(w, A0, zr)
    # closure of the two sums: do it in a q-free context via the zsum lemma form is not needed: fsumcl under A0 needs $d q A0
    tpc = s([w.s([], '2cn', '2 e. CC') if False else s([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC'), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    zeq, zc1, zc2 = conj_split(w, A0, zs)
    a1_ = s([vsp, s([ih, up], 'oveq12d', '( %s + %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (RVL('V', 'L'), RVL('L', 'H'), TPI, SVL, TPI, SLH))], 'eqtrd',
            '%s = ( ( %s x. %s ) + ( %s x. %s ) )' % (RVL('V', 'H'), TPI, SVL, TPI, SLH))
    a2_ = s([tpc, zc1, zc2], 'adddid', '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (TPI, SVL, SLH, TPI, SVL, TPI, SLH))
    a3_ = s([zeq], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s + %s ) )' % (TPI, SVH, TPI, SVL, SLH))
    w.qed([a1_, s([a3_, a2_], 'eqtrd', '( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (TPI, SVH, TPI, SVL, TPI, SLH))], 'eqtr4d', S['ef3cstep'])
    return run8(w)


def gen_chain():
    from ef3_a import icc_mem
    w = W('ef3chain', 'Lean ` rectInt_chain ` fused with ` chain_sum_eq_box ` : for heights ` G ( 0 ) < ... < G ( M ) ` with gaps at most 1, zero-free horizontal lines and a zero-free left edge, the boundary integral of ` [ S , C ] x. [ G ( 0 ) , G ( M ) ] ` is ` 2 pi i ` times the residue sum over the zeros strictly inside.')
    A0, G = ante_of(S['ef3chain'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); h3 = s([], 'simp3', H3)
    mg, gp = conj_split(w, A0, h2); mn, gf = conj_split(w, A0, mg)
    hl, le = conj_split(w, A0, h3)
    Gj = lambda j: '( G ` %s )' % j
    IFZ = '( 0 ... M )'; IFO = '( 0 ..^ M )'
    GAP = lambda j: '( %s < %s /\\ ( %s - %s ) <_ 1 )' % (Gj(j), Gj('( %s + 1 )' % j), Gj('( %s + 1 )' % j), Gj(j))
    LEg = lambda a, b: 'A. t e. ( %s [,] %s ) ( F ` ( S + ( _i x. t ) ) ) =/= 0' % (Gj(a), Gj(b))
    EQg = lambda a, b: '%s = %s' % (RVL(Gj(a), Gj(b)), RHSX(Gj(a), Gj(b)))
    PS = lambda n: '( %s <_ M -> ( %s < %s /\\ ( %s -> %s ) ) )' % (n, Gj('0'), Gj(n), LEg('0', n), EQg('0', n))
    def gr(A, k, kin):
        return w.s([lift(w, gf, A), kin], 'ffvelcdmd', '( %s -> %s e. RR )' % (A, Gj(k)))
    def lnat(A, k, kin):
        return inst_all(w, A, lift(w, hl, A), 'j', k, kin, 'A. x e. ( S [,] C ) ( F ` ( x + ( _i x. %s ) ) ) =/= 0' % Gj('j'))
    def ralcb(A, al_y, var, I, body_y):
        eq, new = w.wcongr(body_y, {'y': var}, 'y = %s' % var, {'y': w.s([], 'id', '( y = %s -> y = %s )' % (var, var))})
        cb = w.s([eq], 'cbvralvw', '( A. y e. %s %s <-> A. %s e. %s %s )' % (I, body_y, var, I, new))
        return St(w, A)([al_y, cb], 'sylib', 'A. %s e. %s %s' % (var, I, new))
    mn0 = s([mn], 'nnnn0d', 'M e. NN0')
    z0 = s([mn0, w.inst('0elfz')], 'syl', '0 e. %s' % IFZ)
    # base
    B0 = '( %s /\\ 1 <_ M )' % A0
    sb = St(w, B0)
    Lb = lambda st: lift(w, st, B0)
    zo = sb([Lb(mn), w.s([], 'lbfzo0', '( 0 e. %s <-> M e. NN )' % IFO)], 'sylibr', '0 e. %s' % IFO)
    g0 = inst_all(w, B0, Lb(gp), 'j', '0', zo, GAP('j'))
    e01 = w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'fveq2i', '%s = %s' % (Gj('( 0 + 1 )'), Gj('1')))
    g0a, g0b = conj_split(w, B0, g0)
    lt01 = sb([g0a, sb([e01], 'a1i', '%s = %s' % (Gj('( 0 + 1 )'), Gj('1')))], 'breqtrd', '%s < %s' % (Gj('0'), Gj('1')))
    gap01 = sb([sb([sb([e01], 'a1i', '%s = %s' % (Gj('( 0 + 1 )'), Gj('1')))], 'oveq1d', '( %s - %s ) = ( %s - %s )' % (Gj('( 0 + 1 )'), Gj('0'), Gj('1'), Gj('0'))), g0b], 'eqbrtrrd', '( %s - %s ) <_ 1' % (Gj('1'), Gj('0')))
    z1 = sb([sb([zo, w.inst('fzofzp1')], 'syl', '( 0 + 1 ) e. %s' % IFZ), sb([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( 0 + 1 ) = 1')], 'eqeltrrd', '1 e. %s' % IFZ) if False else \
        sb([sb([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( 0 + 1 ) = 1'), sb([zo, w.inst('fzofzp1')], 'syl', '( 0 + 1 ) e. %s' % IFZ)], 'eqeltrrd', '1 e. %s' % IFZ)
    B1 = '( %s /\\ %s )' % (B0, LEg('0', '1'))
    s1 = St(w, B1)
    L1 = lambda st: lift(w, st, B1)
    CA = tsub(ante_of(S['ef3c1'])[0], {'L': Gj('0'), 'H': Gj('1')})
    ca1, ca2, ca3 = top_and(CA)
    g0r, g1r = gr(B1, '0', L1(lift(w, z0, B0))), gr(B1, '1', L1(z1))
    c1a = s1([L1(Lb(h1)), s1([s1([g0r, g1r], 'jca', '( %s e. RR /\\ %s e. RR )' % (Gj('0'), Gj('1'))), s1([L1(lt01), L1(gap01)], 'jca', '( %s < %s /\\ ( %s - %s ) <_ 1 )' % (Gj('0'), Gj('1'), Gj('1'), Gj('0')))], 'jca', ca2),
              s1([s1([lnat(B1, '0', L1(lift(w, z0, B0))), lnat(B1, '1', L1(z1))], 'jca', top_and(ca3)[0]), s1([], 'simpr', LEg('0', '1'))], 'jca', ca3)], '3jca', CA)
    c1 = s1([c1a, w.inst('ef3c1')], 'syl', EQg('0', '1'))
    base = w.s([sb([lt01, w.s([c1], 'ex', '( %s -> ( %s -> %s ) )' % (B0, LEg('0', '1'), EQg('0', '1')))], 'jca', '( %s < %s /\\ ( %s -> %s ) )' % (Gj('0'), Gj('1'), LEg('0', '1'), EQg('0', '1')))], 'ex', '( %s -> %s )' % (A0, PS('1')))
    # step
    C0 = '( ( %s /\\ m e. NN ) /\\ %s )' % (A0, PS('m'))
    C1 = '( %s /\\ ( m + 1 ) <_ M )' % C0
    sc_ = St(w, C1)
    Lc = lambda st: lift(w, st, C1)
    mnn = Lc(w.s([], 'simplr', '( %s -> m e. NN )' % C0))
    psm = Lc(w.s([], 'simpr', '( %s -> %s )' % (C0, PS('m'))))
    m1 = sc_([], 'simpr', '( m + 1 ) <_ M')
    mr = sc_([mnn], 'nnred', 'm e. RR'); Mr = sc_([Lc(mn)], 'nnred', 'M e. RR')
    mlt = lin8(w, C1, [m1], 'm < M', {'m': mr, 'M': Mr})
    mle = lin8(w, C1, [m1], 'm <_ M', {'m': mr, 'M': Mr})
    mo = sc_([sc_([sc_([mnn], 'nnnn0d', 'm e. NN0'), Lc(mn), mlt], '3jca', '( m e. NN0 /\\ M e. NN /\\ m < M )'), w.s([], 'elfzo0', '( m e. %s <-> ( m e. NN0 /\\ M e. NN /\\ m < M ) )' % IFO)], 'sylibr', 'm e. %s' % IFO)
    mz = sc_([mo, w.inst('elfzofz')], 'syl', 'm e. %s' % IFZ)
    m1z = sc_([mo, w.inst('fzofzp1')], 'syl', '( m + 1 ) e. %s' % IFZ)
    ih = sc_([mle, psm], 'mpd', '( %s < %s /\\ ( %s -> %s ) )' % (Gj('0'), Gj('m'), LEg('0', 'm'), EQg('0', 'm')))
    lt0m, ihi = conj_split(w, C1, ih)
    gm = inst_all(w, C1, Lc(gp), 'j', 'm', mo, GAP('j'))
    ltm, gapm = conj_split(w, C1, gm)
    g0r, gmr, gm1r = gr(C1, '0', Lc(z0)), gr(C1, 'm', mz), gr(C1, '( m + 1 )', m1z)
    lvg = {Gj('0'): g0r, Gj('m'): gmr, Gj('( m + 1 )'): gm1r}
    lt0m1 = lin8(w, C1, [lt0m, ltm], '%s < %s' % (Gj('0'), Gj('( m + 1 )')), lvg)
    C2 = '( %s /\\ %s )' % (C1, LEg('0', '( m + 1 )'))
    s2 = St(w, C2)
    L2 = lambda st: lift(w, st, C2)
    lebig = s2([], 'simpr', LEg('0', '( m + 1 )'))
    IM = '( %s [,] %s )' % (Gj('0'), Gj('m'))
    C3 = '( %s /\\ y e. %s )' % (C2, IM)
    s3 = St(w, C3)
    L3 = lambda st: lift(w, st, C3)
    yin = s3([], 'simpr', 'y e. %s' % IM)
    e4 = s3([L3(L2(g0r)), L3(L2(gmr)), w.inst('elicc2')], 'syl2anc', '( y e. %s <-> ( y e. RR /\\ %s <_ y /\\ y <_ %s ) )' % (IM, Gj('0'), Gj('m')))
    yr, y0, ym = conj_split(w, C3, s3([yin, e4], 'mpbid', '( y e. RR /\\ %s <_ y /\\ y <_ %s )' % (Gj('0'), Gj('m'))))
    yv = icc_mem(w, C3, 'y', Gj('0'), Gj('( m + 1 )'), yr, L3(L2(g0r)), L3(L2(gm1r)), y0, lin8(w, C3, [ym, L3(L2(ltm))], 'y <_ %s' % Gj('( m + 1 )'), {'y': yr, Gj('m'): L3(L2(gmr)), Gj('( m + 1 )'): L3(L2(gm1r))}))
    BY = '( F ` ( S + ( _i x. y ) ) ) =/= 0'
    lesm = ralcb(C2, s2([inst_all(w, C3, L3(lebig), 't', 'y', yv, '( F ` ( S + ( _i x. t ) ) ) =/= 0')], 'ralrimiva', 'A. y e. %s %s' % (IM, BY)), 't', IM, BY)
    ihe = s2([lesm, L2(ihi)], 'mpd', EQg('0', 'm'))
    SA_ = tsub(ante_of(S['ef3cstep'])[0], {'V': Gj('0'), 'L': Gj('m'), 'H': Gj('( m + 1 )')})
    sa1, sa2, sa3 = top_and(SA_)
    lvs = s2([lnat(C2, '0', L2(Lc(z0))), lnat(C2, 'm', L2(mz)), lnat(C2, '( m + 1 )', L2(m1z))], '3jca', top_and(sa3)[0])
    st_a = s2([L2(Lc(h1)), s2([s2([L2(g0r), L2(gmr), L2(gm1r)], '3jca', top_and(sa2)[0]), s2([L2(lt0m), L2(ltm), L2(gapm)], '3jca', top_and(sa2)[1])], 'jca', sa2),
               s2([lvs, lebig, ihe], '3jca', sa3)], '3jca', SA_)
    stp = s2([st_a, w.inst('ef3cstep')], 'syl', EQg('0', '( m + 1 )'))
    c1b = sc_([lt0m1, w.s([stp], 'ex', '( %s -> ( %s -> %s ) )' % (C1, LEg('0', '( m + 1 )'), EQg('0', '( m + 1 )')))], 'jca', '( %s < %s /\\ ( %s -> %s ) )' % (Gj('0'), Gj('( m + 1 )'), LEg('0', '( m + 1 )'), EQg('0', '( m + 1 )')))
    step = w.s([c1b], 'ex', '( %s -> %s )' % (C0, PS('( m + 1 )')))
    # congruences
    def cg(val):
        eq, _ = w.wcongr(PS('n'), {'n': val}, 'n = %s' % val, {'n': w.s([], 'id', '( n = %s -> n = %s )' % (val, val))})
        return eq
    ind = w.s([cg('1'), cg('m'), cg('( m + 1 )'), cg('M'), base, step], 'nnindd', '( ( %s /\\ M e. NN ) -> %s )' % (A0, PS('M')))
    psM = s([s([], 'id', A0) if False else w.s([], 'id', '( %s -> %s )' % (A0, A0)), mn, ind], 'syl2anc', PS('M'))
    Mr0 = s([mn], 'nnred', 'M e. RR')
    fin = s([s([lin8(w, A0, [], 'M <_ M', {'M': Mr0}), psM], 'mpd', '( %s < %s /\\ ( %s -> %s ) )' % (Gj('0'), Gj('M'), LEg('0', 'M'), EQg('0', 'M'))), w.inst('simpr')], 'syl', '( %s -> %s )' % (LEg('0', 'M'), EQg('0', 'M')))
    w.qed([le, fin], 'mpd', S['ef3chain'])
    return run8(w)


if __name__ == '__main__':
    gen_cs()
    gen_c1()
    gen_zrm()
    gen_zsp()
    gen_zsum()
    gen_cstep()
    gen_chain()
