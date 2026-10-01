"""ZL3b D3: additivity of the rectangle integral over the unit rectangles R_N = sum of residues.
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_d3.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of, twopi, TP, MP
from zl3b_d2 import cst, reim_cp, cpcl

only = sys.argv[1:]
S = STATEMENTS


def pteq(w, A, x, y, xe, ye, X, Y):
    """from xe: ( A -> x = X ), ye: ( A -> y = Y ): ( A -> ( x + ( _i x. y ) ) = ( X + ( _i x. Y ) ) )"""
    return D(w, A, 'oveq12d', [xe, D(w, A, 'oveq2d', [ye], '( _i x. %s ) = ( _i x. %s )' % (y, Y))], '%s = %s' % (CP(x, y), CP(X, Y)))


def lieq(w, A, F, P, Q, pe, qe, P2, Q2):
    """( A -> LI(F,P,Q) = LI(F,P2,Q2) ) from pe: P = P2, qe: Q = Q2 (None: unchanged)"""
    cur = P
    if pe is None and qe is None:
        return None
    if pe is None:
        pe = D(w, A, 'eqidd', [], '%s = %s' % (P, P)); P2 = P
    if qe is None:
        qe = D(w, A, 'eqidd', [], '%s = %s' % (Q, Q)); Q2 = Q
    op = D(w, A, 'opeq12d', [pe, qe], '<. %s , %s >. = <. %s , %s >.' % (P, Q, P2, Q2))
    return D(w, A, 'oveq2d', [op], '%s = %s' % (LI(F, P, Q), LI(F, P2, Q2)))


# ---------------------------------------------------------------- zl3rval
if __name__ == '__main__' and (not only or 'zl3rval' in only):
    w = W('zl3rval', 'The rectangle integral with corners ` X + i U ` and ` Y + i W ` as the sum of its four edge integrals.')
    ph, concl = ante_of(S['zl3rval'])
    xy = w.s([], 'simp1', '( %s -> ( X e. RR /\\ Y e. RR ) )' % ph)
    uw = w.s([], 'simp2', '( %s -> ( U e. RR /\\ W e. RR ) )' % ph)
    fv = w.s([], 'simp3', '( %s -> F e. V )' % ph)
    xr = w.s([xy, w.inst('simpl')], 'syl', '( %s -> X e. RR )' % ph); yr = w.s([xy, w.inst('simpr')], 'syl', '( %s -> Y e. RR )' % ph)
    ur = w.s([uw, w.inst('simpl')], 'syl', '( %s -> U e. RR )' % ph); wr = w.s([uw, w.inst('simpr')], 'syl', '( %s -> W e. RR )' % ph)
    A_ = CP('X', 'U'); B_ = CP('Y', 'W')
    ac = cpcl(w, ph, 'X', 'U', xr, ur); bc = cpcl(w, ph, 'Y', 'W', yr, wr)
    reA, imA = reim_cp(w, ph, 'X', 'U', xr, ur); reB, imB = reim_cp(w, ph, 'Y', 'W', yr, wr)
    P10r = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (B_, A_); P01r = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (A_, B_)
    P10 = CP('Y', 'U'); P01 = CP('X', 'W')
    rv = w.s([fv, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (
        ph, RI('F', A_, B_), LI('F', A_, P10r), LI('F', P10r, B_), LI('F', B_, P01r), LI('F', P01r, A_)))
    e10 = pteq(w, ph, '( Re ` %s )' % B_, '( Im ` %s )' % A_, reB, imA, 'Y', 'U')
    e01 = pteq(w, ph, '( Re ` %s )' % A_, '( Im ` %s )' % B_, reA, imB, 'X', 'W')
    l1 = lieq(w, ph, 'F', A_, P10r, None, e10, A_, P10)
    l2 = lieq(w, ph, 'F', P10r, B_, e10, None, P10, B_)
    l3 = lieq(w, ph, 'F', B_, P01r, None, e01, B_, P01)
    l4 = lieq(w, ph, 'F', P01r, A_, e01, None, P01, A_)
    s12 = D(w, ph, 'oveq12d', [l1, l2], '( %s + %s ) = ( %s + %s )' % (LI('F', A_, P10r), LI('F', P10r, B_), LI('F', A_, P10), LI('F', P10, B_)))
    s34 = D(w, ph, 'oveq12d', [l3, l4], '( %s + %s ) = ( %s + %s )' % (LI('F', B_, P01r), LI('F', P01r, A_), LI('F', B_, P01), LI('F', P01, A_)))
    s = D(w, ph, 'oveq12d', [s12, s34], '( ( %s + %s ) + ( %s + %s ) ) = ( ( %s + %s ) + ( %s + %s ) )' % (
        LI('F', A_, P10r), LI('F', P10r, B_), LI('F', B_, P01r), LI('F', P01r, A_), LI('F', A_, P10), LI('F', P10, B_), LI('F', B_, P01), LI('F', P01, A_)))
    w.qed([rv, s], 'eqtrd', S['zl3rval'])
    go(w, only)


# ---------------------------------------------------------------- zl3vsp
from c0b_lib import CxSum, cancel, rn


def ptsplit(w, A, x, y1, y2, yc, xr, y1r, y2r, ycr, lo, hi, up):
    """P = x + i y1, Q = x + i y2, M = x + i yc strictly between (lo, hi: the two strict inequalities
    y1 < yc, yc < y2 if up; y2 < yc, yc < y1 otherwise).  Returns (S, s01, meq):
    ( A -> S e. ( 0 [,] 1 ) ), ( A -> M = ( P + ( S x. ( Q - P ) ) ) )"""
    if up:
        NUM = '( %s - %s )' % (yc, y1); DEN = '( %s - %s )' % (y2, y1)
        nr = D(w, A, 'resubcld', [ycr, y1r], '%s e. RR' % NUM); dr = D(w, A, 'resubcld', [y2r, y1r], '%s e. RR' % DEN)
        dpos = D(w, A, 'mpbid', [D(w, A, 'lttrd', [y1r, ycr, y2r, lo, hi], '%s < %s' % (y1, y2)), D(w, A, 'posdifd', [y1r, y2r], '( %s < %s <-> 0 < %s )' % (y1, y2, DEN))], '0 < %s' % DEN)
        n0 = D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), nr, D(w, A, 'mpbid', [lo, D(w, A, 'posdifd', [y1r, ycr], '( %s < %s <-> 0 < %s )' % (y1, yc, NUM))], '0 < %s' % NUM)], '0 <_ %s' % NUM)
        nle = D(w, A, 'ltled', [nr, dr, D(w, A, 'ltsub1dd', [ycr, y2r, y1r, hi], '%s < %s' % (NUM, DEN))], '%s <_ %s' % (NUM, DEN))
    else:
        NUM = '( %s - %s )' % (y1, yc); DEN = '( %s - %s )' % (y1, y2)
        nr = D(w, A, 'resubcld', [y1r, ycr], '%s e. RR' % NUM); dr = D(w, A, 'resubcld', [y1r, y2r], '%s e. RR' % DEN)
        dpos = D(w, A, 'mpbid', [D(w, A, 'lttrd', [y2r, ycr, y1r, lo, hi], '%s < %s' % (y2, y1)), D(w, A, 'posdifd', [y2r, y1r], '( %s < %s <-> 0 < %s )' % (y2, y1, DEN))], '0 < %s' % DEN)
        n0 = D(w, A, 'ltled', [cst(w, A, '0re', '0 e. RR'), nr, D(w, A, 'mpbid', [hi, D(w, A, 'posdifd', [ycr, y1r], '( %s < %s <-> 0 < %s )' % (yc, y1, NUM))], '0 < %s' % NUM)], '0 <_ %s' % NUM)
        nle = D(w, A, 'ltled', [nr, dr, D(w, A, 'ltsub2dd', [y2r, ycr, y1r, lo], '%s < %s' % (NUM, DEN))], '%s <_ %s' % (NUM, DEN))
    drp = D(w, A, 'elrpd', [dr, dpos], '%s e. RR+' % DEN)
    Sx = '( %s / %s )' % (NUM, DEN)
    sr = D(w, A, 'rerpdivcld', [nr, drp], '%s e. RR' % Sx)
    sg = D(w, A, 'divge0d', [nr, drp, n0], '0 <_ %s' % Sx)
    s1 = D(w, A, 'mpbird', [nle, w.s([nr, drp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> %s <_ %s ) )' % (A, Sx, NUM, DEN))], '%s <_ 1' % Sx)
    e01 = w.s([cst(w, A, '0re', '0 e. RR'), cst(w, A, '1re', '1 e. RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) ) )' % (A, Sx, Sx, Sx, Sx))
    s01 = D(w, A, 'mpbird', [w.s([sr, sg, s1], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (A, Sx, Sx, Sx)), e01], '%s e. ( 0 [,] 1 )' % Sx)
    # S ( y2 - y1 ) = yc - y1
    Y21 = '( %s - %s )' % (y2, y1); YC1 = '( %s - %s )' % (yc, y1)
    sc = D(w, A, 'recnd', [sr], '%s e. CC' % Sx); ncx = D(w, A, 'recnd', [nr], '%s e. CC' % NUM); dcx = D(w, A, 'recnd', [dr], '%s e. CC' % DEN)
    dne = D(w, A, 'gt0ne0d', [dpos], '%s =/= 0' % DEN)
    dc1 = D(w, A, 'divcan1d', [ncx, dcx, dne], '( %s x. %s ) = %s' % (Sx, DEN, NUM))
    y1c = D(w, A, 'recnd', [y1r], '%s e. CC' % y1); y2c = D(w, A, 'recnd', [y2r], '%s e. CC' % y2); ycc = D(w, A, 'recnd', [ycr], '%s e. CC' % yc)
    if up:
        t = dc1   # DEN is Y21, NUM is YC1
    else:
        ng = D(w, A, 'negsubdi2d', [y1c, y2c], '-u %s = %s' % (DEN, Y21))
        t1 = D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [ng], '%s = -u %s' % (Y21, DEN))], '( %s x. %s ) = ( %s x. -u %s )' % (Sx, Y21, Sx, DEN))
        t2 = D(w, A, 'mulneg2d', [sc, dcx], '( %s x. -u %s ) = -u ( %s x. %s )' % (Sx, DEN, Sx, DEN))
        t3 = D(w, A, 'negeqd', [dc1], '-u ( %s x. %s ) = -u %s' % (Sx, DEN, NUM))
        t4 = D(w, A, 'negsubdi2d', [y1c, ycc], '-u %s = %s' % (NUM, YC1))
        t = D(w, A, 'eqtrd', [D(w, A, 'eqtrd', [D(w, A, 'eqtrd', [t1, t2], '( %s x. %s ) = -u ( %s x. %s )' % (Sx, Y21, Sx, DEN)), t3], '( %s x. %s ) = -u %s' % (Sx, Y21, NUM)), t4],
              '( %s x. %s ) = %s' % (Sx, Y21, YC1))
    ic = cst(w, A, 'ax-icn', '_i e. CC'); xc = D(w, A, 'recnd', [xr], '%s e. CC' % x)
    iy1 = D(w, A, 'mulcld', [ic, y1c], '( _i x. %s ) e. CC' % y1); iy2 = D(w, A, 'mulcld', [ic, y2c], '( _i x. %s ) e. CC' % y2)
    P = CP(x, y1); Q = CP(x, y2); M = CP(x, yc)
    q1 = D(w, A, 'pnpcand', [xc, iy2, iy1], '( %s - %s ) = ( ( _i x. %s ) - ( _i x. %s ) )' % (Q, P, y2, y1))
    q2 = D(w, A, 'subdid', [ic, y2c, y1c], '( _i x. %s ) = ( ( _i x. %s ) - ( _i x. %s ) )' % (Y21, y2, y1))
    q3 = D(w, A, 'eqtr4d', [q1, q2], '( %s - %s ) = ( _i x. %s )' % (Q, P, Y21))
    y21c = D(w, A, 'subcld', [y2c, y1c], '%s e. CC' % Y21)
    q4 = D(w, A, 'oveq2d', [q3], '( %s x. ( %s - %s ) ) = ( %s x. ( _i x. %s ) )' % (Sx, Q, P, Sx, Y21))
    q5 = D(w, A, 'mul12d', [sc, ic, y21c], '( %s x. ( _i x. %s ) ) = ( _i x. ( %s x. %s ) )' % (Sx, Y21, Sx, Y21))
    q6 = D(w, A, 'oveq2d', [t], '( _i x. ( %s x. %s ) ) = ( _i x. %s )' % (Sx, Y21, YC1))
    q7 = D(w, A, 'eqtrd', [D(w, A, 'eqtrd', [q4, q5], '( %s x. ( %s - %s ) ) = ( _i x. ( %s x. %s ) )' % (Sx, Q, P, Sx, Y21)), q6], '( %s x. ( %s - %s ) ) = ( _i x. %s )' % (Sx, Q, P, YC1))
    yc1c = D(w, A, 'subcld', [ycc, y1c], '%s e. CC' % YC1)
    iyc1 = D(w, A, 'mulcld', [ic, yc1c], '( _i x. %s ) e. CC' % YC1)
    r1 = D(w, A, 'oveq2d', [q7], '( %s + ( %s x. ( %s - %s ) ) ) = ( %s + ( _i x. %s ) )' % (P, Sx, Q, P, P, YC1))
    r2 = D(w, A, 'addassd', [xc, iy1, iyc1], '( %s + ( _i x. %s ) ) = ( %s + ( ( _i x. %s ) + ( _i x. %s ) ) )' % (P, YC1, x, y1, YC1))
    r3 = D(w, A, 'adddid', [ic, y1c, yc1c], '( _i x. ( %s + %s ) ) = ( ( _i x. %s ) + ( _i x. %s ) )' % (y1, YC1, y1, YC1))
    r4 = D(w, A, 'oveq2d', [D(w, A, 'pncan3d', [y1c, ycc], '( %s + %s ) = %s' % (y1, YC1, yc))], '( _i x. ( %s + %s ) ) = ( _i x. %s )' % (y1, YC1, yc))
    r5 = D(w, A, 'eqtr3d', [r3, r4], '( ( _i x. %s ) + ( _i x. %s ) ) = ( _i x. %s )' % (y1, YC1, yc))
    r6 = D(w, A, 'oveq2d', [r5], '( %s + ( ( _i x. %s ) + ( _i x. %s ) ) ) = %s' % (x, y1, YC1, M))
    meq = D(w, A, 'eqtrd', [D(w, A, 'eqtrd', [r1, r2], '( %s + ( %s x. ( %s - %s ) ) ) = ( %s + ( ( _i x. %s ) + ( _i x. %s ) ) )' % (P, Sx, Q, P, x, y1, YC1)), r6],
            '( %s + ( %s x. ( %s - %s ) ) ) = %s' % (P, Sx, Q, P, M))
    return Sx, s01, D(w, A, 'eqcomd', [meq], '%s = ( %s + ( %s x. ( %s - %s ) ) )' % (M, P, Sx, Q, P))


if __name__ == '__main__' and (not only or 'zl3vsp' in only):
    w = W('zl3vsp', 'A rectangle integral splits at a horizontal cut when the integrand is continuous on the three frames only.')
    ph, concl = ante_of(S['zl3vsp'])
    F1 = FRC('X', 'U', 'Y', 'W'); F2 = FRC('X', 'U', 'Y', 'C'); F3 = FRC('X', 'C', 'Y', 'W')
    L0 = '( ( ( X e. RR /\\ Y e. RR ) /\\ ( U e. RR /\\ W e. RR /\\ C e. RR ) /\\ ( U < C /\\ C < W ) ) )'[2:-2]
    L0 = '( ( X e. RR /\\ Y e. RR ) /\\ ( U e. RR /\\ W e. RR /\\ C e. RR ) /\\ ( U < C /\\ C < W ) )'
    R0 = '( F e. ( D -cn-> CC ) /\\ ( ( %s u. %s ) u. %s ) C_ D )' % (F1, F2, F3)
    assert ph == '( %s /\\ %s )' % (L0, R0)
    l0 = w.s([], 'simpl', '( %s -> %s )' % (ph, L0)); r0 = w.s([], 'simpr', '( %s -> %s )' % (ph, R0))
    xy = w.s([l0, w.inst('simp1')], 'syl', '( %s -> ( X e. RR /\\ Y e. RR ) )' % ph)
    uwc = w.s([l0, w.inst('simp2')], 'syl', '( %s -> ( U e. RR /\\ W e. RR /\\ C e. RR ) )' % ph)
    lts = w.s([l0, w.inst('simp3')], 'syl', '( %s -> ( U < C /\\ C < W ) )' % ph)
    xr = w.s([xy, w.inst('simpl')], 'syl', '( %s -> X e. RR )' % ph); yr = w.s([xy, w.inst('simpr')], 'syl', '( %s -> Y e. RR )' % ph)
    ur = w.s([uwc, w.inst('simp1')], 'syl', '( %s -> U e. RR )' % ph); wr = w.s([uwc, w.inst('simp2')], 'syl', '( %s -> W e. RR )' % ph)
    cr = w.s([uwc, w.inst('simp3')], 'syl', '( %s -> C e. RR )' % ph)
    uc = w.s([lts, w.inst('simpl')], 'syl', '( %s -> U < C )' % ph); cw = w.s([lts, w.inst('simpr')], 'syl', '( %s -> C < W )' % ph)
    fcn = w.s([r0, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % ph)
    fss = w.s([r0, w.inst('simpr')], 'syl', '( %s -> ( ( %s u. %s ) u. %s ) C_ D )' % (ph, F1, F2, F3))
    A_ = CP('X', 'U'); P10 = CP('Y', 'U'); B_ = CP('Y', 'W'); P01 = CP('X', 'W'); N0 = CP('X', 'C'); N1 = CP('Y', 'C')
    pc = {A_: cpcl(w, ph, 'X', 'U', xr, ur), P10: cpcl(w, ph, 'Y', 'U', yr, ur), B_: cpcl(w, ph, 'Y', 'W', yr, wr),
          P01: cpcl(w, ph, 'X', 'W', xr, wr), N0: cpcl(w, ph, 'X', 'C', xr, cr), N1: cpcl(w, ph, 'Y', 'C', yr, cr)}
    FR = {1: F1, 2: F2, 3: F3}
    EDG = {1: [(A_, P10), (P10, B_), (B_, P01), (P01, A_)], 2: [(A_, P10), (P10, N1), (N1, N0), (N0, A_)], 3: [(N0, N1), (N1, B_), (B_, P01), (P01, N0)]}
    ALL = '( ( %s u. %s ) u. %s )' % (F1, F2, F3)
    frss = {}
    frss[1] = w.s([w.s([], 'ssun1', '%s C_ ( %s u. %s )' % (F1, F1, F2)), w.s([], 'ssun1', '( %s u. %s ) C_ %s' % (F1, F2, ALL))], 'sstri', '%s C_ %s' % (F1, ALL))
    frss[2] = w.s([w.s([], 'ssun2', '%s C_ ( %s u. %s )' % (F2, F1, F2)), w.s([], 'ssun1', '( %s u. %s ) C_ %s' % (F1, F2, ALL))], 'sstri', '%s C_ %s' % (F2, ALL))
    frss[3] = w.s([], 'ssun2', '%s C_ %s' % (F3, ALL))
    def segss(fr, e):
        (P, Q) = EDG[fr][e]
        seg = '( %s cseg %s )' % (P, Q)
        e0, e1, e2, e3 = ['( %s cseg %s )' % pq for pq in EDG[fr]]
        L = '( %s u. %s )' % (e0, e1); R = '( %s u. %s )' % (e2, e3)
        if e < 2:
            a = w.s([], 'ssun1' if e == 0 else 'ssun2', '%s C_ %s' % (seg, L)); b = w.s([], 'ssun1', '%s C_ %s' % (L, FR[fr]))
        else:
            a = w.s([], 'ssun1' if e == 2 else 'ssun2', '%s C_ %s' % (seg, R)); b = w.s([], 'ssun2', '%s C_ %s' % (R, FR[fr]))
        c = w.s([w.s([a, b], 'sstri', '%s C_ %s' % (seg, FR[fr])), frss[fr]], 'sstri', '%s C_ %s' % (seg, ALL))
        return D(w, ph, 'sstrd', [w.s([c], 'a1i', '( %s -> %s C_ %s )' % (ph, seg, ALL)), fss], '%s C_ D' % seg)
    def phs(P, Q, ss):
        return D(w, ph, 'jca', [D(w, ph, 'jca', [pc[P], pc[Q]], '( %s e. CC /\\ %s e. CC )' % (P, Q)), D(w, ph, 'jca', [fcn, ss], '( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (P, Q))],
                 '( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (P, Q, P, Q))
    segs = {(A_, P10): (1, 0), (P10, N1): (2, 1), (N1, B_): (3, 1), (B_, P01): (1, 2), (P01, N0): (3, 3), (N0, A_): (2, 3), (N0, N1): (3, 0), (N1, N0): (2, 2),
            (P10, B_): (1, 1), (P01, A_): (1, 3)}
    PH = {k: phs(k[0], k[1], segss(*v)) for k, v in segs.items()}
    cc = {LI('F', P, Q): w.s([PH[(P, Q)], w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (ph, LI('F', P, Q))) for (P, Q) in segs}
    a = LI('F', A_, P10); k = LI('F', P10, N1); m = LI('F', N1, B_); c = LI('F', B_, P01); n = LI('F', P01, N0); o = LI('F', N0, A_)
    q = LI('F', N0, N1); pp = LI('F', N1, N0); b = LI('F', P10, B_); dd = LI('F', P01, A_)
    S1, s01, meq1 = ptsplit(w, ph, 'Y', 'U', 'W', 'C', yr, ur, wr, cr, uc, cw, True)
    sp1 = w.s([PH[(P10, B_)], s01, meq1, w.inst('lintsplit')], 'syl3anc', '( %s -> %s = ( %s + %s ) )' % (ph, b, k, m))
    S2, s02, meq2 = ptsplit(w, ph, 'X', 'W', 'U', 'C', xr, wr, ur, cr, uc, cw, False)
    sp2 = w.s([PH[(P01, A_)], s02, meq2, w.inst('lintsplit')], 'syl3anc', '( %s -> %s = ( %s + %s ) )' % (ph, dd, n, o))
    rev = w.s([PH[(N0, N1)], w.inst('lintrev')], 'syl', '( %s -> %s = -u %s )' % (ph, pp, q))
    fv = w.s([fcn, w.inst('elex')], 'syl', '( %s -> F e. _V )' % ph)
    def rval(x1, y1, x2, y2, x1r, y1r, x2r, y2r):
        h = w.s([D(w, ph, 'jca', [x1r, x2r], '( %s e. RR /\\ %s e. RR )' % (x1, x2)), D(w, ph, 'jca', [y1r, y2r], '( %s e. RR /\\ %s e. RR )' % (y1, y2)), fv], '3jca',
                '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( %s e. RR /\\ %s e. RR ) /\\ F e. _V ) )' % (ph, x1, x2, y1, y2))
        Aq, Bq = CP(x1, y1), CP(x2, y2); Pq, Qq = CP(x2, y1), CP(x1, y2)
        return w.s([h, w.inst('zl3rval')], 'syl', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (ph, RI('F', Aq, Bq), LI('F', Aq, Pq), LI('F', Pq, Bq), LI('F', Bq, Qq), LI('F', Qq, Aq)))
    lhs = rval('X', 'U', 'Y', 'W', xr, ur, yr, wr)
    r2 = rval('X', 'U', 'Y', 'C', xr, ur, yr, cr)
    r3 = rval('X', 'C', 'Y', 'W', xr, cr, yr, wr)
    key = {a: 0, k: 1, m: 2, c: 3, n: 4, o: 5, q: 6, pp: 7}
    cs = CxSum(w, ph, cc, key)
    l1 = D(w, ph, 'oveq2d', [sp1], '( %s + %s ) = ( %s + ( %s + %s ) )' % (a, b, a, k, m))
    l2 = D(w, ph, 'oveq1d', [sp2], '( %s + %s ) = ( %s + ( %s + %s ) )' % (c, dd, c, n, o)) if False else D(w, ph, 'oveq2d', [sp2], '( %s + %s ) = ( %s + ( %s + %s ) )' % (c, dd, c, n, o))
    TL0 = '( ( %s + %s ) + ( %s + %s ) )' % (a, b, c, dd)
    treeL = ('+', ('+', a, ('+', k, m)), ('+', c, ('+', n, o)))
    from c0b_lib import tree_text
    lsub = D(w, ph, 'oveq12d', [l1, l2], '%s = %s' % (TL0, tree_text(treeL)))
    nL, atL = cs.nf(treeL)
    lhs2 = D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [lhs, lsub], '%s = %s' % (RI('F', A_, B_), tree_text(treeL))), nL], '%s = %s' % (RI('F', A_, B_), rn(atL)))
    treeR = ('+', ('+', ('+', a, k), ('+', pp, o)), ('+', ('+', q, m), ('+', c, n)))
    sumst = D(w, ph, 'oveq12d', [r2, r3], '( %s + %s ) = %s' % (RI('F', A_, N1), RI('F', N0, B_), tree_text(treeR)))
    nR, atR = cs.nf(treeR)
    assert atR[-2:] == [q, pp], atR
    can = cancel(w, ph, cs, atR, q, pp, rev, cc)
    rhs2 = D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [sumst, nR], '( %s + %s ) = %s' % (RI('F', A_, N1), RI('F', N0, B_), rn(atR))), can],
             '( %s + %s ) = %s' % (RI('F', A_, N1), RI('F', N0, B_), rn(atR[:-2])))
    assert atR[:-2] == atL
    w.qed([lhs2, rhs2], 'eqtr4d', S['zl3vsp'])
    go(w, only)


# ---------------------------------------------------------------- zl3frd
def frame_eq(w, A, x1, y1, x2, y2, reA, imA, reB, imB):
    """( A -> FRAME(A,B) = FRC(x1,y1,x2,y2) ) for A = x1 + i y1, B = x2 + i y2"""
    A_, B_ = CP(x1, y1), CP(x2, y2)
    P10r = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (B_, A_); P01r = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (A_, B_)
    P10, P01 = CP(x2, y1), CP(x1, y2)
    e10 = pteq(w, A, '( Re ` %s )' % B_, '( Im ` %s )' % A_, reB, imA, x2, y1)
    e01 = pteq(w, A, '( Re ` %s )' % A_, '( Im ` %s )' % B_, reA, imB, x1, y2)
    ea = D(w, A, 'eqidd', [], '%s = %s' % (A_, A_)); eb = D(w, A, 'eqidd', [], '%s = %s' % (B_, B_))
    def sg(P, Q, pe, qe, P2, Q2):
        return D(w, A, 'oveq12d', [pe, qe], '( %s cseg %s ) = ( %s cseg %s )' % (P, Q, P2, Q2))
    s1 = sg(A_, P10r, ea, e10, A_, P10); s2 = sg(P10r, B_, e10, eb, P10, B_)
    s3 = sg(B_, P01r, eb, e01, B_, P01); s4 = sg(P01r, A_, e01, ea, P01, A_)
    u1 = D(w, A, 'uneq12d', [s1, s2], '( ( %s cseg %s ) u. ( %s cseg %s ) ) = ( ( %s cseg %s ) u. ( %s cseg %s ) )' % (A_, P10r, P10r, B_, A_, P10, P10, B_))
    u2 = D(w, A, 'uneq12d', [s3, s4], '( ( %s cseg %s ) u. ( %s cseg %s ) ) = ( ( %s cseg %s ) u. ( %s cseg %s ) )' % (B_, P01r, P01r, A_, B_, P01, P01, A_))
    return D(w, A, 'uneq12d', [u1, u2], '%s = %s' % (FRAME(A_, B_), FRC(x1, y1, x2, y2)))


if __name__ == '__main__' and (not only or 'zl3frd' in only):
    w = W('zl3frd', 'The frame of the rectangle ` [ -1 + i U , 1 + i W ] ` with non-integral ` U `, ` W ` avoids the zeros of ` e ^ ( 2 pi w ) - 1 `.')
    ph, concl = ante_of(S['zl3frd'])
    uw = w.s([], 'simp1', '( %s -> ( U e. RR /\\ W e. RR ) )' % ph)
    nz = w.s([], 'simp2', '( %s -> ( -. U e. ZZ /\\ -. W e. ZZ ) )' % ph)
    ule = w.s([], 'simp3', '( %s -> U <_ W )' % ph)
    ur = w.s([uw, w.inst('simpl')], 'syl', '( %s -> U e. RR )' % ph); wr = w.s([uw, w.inst('simpr')], 'syl', '( %s -> W e. RR )' % ph)
    unz = w.s([nz, w.inst('simpl')], 'syl', '( %s -> -. U e. ZZ )' % ph); wnz = w.s([nz, w.inst('simpr')], 'syl', '( %s -> -. W e. ZZ )' % ph)
    m1 = cst(w, ph, 'neg1rr', '-u 1 e. RR'); p1 = cst(w, ph, '1re', '1 e. RR')
    A_, B_ = CP('-u 1', 'U'), CP('1', 'W')
    ac = cpcl(w, ph, '-u 1', 'U', m1, ur); bc = cpcl(w, ph, '1', 'W', p1, wr)
    reA, imA = reim_cp(w, ph, '-u 1', 'U', m1, ur); reB, imB = reim_cp(w, ph, '1', 'W', p1, wr)
    l11 = D(w, ph, 'ltled', [m1, p1, D(w, ph, 'lttrd', [m1, cst(w, ph, '0re', '0 e. RR'), p1, cst(w, ph, 'neg1lt0', '-u 1 < 0'), cst(w, ph, '0lt1', '0 < 1')], '-u 1 < 1')], '-u 1 <_ 1')
    g1 = D(w, ph, '3brtr4d', [l11, reA, reB], '( Re ` %s ) <_ ( Re ` %s )' % (A_, B_))
    g2 = D(w, ph, '3brtr4d', [ule, imA, imB], '( Im ` %s ) <_ ( Im ` %s )' % (A_, B_))
    GEO = '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (A_, B_, A_, B_)
    abg = D(w, ph, 'jca', [D(w, ph, 'jca', [ac, bc], '( %s e. CC /\\ %s e. CC )' % (A_, B_)), D(w, ph, 'jca', [g1, g2], GEO)], '( ( %s e. CC /\\ %s e. CC ) /\\ %s )' % (A_, B_, GEO))
    FRm = FRAME(A_, B_); FRc = FRC('-u 1', 'U', '1', 'W')
    DJr = '( ( ( Re ` u ) = ( Re ` %s ) \\/ ( Re ` u ) = ( Re ` %s ) ) \\/ ( ( Im ` u ) = ( Im ` %s ) \\/ ( Im ` u ) = ( Im ` %s ) ) )' % (A_, B_, A_, B_)
    fre = w.s([abg, w.inst('crectfre')], 'syl', '( %s -> A. u e. %s %s )' % (ph, FRm, DJr))
    fru = w.s([abg, w.inst('crectfru')], 'syl', '( %s -> %s C_ ( %s crect %s ) )' % (ph, FRm, A_, B_))
    feq = frame_eq(w, ph, '-u 1', 'U', '1', 'W', reA, imA, reB, imB)
    A1 = '( %s /\\ u e. %s )' % (ph, FRc)
    uf = D(w, A1, 'eleqtrrd', [w.s([], 'simpr', '( %s -> u e. %s )' % (A1, FRc)), w.s([feq], 'adantr', '( %s -> %s = %s )' % (A1, FRm, FRc))], 'u e. %s' % FRm)
    dj0 = w.s([w.s([fre], 'adantr', '( %s -> A. u e. %s %s )' % (A1, FRm, DJr)), uf, w.inst('rsp')], 'sylc', '( %s -> %s )' % (A1, DJr))
    lift = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
    r1 = D(w, A1, 'eqeq2d', [lift(reA, '( Re ` %s ) = -u 1' % A_)], '( ( Re ` u ) = ( Re ` %s ) <-> ( Re ` u ) = -u 1 )' % A_)
    r2 = D(w, A1, 'eqeq2d', [lift(reB, '( Re ` %s ) = 1' % B_)], '( ( Re ` u ) = ( Re ` %s ) <-> ( Re ` u ) = 1 )' % B_)
    r3 = D(w, A1, 'eqeq2d', [lift(imA, '( Im ` %s ) = U' % A_)], '( ( Im ` u ) = ( Im ` %s ) <-> ( Im ` u ) = U )' % A_)
    r4 = D(w, A1, 'eqeq2d', [lift(imB, '( Im ` %s ) = W' % B_)], '( ( Im ` u ) = ( Im ` %s ) <-> ( Im ` u ) = W )' % B_)
    DJ = '( ( ( Re ` u ) = -u 1 \\/ ( Re ` u ) = 1 ) \\/ ( ( Im ` u ) = U \\/ ( Im ` u ) = W ) )'
    dj = D(w, A1, 'mpbid', [dj0, D(w, A1, 'orbi12d', [D(w, A1, 'orbi12d', [r1, r2], '( ( ( Re ` u ) = ( Re ` %s ) \\/ ( Re ` u ) = ( Re ` %s ) ) <-> ( ( Re ` u ) = -u 1 \\/ ( Re ` u ) = 1 ) )' % (A_, B_)),
                                                          D(w, A1, 'orbi12d', [r3, r4], '( ( ( Im ` u ) = ( Im ` %s ) \\/ ( Im ` u ) = ( Im ` %s ) ) <-> ( ( Im ` u ) = U \\/ ( Im ` u ) = W ) )' % (A_, B_))],
                                          '( %s <-> %s )' % (DJr, DJ))], DJ)
    G = '( ( Re ` u ) = 0 /\\ ( Im ` u ) e. ZZ )'
    def casere(val, ne0):
        B = '( %s /\\ ( Re ` u ) = %s )' % (A1, val)
        n1 = D(w, B, 'neneqd', [D(w, B, 'eqnetrd', [w.s([], 'simpr', '( %s -> ( Re ` u ) = %s )' % (B, val)), cst(w, B, ne0, '%s =/= 0' % val)], '( Re ` u ) =/= 0')], '-. ( Re ` u ) = 0')
        return D(w, B, 'intnanrd', [n1], '-. %s' % G)
    def caseim(val, vnz):
        B = '( %s /\\ ( Im ` u ) = %s )' % (A1, val)
        e = D(w, B, 'eleq1d', [w.s([], 'simpr', '( %s -> ( Im ` u ) = %s )' % (B, val))], '( ( Im ` u ) e. ZZ <-> %s e. ZZ )' % val)
        n1 = D(w, B, 'mtbird', [w.s([vnz], 'ad2antrr', '( %s -> -. %s e. ZZ )' % (B, val)), e], '-. ( Im ` u ) e. ZZ')
        return D(w, B, 'intnand', [n1], '-. %s' % G)
    c1 = casere('-u 1', 'neg1ne0'); c2 = casere('1', 'ax-1ne0')
    c3 = caseim('U', unz); c4 = caseim('W', wnz)
    j1 = w.s([c1, c2], 'jaodan', '( ( %s /\\ ( ( Re ` u ) = -u 1 \\/ ( Re ` u ) = 1 ) ) -> -. %s )' % (A1, G))
    j2 = w.s([c3, c4], 'jaodan', '( ( %s /\\ ( ( Im ` u ) = U \\/ ( Im ` u ) = W ) ) -> -. %s )' % (A1, G))
    j3 = w.s([j1, j2], 'jaodan', '( ( %s /\\ %s ) -> -. %s )' % (A1, DJ, G))
    ng = w.s([dj, j3], 'mpdan', '( %s -> -. %s )' % (A1, G))
    ucr = D(w, A1, 'sseldd', [lift(fru, '%s C_ ( %s crect %s )' % (FRm, A_, B_)), uf], 'u e. ( %s crect %s )' % (A_, B_))
    uc = D(w, A1, 'sseldd', [w.s([lift(D(w, ph, 'jca', [ac, bc], '( %s e. CC /\\ %s e. CC )' % (A_, B_)), '( %s e. CC /\\ %s e. CC )' % (A_, B_)), w.inst('crectss')], 'syl', '( %s -> ( %s crect %s ) C_ CC )' % (A1, A_, B_)), ucr], 'u e. CC')
    ez = w.s([uc, w.inst('zl3ez')], 'sylan', '( %s -> ( %s = 1 -> %s ) )' % (A1, E2('u'), G)) if False else None
    ez = D(w, A1, 'ex', [], 'x') if False else None
    B2 = '( %s /\\ %s = 1 )' % (A1, E2('u'))
    ezz = w.s([w.s([uc], 'adantr', '( %s -> u e. CC )' % B2), w.s([], 'simpr', '( %s -> %s = 1 )' % (B2, E2('u'))), w.inst('zl3ez')], 'syl2anc', '( %s -> %s )' % (B2, G))
    ez = w.s([ezz], 'ex', '( %s -> ( %s = 1 -> %s ) )' % (A1, E2('u'), G))
    ne1 = D(w, A1, 'neqned', [D(w, A1, 'mtod', [ng, ez], '-. %s = 1' % E2('u'))], '%s =/= 1' % E2('u'))
    vsub = w.s([w.s([w.s([w.s([], 'id', '( v = u -> v = u )')], 'oveq2d', '( v = u -> ( %s x. v ) = ( %s x. u ) )' % (TP, TP))], 'fveq2d', '( v = u -> %s = %s )' % (E2('v'), E2('u')))],
               'neeq1d', '( v = u -> ( %s =/= 1 <-> %s =/= 1 ) )' % (E2('v'), E2('u')))
    elr = w.s([vsub], 'elrab', '( u e. %s <-> ( u e. CC /\\ %s =/= 1 ) )' % (D0, E2('u')))
    ud0 = w.s([D(w, A1, 'jca', [uc, ne1], '( u e. CC /\\ %s =/= 1 )' % E2('u')), elr], 'sylibr', '( %s -> u e. %s )' % (A1, D0))
    w.qed([w.s([ud0], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (ph, FRc, D0))], 'ssrdv', S['zl3frd'])
    go(w, only)


# ---------------------------------------------------------------- zl3fkcn
if __name__ == '__main__' and (not only or 'zl3fkcn' in only):
    w = W('zl3fkcn', '` H ( w ) / ( e ^ ( 2 pi w ) - 1 ) ` is continuous where the denominator does not vanish.')
    ph, concl = ante_of(S['zl3fkcn'])
    hcn0 = w.s([], 'simpl', '( %s -> H e. ( CC -cn-> CC ) )' % ph)
    d0c = cst(w, ph, 'ssrab2', '%s C_ CC' % D0)
    idc = w.s([d0c, cst(w, ph, 'ssid', 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( %s -> ( w e. %s |-> w ) e. ( %s -cn-> CC ) )' % (ph, D0, D0))
    hcn = w.s([hcn0, idc], 'cncfmpt1f', '( %s -> ( w e. %s |-> ( H ` w ) ) e. ( %s -cn-> CC ) )' % (ph, D0, D0))
    efc = w.s([cst(w, ph, 'zl3dve', S['zl3dve']), w.inst('simpl')], 'syl', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, EF))
    ccc = cst(w, ph, 'ssid', 'CC C_ CC')
    tpc = w.s([twopi(w, ph)[0], d0c, ccc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( w e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (ph, D0, TP, D0))
    lin_ = w.s([tpc, idc], 'mulcncf', '( %s -> ( w e. %s |-> ( %s x. w ) ) e. ( %s -cn-> CC ) )' % (ph, D0, TP, D0))
    ex_ = w.s([cst(w, ph, 'efcn', 'exp e. ( CC -cn-> CC )'), lin_], 'cncfmpt1f', '( %s -> ( w e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (ph, D0, E2('w'), D0))
    onec = w.s([cst(w, ph, 'ax-1cn', '1 e. CC'), d0c, ccc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( w e. %s |-> 1 ) e. ( %s -cn-> CC ) )' % (ph, D0, D0))
    ecn2 = w.s([ex_, onec], 'subcncf', '( %s -> ( w e. %s |-> ( %s - 1 ) ) e. ( %s -cn-> CC ) )' % (ph, D0, E2('w'), D0))
    A1 = '( %s /\\ w e. %s )' % (ph, D0)
    wd = w.s([], 'simpr', '( %s -> w e. %s )' % (A1, D0))
    vsub = w.s([w.s([w.s([w.s([], 'id', '( v = w -> v = w )')], 'oveq2d', '( v = w -> ( %s x. v ) = ( %s x. w ) )' % (TP, TP))], 'fveq2d', '( v = w -> %s = %s )' % (E2('v'), E2('w')))],
               'neeq1d', '( v = w -> ( %s =/= 1 <-> %s =/= 1 ) )' % (E2('v'), E2('w')))
    elr = w.s([vsub], 'elrab', '( w e. %s <-> ( w e. CC /\\ %s =/= 1 ) )' % (D0, E2('w')))
    we = w.s([wd, elr], 'sylib', '( %s -> ( w e. CC /\\ %s =/= 1 ) )' % (A1, E2('w')))
    wc = w.s([we, w.inst('simpl')], 'syl', '( %s -> w e. CC )' % A1)
    wn = w.s([we, w.inst('simpr')], 'syl', '( %s -> %s =/= 1 )' % (A1, E2('w')))
    tc, tn = twopi(w, A1)
    ewc = w.s([D(w, A1, 'mulcld', [tc, wc], '( %s x. w ) e. CC' % TP), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A1, E2('w')))
    one = cst(w, A1, 'ax-1cn', '1 e. CC')
    vc = D(w, A1, 'subcld', [ewc, one], '( %s - 1 ) e. CC' % E2('w'))
    vn = D(w, A1, 'subne0d', [ewc, one, wn], '( %s - 1 ) =/= 0' % E2('w'))
    vin = w.s([D(w, A1, 'jca', [vc, vn], '( ( %s - 1 ) e. CC /\\ ( %s - 1 ) =/= 0 )' % (E2('w'), E2('w'))),
               w.s([], 'eldifsn', '( ( %s - 1 ) e. ( CC \\ { 0 } ) <-> ( ( %s - 1 ) e. CC /\\ ( %s - 1 ) =/= 0 ) )' % (E2('w'), E2('w'), E2('w')))], 'sylibr',
              '( %s -> ( %s - 1 ) e. ( CC \\ { 0 } ) )' % (A1, E2('w')))
    ff = w.s([vin, w.s([], 'eqid', '( w e. %s |-> ( %s - 1 ) ) = ( w e. %s |-> ( %s - 1 ) )' % (D0, E2('w'), D0, E2('w')))], 'fmptd',
             '( %s -> ( w e. %s |-> ( %s - 1 ) ) : %s --> ( CC \\ { 0 } ) )' % (ph, D0, E2('w'), D0))
    cd = w.s([cst(w, ph, 'difss', '( CC \\ { 0 } ) C_ CC'), ecn2, w.inst('cncfcdm')], 'syl2anc',
             '( %s -> ( ( w e. %s |-> ( %s - 1 ) ) e. ( %s -cn-> ( CC \\ { 0 } ) ) <-> ( w e. %s |-> ( %s - 1 ) ) : %s --> ( CC \\ { 0 } ) ) )' % (ph, D0, E2('w'), D0, D0, E2('w'), D0))
    ecn3 = D(w, ph, 'mpbird', [ff, cd], '( w e. %s |-> ( %s - 1 ) ) e. ( %s -cn-> ( CC \\ { 0 } ) )' % (D0, E2('w'), D0))
    w.qed([hcn, ecn3], 'divcncf', S['zl3fkcn'])
    go(w, only)


# ---------------------------------------------------------------- zl3rsum
def SUMH(lo, hi):
    return 'sum_ n e. ( %s ... %s ) ( H ` ( _i x. n ) )' % (lo, hi)


def EQK(T):
    A_, B_ = RN(T)
    return '%s = ( _i x. %s )' % (RI(FK, A_, B_), SUMH('-u %s' % T, T))


if __name__ == '__main__' and (not only or 'zl3rsum' in only):
    w = W('zl3rsum', 'The rectangle integral of ` H ( w ) / ( e ^ ( 2 pi w ) - 1 ) ` over ` R_N ` is ` i ` times the sum of ` H ( i n ) ` over ` | n | <_ N ` (residue sum).')
    PK = lambda T: '( %s -> %s )' % (HENT, EQK(T))
    def subst(T):
        E = 'k = %s' % T
        e = w.s([], 'id', '( %s -> %s )' % (E, E))
        a = D(w, E, 'oveq1d', [e], '( k + ( 1 / 2 ) ) = ( %s + ( 1 / 2 ) )' % T)
        na = D(w, E, 'negeqd', [a], '-u ( k + ( 1 / 2 ) ) = -u ( %s + ( 1 / 2 ) )' % T)
        p1 = pteq(w, E, '-u 1', '-u ( k + ( 1 / 2 ) )', D(w, E, 'eqidd', [], '-u 1 = -u 1'), na, '-u 1', '-u ( %s + ( 1 / 2 ) )' % T)
        p2 = pteq(w, E, '1', '( k + ( 1 / 2 ) )', D(w, E, 'eqidd', [], '1 = 1'), a, '1', '( %s + ( 1 / 2 ) )' % T)
        A0_, B0_ = RN('k'); A1_, B1_ = RN(T)
        r = D(w, E, 'oveq2d', [D(w, E, 'opeq12d', [p1, p2], '<. %s , %s >. = <. %s , %s >.' % (A0_, B0_, A1_, B1_))], '%s = %s' % (RI(FK, A0_, B0_), RI(FK, A1_, B1_)))
        fz = D(w, E, 'oveq12d', [D(w, E, 'negeqd', [e], '-u k = -u %s' % T), e], '( -u k ... k ) = ( -u %s ... %s )' % (T, T))
        sm = D(w, E, 'oveq2d', [D(w, E, 'sumeq1d', [fz], '%s = %s' % (SUMH('-u k', 'k'), SUMH('-u %s' % T, T)))],
               '( _i x. %s ) = ( _i x. %s )' % (SUMH('-u k', 'k'), SUMH('-u %s' % T, T)))
        q = D(w, E, 'eqeq12d', [r, sm], '( %s <-> %s )' % (EQK('k'), EQK(T)))
        return D(w, E, 'imbi2d', [q], '( %s <-> %s )' % (PK('k'), PK(T)))
    h1 = subst('0'); h2 = subst('m'); h3 = subst('( m + 1 )'); h4 = subst('N')
    # ---- base
    B0 = HENT
    hent0 = w.s([], 'id', '( %s -> %s )' % (B0, HENT))
    z0 = cst(w, B0, '0z', '0 e. ZZ')
    rn0 = w.s([w.s([hent0, z0], 'jca', '( %s -> ( %s /\\ 0 e. ZZ ) )' % (B0, HENT)), w.inst('zl3resn')], 'syl', '( %s -> %s = ( _i x. ( H ` ( _i x. 0 ) ) ) )' % (B0, RI(FK, *QN('0'))))
    hc = cst(w, B0, 'halfcn', '( 1 / 2 ) e. CC')
    q1 = D(w, B0, 'negeqd', [D(w, B0, 'addlidd', [hc], '( 0 + ( 1 / 2 ) ) = ( 1 / 2 )')], '-u ( 0 + ( 1 / 2 ) ) = -u ( 1 / 2 )')
    q2 = D(w, B0, 'eqtrd', [q1, cst(w, B0, 'df-neg', '-u ( 1 / 2 ) = ( 0 - ( 1 / 2 ) )')], '-u ( 0 + ( 1 / 2 ) ) = ( 0 - ( 1 / 2 ) )')
    pA = pteq(w, B0, '-u 1', '-u ( 0 + ( 1 / 2 ) )', D(w, B0, 'eqidd', [], '-u 1 = -u 1'), q2, '-u 1', '( 0 - ( 1 / 2 ) )')
    rr = D(w, B0, 'oveq2d', [D(w, B0, 'opeq1d', [pA], '<. %s , %s >. = <. %s , %s >.' % (RN('0')[0], RN('0')[1], QN('0')[0], QN('0')[1]))], '%s = %s' % (RI(FK, *RN('0')), RI(FK, *QN('0'))))
    fz0 = D(w, B0, 'eqtrd', [D(w, B0, 'oveq1d', [cst(w, B0, 'neg0', '-u 0 = 0')], '( -u 0 ... 0 ) = ( 0 ... 0 )'), w.s([z0, w.inst('fzsn')], 'syl', '( %s -> ( 0 ... 0 ) = { 0 } )' % B0)],
            '( -u 0 ... 0 ) = { 0 }')
    hf0 = w.s([w.s([hent0, w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % B0), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % B0)
    i0c = D(w, B0, 'mulcld', [cst(w, B0, 'ax-icn', '_i e. CC'), cst(w, B0, '0cn', '0 e. CC')], '( _i x. 0 ) e. CC')
    h0c = D(w, B0, 'ffvelcdmd', [hf0, i0c], '( H ` ( _i x. 0 ) ) e. CC')
    ssn = w.s([cst(w, B0, 'c0ex', '0 e. _V'), h0c, w.s([w.s([w.s([], 'oveq2', '( n = 0 -> ( _i x. n ) = ( _i x. 0 ) )')], 'fveq2d', '( n = 0 -> ( H ` ( _i x. n ) ) = ( H ` ( _i x. 0 ) ) )')], 'sumsn',
                                                                            '( ( 0 e. _V /\\ ( H ` ( _i x. 0 ) ) e. CC ) -> sum_ n e. { 0 } ( H ` ( _i x. n ) ) = ( H ` ( _i x. 0 ) ) )')], 'syl2anc',
              '( %s -> sum_ n e. { 0 } ( H ` ( _i x. n ) ) = ( H ` ( _i x. 0 ) ) )' % B0)
    s0 = D(w, B0, 'eqtrd', [D(w, B0, 'sumeq1d', [fz0], '%s = sum_ n e. { 0 } ( H ` ( _i x. n ) )' % SUMH('-u 0', '0')), ssn], '%s = ( H ` ( _i x. 0 ) )' % SUMH('-u 0', '0'))
    base = D(w, B0, 'eqtr4d', [D(w, B0, 'eqtrd', [rr, rn0], '%s = ( _i x. ( H ` ( _i x. 0 ) ) )' % RI(FK, *RN('0'))), D(w, B0, 'oveq2d', [s0], '( _i x. %s ) = ( _i x. ( H ` ( _i x. 0 ) ) )' % SUMH('-u 0', '0'))],
             EQK('0'))
    # ---- step
    A = '( m e. NN0 /\\ %s )' % HENT
    m0 = w.s([], 'simpl', '( %s -> m e. NN0 )' % A); hent = w.s([], 'simpr', '( %s -> %s )' % (A, HENT))
    mz = D(w, A, 'nn0zd', [m0], 'm e. ZZ'); mr = D(w, A, 'nn0red', [m0], 'm e. RR'); mc = D(w, A, 'nn0cnd', [m0], 'm e. CC')
    hr = cst(w, A, 'halfre', '( 1 / 2 ) e. RR'); hcA = cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'); one = cst(w, A, 'ax-1cn', '1 e. CC')
    m1 = '( m + 1 )'
    m1z = D(w, A, 'peano2zd', [mz], '%s e. ZZ' % m1); m1r = D(w, A, 'zred', [m1z], '%s e. RR' % m1); m1c = D(w, A, 'zcnd', [m1z], '%s e. CC' % m1)
    a = '( m + ( 1 / 2 ) )'; a1 = '( %s + ( 1 / 2 ) )' % m1; na = '-u %s' % a; na1 = '-u %s' % a1
    ar = D(w, A, 'readdcld', [mr, hr], '%s e. RR' % a); a1r = D(w, A, 'readdcld', [m1r, hr], '%s e. RR' % a1)
    nar = D(w, A, 'renegcld', [ar], '%s e. RR' % na); na1r = D(w, A, 'renegcld', [a1r], '%s e. RR' % na1)
    hlf = cst(w, A, 'halfnz', '-. ( 1 / 2 ) e. ZZ')
    def nothalf(T, Tz, Tc):
        X = '( %s + ( 1 / 2 ) )' % T
        Bq = '( %s /\\ %s e. ZZ )' % (A, X)
        sb = w.s([w.s([], 'simpr', '( %s -> %s e. ZZ )' % (Bq, X)), w.s([Tz], 'adantr', '( %s -> %s e. ZZ )' % (Bq, T)), w.inst('zsubcl')], 'syl2anc', '( %s -> ( %s - %s ) e. ZZ )' % (Bq, X, T))
        pc = w.s([w.s([Tc], 'adantr', '( %s -> %s e. CC )' % (Bq, T)), cst(w, Bq, 'halfcn', '( 1 / 2 ) e. CC'), w.inst('pncan2')], 'syl2anc', '( %s -> ( %s - %s ) = ( 1 / 2 ) )' % (Bq, X, T))
        hz = D(w, Bq, 'eqeltrrd', [pc, sb], '( 1 / 2 ) e. ZZ')
        return D(w, A, 'mtod', [hlf, w.s([hz], 'ex', '( %s -> ( %s e. ZZ -> ( 1 / 2 ) e. ZZ ) )' % (A, X))], '-. %s e. ZZ' % X)
    def notneg(X, nx, xr):
        xc = D(w, A, 'recnd', [xr], '%s e. CC' % X)
        return D(w, A, 'mtbid', [nx, w.s([xc, w.inst('znegclb')], 'syl', '( %s -> ( %s e. ZZ <-> -u %s e. ZZ ) )' % (A, X, X))], '-. -u %s e. ZZ' % X)
    nza = nothalf('m', mz, mc); nza1 = nothalf(m1, m1z, m1c)
    nzna = notneg(a, nza, ar); nzna1 = notneg(a1, nza1, a1r)
    a0 = D(w, A, 'addgegt0d', [mr, hr, D(w, A, 'nn0ge0d', [m0], '0 <_ m'), cst(w, A, 'halfgt0', '0 < ( 1 / 2 )')], '0 < %s' % a)
    aa1 = D(w, A, 'ltadd1dd', [mr, m1r, hr, D(w, A, 'ltp1d', [mr], 'm < %s' % m1)], '%s < %s' % (a, a1))
    na1na = D(w, A, 'mpbid', [aa1, D(w, A, 'ltnegd', [ar, a1r], '( %s < %s <-> %s < %s )' % (a, a1, na1, na))], '%s < %s' % (na1, na))
    na0 = D(w, A, 'mpbid', [a0, D(w, A, 'lt0neg2d', [ar], '( 0 < %s <-> %s < 0 )' % (a, na))], '%s < 0' % na)
    naa = D(w, A, 'lttrd', [nar, cst(w, A, '0re', '0 e. RR'), ar, na0, a0], '%s < %s' % (na, a))
    naa1 = D(w, A, 'lttrd', [nar, ar, a1r, naa, aa1], '%s < %s' % (na, a1))
    na1a1 = D(w, A, 'lttrd', [na1r, nar, a1r, na1na, naa1], '%s < %s' % (na1, a1))
    rx = {a: ar, a1: a1r, na: nar, na1: na1r}; nzx = {a: nza, a1: nza1, na: nzna, na1: nzna1}
    fkcn = w.s([hent, w.inst('zl3fkcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A, FK, D0))
    def frd(U, W_, lt):
        h = w.s([D(w, A, 'jca', [rx[U], rx[W_]], '( %s e. RR /\\ %s e. RR )' % (U, W_)), D(w, A, 'jca', [nzx[U], nzx[W_]], '( -. %s e. ZZ /\\ -. %s e. ZZ )' % (U, W_)),
                 D(w, A, 'ltled', [rx[U], rx[W_], lt], '%s <_ %s' % (U, W_))], '3jca', '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( -. %s e. ZZ /\\ -. %s e. ZZ ) /\\ %s <_ %s ) )' % (A, U, W_, U, W_, U, W_))
        return w.s([h, w.inst('zl3frd')], 'syl', '( %s -> %s C_ %s )' % (A, FRC('-u 1', U, '1', W_), D0))
    m1rr = cst(w, A, 'neg1rr', '-u 1 e. RR'); p1rr = cst(w, A, '1re', '1 e. RR')
    def vsp(U, W_, C, uc, cw, uw):
        F1 = FRC('-u 1', U, '1', W_); F2 = FRC('-u 1', U, '1', C); F3 = FRC('-u 1', C, '1', W_)
        un = D(w, A, 'unssd', [D(w, A, 'unssd', [frd(U, W_, uw), frd(U, C, uc)], '( %s u. %s ) C_ %s' % (F1, F2, D0)), frd(C, W_, cw)], '( ( %s u. %s ) u. %s ) C_ %s' % (F1, F2, F3, D0))
        L0 = '( ( -u 1 e. RR /\\ 1 e. RR ) /\\ ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ ( %s < %s /\\ %s < %s ) )' % (U, W_, C, U, C, C, W_)
        l0 = w.s([D(w, A, 'jca', [m1rr, p1rr], '( -u 1 e. RR /\\ 1 e. RR )'), w.s([rx[U], rx[W_], rx[C]], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) )' % (A, U, W_, C)),
                  D(w, A, 'jca', [uc, cw], '( %s < %s /\\ %s < %s )' % (U, C, C, W_))], '3jca', '( %s -> %s )' % (A, L0))
        h = D(w, A, 'jca', [l0, D(w, A, 'jca', [fkcn, un], '( %s e. ( %s -cn-> CC ) /\\ ( ( %s u. %s ) u. %s ) C_ %s )' % (FK, D0, F1, F2, F3, D0))],
              '( %s /\\ ( %s e. ( %s -cn-> CC ) /\\ ( ( %s u. %s ) u. %s ) C_ %s ) )' % (L0, FK, D0, F1, F2, F3, D0))
        return w.s([h, w.inst('zl3vsp')], 'syl', '( %s -> %s = ( %s + %s ) )' % (A, RI(FK, CP('-u 1', U), CP('1', W_)), RI(FK, CP('-u 1', U), CP('1', C)), RI(FK, CP('-u 1', C), CP('1', W_))))
    sp1 = vsp(na1, a1, na, na1na, naa1, na1a1)
    sp2 = vsp(na, a1, a, naa, aa1, naa1)
    # the two unit rectangles
    X_ = '-u %s' % m1
    x_z = D(w, A, 'znegcld', [m1z], '%s e. ZZ' % X_); x_c = D(w, A, 'zcnd', [x_z], '%s e. CC' % X_)
    rb = w.s([D(w, A, 'jca', [hent, x_z], '( %s /\\ %s e. ZZ )' % (HENT, X_)), w.inst('zl3resn')], 'syl', '( %s -> %s = ( _i x. ( H ` ( _i x. %s ) ) ) )' % (A, RI(FK, *QN(X_)), X_))
    rt = w.s([D(w, A, 'jca', [hent, m1z], '( %s /\\ %s e. ZZ )' % (HENT, m1)), w.inst('zl3resn')], 'syl', '( %s -> %s = ( _i x. ( H ` ( _i x. %s ) ) ) )' % (A, RI(FK, *QN(m1)), m1))
    mh = D(w, A, 'eqtrd', [D(w, A, 'addsubassd', [mc, one, hcA], '( %s - ( 1 / 2 ) ) = ( m + ( 1 - ( 1 / 2 ) ) )' % m1), D(w, A, 'oveq2d', [cst(w, A, '1mhlfehlf', '( 1 - ( 1 / 2 ) ) = ( 1 / 2 )')], '( m + ( 1 - ( 1 / 2 ) ) ) = %s' % a)],
           '( %s - ( 1 / 2 ) ) = %s' % (m1, a))
    b1 = D(w, A, 'eqcomd', [w.s([m1c, hcA, w.inst('negdi2')], 'syl2anc', '( %s -> %s = ( %s - ( 1 / 2 ) ) )' % (A, na1, X_))], '( %s - ( 1 / 2 ) ) = %s' % (X_, na1))
    b2 = D(w, A, 'eqtr3d', [w.s([m1c, hcA, w.inst('negsubdi')], 'syl2anc', '( %s -> -u ( %s - ( 1 / 2 ) ) = ( %s + ( 1 / 2 ) ) )' % (A, m1, X_)), D(w, A, 'negeqd', [mh], '-u ( %s - ( 1 / 2 ) ) = %s' % (m1, na))],
           '( %s + ( 1 / 2 ) ) = %s' % (X_, na))
    ce = lambda st, l, r: D(w, A, 'oveq2d', [D(w, A, 'opeq12d', [st[0], st[1]], '<. %s , %s >. = <. %s , %s >.' % l)], '%s = %s' % r)
    e1 = D(w, A, 'eqidd', [], '-u 1 = -u 1'); e2 = D(w, A, 'eqidd', [], '1 = 1')
    qb = ce((pteq(w, A, '-u 1', '( %s - ( 1 / 2 ) )' % X_, e1, b1, '-u 1', na1), pteq(w, A, '1', '( %s + ( 1 / 2 ) )' % X_, e2, b2, '1', na)),
            (QN(X_)[0], QN(X_)[1], CP('-u 1', na1), CP('1', na)), (RI(FK, *QN(X_)), RI(FK, CP('-u 1', na1), CP('1', na))))
    qt = ce((pteq(w, A, '-u 1', '( %s - ( 1 / 2 ) )' % m1, e1, mh, '-u 1', a), D(w, A, 'eqidd', [], '%s = %s' % (QN(m1)[1], QN(m1)[1]))),
            (QN(m1)[0], QN(m1)[1], CP('-u 1', a), QN(m1)[1]), (RI(FK, *QN(m1)), RI(FK, CP('-u 1', a), QN(m1)[1])))
    ub = D(w, A, 'eqtr3d', [qb, rb], '%s = ( _i x. ( H ` ( _i x. %s ) ) )' % (RI(FK, CP('-u 1', na1), CP('1', na)), X_))
    ut = D(w, A, 'eqtr3d', [qt, rt], '%s = ( _i x. ( H ` ( _i x. %s ) ) )' % (RI(FK, CP('-u 1', a), QN(m1)[1]), m1))
    RB = RI(FK, CP('-u 1', na1), CP('1', na)); RM = RI(FK, *RN('m')); RT = RI(FK, CP('-u 1', a), CP('1', a1)); RU = RI(FK, CP('-u 1', na), CP('1', a1))
    IB = '( _i x. ( H ` ( _i x. %s ) ) )' % X_; IT = '( _i x. ( H ` ( _i x. %s ) ) )' % m1
    t1 = D(w, A, 'eqtrd', [sp1, D(w, A, 'oveq2d', [sp2], '( %s + %s ) = ( %s + ( %s + %s ) )' % (RB, RU, RB, RM, RT))], '%s = ( %s + ( %s + %s ) )' % (RI(FK, *RN(m1)), RB, RM, RT))
    t2 = D(w, A, 'eqtrd', [t1, D(w, A, 'oveq12d', [ub, D(w, A, 'oveq2d', [ut], '( %s + %s ) = ( %s + %s )' % (RM, RT, RM, IT))], '( %s + ( %s + %s ) ) = ( %s + ( %s + %s ) )' % (RB, RM, RT, IB, RM, IT))],
           '%s = ( %s + ( %s + %s ) )' % (RI(FK, *RN(m1)), IB, RM, IT))
    # the sum
    hf = w.s([w.s([hent, w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % A), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % A)
    def hval(lo, hi):
        Bq = '( %s /\\ n e. ( %s ... %s ) )' % (A, lo, hi)
        nz_ = w.s([w.s([], 'simpr', '( %s -> n e. ( %s ... %s ) )' % (Bq, lo, hi)), w.inst('elfzelz')], 'syl', '( %s -> n e. ZZ )' % Bq)
        inc = D(w, Bq, 'mulcld', [cst(w, Bq, 'ax-icn', '_i e. CC'), D(w, Bq, 'zcnd', [nz_], 'n e. CC')], '( _i x. n ) e. CC')
        return D(w, Bq, 'ffvelcdmd', [w.s([hf], 'adantr', '( %s -> H : CC --> CC )' % Bq), inc], '( H ` ( _i x. n ) ) e. CC')
    def hsub(T):
        return w.s([w.s([], 'oveq2', '( n = %s -> ( _i x. n ) = ( _i x. %s ) )' % (T, T))], 'fveq2d', '( n = %s -> ( H ` ( _i x. n ) ) = ( H ` ( _i x. %s ) ) )' % (T, T))
    def uz(lo, hi, lor, hir, loz, hiz, le):
        return w.s([w.s([loz, hiz, le], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (A, lo, hi, lo, hi)), w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (hi, lo, lo, hi, lo, hi))],
                   'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (A, hi, lo))
    x_r = D(w, A, 'zred', [x_z], '%s e. RR' % X_)
    lex = D(w, A, 'ltled', [x_r, m1r, D(w, A, 'lttrd', [x_r, cst(w, A, '0re', '0 e. RR'), m1r, D(w, A, 'mpbid', [D(w, A, 'nngt0d', [w.s([m0, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (A, m1))], '0 < %s' % m1), D(w, A, 'lt0neg2d', [m1r], '( 0 < %s <-> %s < 0 )' % (m1, X_))], '%s < 0' % X_),
                                                                    D(w, A, 'nngt0d', [w.s([m0, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (A, m1))], '0 < %s' % m1)], '%s < %s' % (X_, m1))], '%s <_ %s' % (X_, m1))
    f1 = w.s([uz(X_, m1, x_r, m1r, x_z, m1z, lex), hval(X_, m1), hsub(X_)], 'fsum1p', '( %s -> %s = ( ( H ` ( _i x. %s ) ) + %s ) )' % (A, SUMH(X_, m1), X_, SUMH('( %s + 1 )' % X_, m1)))
    nm = '-u m'
    xp1 = D(w, A, 'eqtrd', [D(w, A, 'oveq1d', [w.s([mc, one, w.inst('negdi2')], 'syl2anc', '( %s -> %s = ( %s - 1 ) )' % (A, X_, nm))], '( %s + 1 ) = ( ( %s - 1 ) + 1 )' % (X_, nm)),
                            w.s([D(w, A, 'negcld', [mc], '%s e. CC' % nm), one, w.inst('npcan')], 'syl2anc', '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (A, nm, nm))], '( %s + 1 ) = %s' % (X_, nm))
    f2 = D(w, A, 'sumeq1d', [D(w, A, 'oveq1d', [xp1], '( ( %s + 1 ) ... %s ) = ( %s ... %s )' % (X_, m1, nm, m1))], '%s = %s' % (SUMH('( %s + 1 )' % X_, m1), SUMH(nm, m1)))
    nmz = D(w, A, 'znegcld', [mz], '%s e. ZZ' % nm); nmr = D(w, A, 'zred', [nmz], '%s e. RR' % nm)
    lem = D(w, A, 'mpbid', [D(w, A, 'nn0ge0d', [m0], '0 <_ m'), D(w, A, 'ge0negd' if False else 'lenegcon1d', [mr, mr], 'x')], 'x') if False else None
    lem = D(w, A, 'letrd', [nmr, cst(w, A, '0re', '0 e. RR'), mr, D(w, A, 'mpbid', [D(w, A, 'nn0ge0d', [m0], '0 <_ m'), D(w, A, 'le0neg2d', [mr], '( 0 <_ m <-> %s <_ 0 )' % nm)], '%s <_ 0' % nm), D(w, A, 'nn0ge0d', [m0], '0 <_ m')],
            '%s <_ m' % nm)
    f3 = w.s([uz(nm, 'm', nmr, mr, nmz, mz, lem), hval(nm, m1), hsub(m1)], 'fsump1', '( %s -> %s = ( %s + ( H ` ( _i x. %s ) ) ) )' % (A, SUMH(nm, m1), SUMH(nm, 'm'), m1))
    HB = '( H ` ( _i x. %s ) )' % X_; HT = '( H ` ( _i x. %s ) )' % m1; SM = SUMH(nm, 'm')
    sall = D(w, A, 'eqtrd', [f1, D(w, A, 'oveq2d', [D(w, A, 'eqtrd', [f2, f3], '%s = ( %s + %s )' % (SUMH('( %s + 1 )' % X_, m1), SM, HT))],
                                                   '( %s + %s ) = ( %s + ( %s + %s ) )' % (HB, SUMH('( %s + 1 )' % X_, m1), HB, SM, HT))], '%s = ( %s + ( %s + %s ) )' % (SUMH(X_, m1), HB, SM, HT))
    # combine with the induction hypothesis
    A2 = '( %s /\\ %s )' % (A, EQK('m'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (A2, EQK('m')))
    lA = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
    t3 = D(w, A2, 'eqtrd', [lA(t2, '%s = ( %s + ( %s + %s ) )' % (RI(FK, *RN(m1)), IB, RM, IT)), D(w, A2, 'oveq2d', [D(w, A2, 'oveq1d', [ih], '( %s + %s ) = ( ( _i x. %s ) + %s )' % (RM, IT, SM, IT))],
                                                                                                  '( %s + ( %s + %s ) ) = ( %s + ( ( _i x. %s ) + %s ) )' % (IB, RM, IT, IB, SM, IT))],
           '%s = ( %s + ( ( _i x. %s ) + %s ) )' % (RI(FK, *RN(m1)), IB, SM, IT))
    ic2 = cst(w, A2, 'ax-icn', '_i e. CC')
    hbc = D(w, A2, 'ffvelcdmd', [lA(hf, 'H : CC --> CC'), D(w, A2, 'mulcld', [ic2, lA(x_c, '%s e. CC' % X_)], '( _i x. %s ) e. CC' % X_)], '%s e. CC' % HB)
    htc = D(w, A2, 'ffvelcdmd', [lA(hf, 'H : CC --> CC'), D(w, A2, 'mulcld', [ic2, lA(m1c, '%s e. CC' % m1)], '( _i x. %s ) e. CC' % m1)], '%s e. CC' % HT)
    smc = lA(w.s([w.s([], 'fzfid', '( %s -> ( %s ... m ) e. Fin )' % (A, nm)), hval(nm, 'm')], 'fsumcl', '( %s -> %s e. CC )' % (A, SM)), '%s e. CC' % SM)
    d1 = D(w, A2, 'adddid', [ic2, hbc, D(w, A2, 'addcld', [smc, htc], '( %s + %s ) e. CC' % (SM, HT))], '( _i x. ( %s + ( %s + %s ) ) ) = ( %s + ( _i x. ( %s + %s ) ) )' % (HB, SM, HT, IB, SM, HT))
    d2 = D(w, A2, 'adddid', [ic2, smc, htc], '( _i x. ( %s + %s ) ) = ( ( _i x. %s ) + %s )' % (SM, HT, SM, IT))
    d3 = D(w, A2, 'eqtrd', [d1, D(w, A2, 'oveq2d', [d2], '( %s + ( _i x. ( %s + %s ) ) ) = ( %s + ( ( _i x. %s ) + %s ) )' % (IB, SM, HT, IB, SM, IT))],
           '( _i x. ( %s + ( %s + %s ) ) ) = ( %s + ( ( _i x. %s ) + %s ) )' % (HB, SM, HT, IB, SM, IT))
    t4 = D(w, A2, 'eqtr4d', [t3, D(w, A2, 'eqtrd', [D(w, A2, 'oveq2d', [lA(sall, '%s = ( %s + ( %s + %s ) )' % (SUMH(X_, m1), HB, SM, HT))], '( _i x. %s ) = ( _i x. ( %s + ( %s + %s ) ) )' % (SUMH(X_, m1), HB, SM, HT)), d3],
                                                     '( _i x. %s ) = ( %s + ( ( _i x. %s ) + %s ) )' % (SUMH(X_, m1), IB, SM, IT))], EQK(m1))
    st1 = w.s([t4], 'ex', '( %s -> ( %s -> %s ) )' % (A, EQK('m'), EQK(m1)))
    st2 = w.s([st1], 'ex', '( m e. NN0 -> ( %s -> ( %s -> %s ) ) )' % (HENT, EQK('m'), EQK(m1)))
    st3 = w.s([st2], 'a2d', '( m e. NN0 -> ( %s -> %s ) )' % (PK('m'), PK(m1)))
    ind = w.s([h1, h2, h3, h4, base, st3], 'nn0ind', '( N e. NN0 -> %s )' % PK('N'))
    w.qed([ind], 'impcom', S['zl3rsum'])
    go(w, only)
