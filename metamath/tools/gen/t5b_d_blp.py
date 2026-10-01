"""T5b: the prologue of `bitlen` (TM/Prims.lean) --- ` push comma s ; moveNum x s ;
push comma x ; pushNum y 0 ; load ( flag := false , carry := false ) ` as a
~ tm2hseq chain over ~ tm2fpshn , ~ tm2fmvn , ~ tm2flg (~ tm2fblp ); the stacks
are ` K ` = x, ` J ` = s, ` I ` = y."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_b_iter import ldstep

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def pushstep(w, ph, phm, meq, al, el, kk, yk, dd, nss, A, E, K_, N, D):
    """tm2fpshn: push the constant Y on stack K_ at A to E, state class N"""
    D2 = UP(D, K_, CC(S1('Y'), '( %s ` %s )' % (D, K_)))
    return applylem(w, ph, 'tm2fpshn', ((phm, meq), (al, el, (kk, yk)), (dd, nss)),
                    TRI(CLN(A, N, D), CLN(E, N, D2), '1')), D2


def tm2fblp():
    lab = 'tm2fblp'
    tree, ph = TREE_BLP, cj(TREE_BLP)
    DK, DJ, DI = '( D ` K )', '( D ` J )', '( D ` I )'
    YDJ = CC(S1('Y'), DJ)
    RW = '( reverse ` W )'
    RWH = CC(RW, YDJ)
    assert RWH == RWYDJ
    w = W(lab, 'The prologue of ` bitlen ` (TM/Prims.lean): ` push comma s ; moveNum x s ; '
               'push comma x ; pushNum y 0 ; load ( flag := false , carry := false ) ` '
               'reverses the number on stack ` K ` (= x) onto the scratch stack ` J ` (= s) '
               'most-significant bit first, re-terminates ` K ` , pushes the terminated '
               'zero (one terminator, ` encodeNatGamma\' 0 = [] ` ) on the counter stack '
               '` I ` (= y) and loads the state from ` N ` into ` N\' ` , in ` ( # ` W ) + 5 ` '
               'steps.  Lean: ` bitlen_runs ` , stages 1-5.  Four instances of ~ tm2hseq '
               'over ~ tm2fpshn , ~ tm2fmvn , ~ tm2flg .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, a1, a2, e1, e2, el = [c[LAB(x)] for x in ('A', "A'", 'A"', "E'", 'E"', 'E')]
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)
    nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    ff, cc, pp, ll = c[RTY('F', 'K')], c[CTY('C')], c[PTY('P', 'J')], c[LTY('L')]
    bk, bj = c['B C_ %s' % GK], c['B C_ %s' % GJ]
    yk, yj, yi = c['Y e. %s' % GK], c['Y e. %s' % GJ], c['Y e. %s' % GI]
    ww, xx, dd = c[WRD('W', 'B')], c[WRD('X', GK)], c[STKD('D')]
    dke = c['( D ` K ) = %s' % WYX]
    nss, n2s = c[SSS('N')], c[SSS("N'")]
    hc, he, hld = c[HCMVN('N')], c[HEMVN('N')], c[HLD('N', "N'")]
    meqA, meqA1, meqA2, meqE1, meqE2 = [c[MEQ(a, s)] for a, s in (('A', ST_P1), ("A'", ST_PMV), ('A"', ST_P3), ("E'", ST_P4), ('E"', ST_P5))]
    # words
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    ysk, ysj, ysi = s1w(w, ph, yk, 'Y', GK), s1w(w, ph, yj, 'Y', GJ), s1w(w, ph, yi, 'Y', GI)
    yxw = ccatw(w, ph, ysk, xx, S1('Y'), 'X', GK)
    ydjw = ccatw(w, ph, ysj, djw, S1('Y'), DJ, GJ)
    rwb = revw(w, ph, ww, 'W', 'B')
    rwj = sswordd(w, ph, rwb, RW, 'B', GJ, bj)
    rwhw = ccatw(w, ph, rwj, ydjw, RW, YDJ, GJ)
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    ydiw = ccatw(w, ph, ysi, diw, S1('Y'), DI, GI)
    # ---- stage 1: push Y on J
    C0 = CLN('A', 'N', 'D')
    t1, D1 = pushstep(w, ph, phm, meqA, al, a1, jj, yj, dd, nss, 'A', "A'", 'J', 'N', 'D')
    assert D1 == UP('D', 'J', YDJ)
    d1cl = updcl(w, ph, 'D', 'J', YDJ, tv, dd, jj, ydjw)
    # ---- stage 2: moveNum K -> J
    PRE2 = UP(UP(D1, 'K', WYX), 'J', YDJ)
    D2 = UP(UP(D1, 'K', 'X'), 'J', RWH)
    t2 = applylem(w, ph, 'tm2fmvn',
                  ((((phm, meqA1), ((a1, a2), (kk, jj), nkj),
                     ((ff, cc, pp), ((bk, bj), (yk, xx, ydjw), d1cl), (nss, (hc, he)))), ww)),
                  TRI(CLN("A'", 'N', PRE2), CLN('A"', 'N', D2), '( ( # ` W ) + 1 )'))
    ydjv = elv(w, ph, ydjw, YDJ)
    d1k = updnv(w, ph, 'D', 'J', YDJ, 'K', tv, dd, jj, ydjv, kk, nkj)
    d1k2 = w.s([d1k, dke], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, WYX))
    e4 = upidv(w, ph, D1, 'K', WYX, d1k2, tv, d1cl, kk)
    d1j = updkv(w, ph, 'D', 'J', YDJ, tv, dd, jj, ydjv)
    f4 = upidv(w, ph, D1, 'J', YDJ, d1j, tv, d1cl, jj)
    g1, mid = w.rewrite(PRE2, {UP(D1, 'K', WYX): (D1, e4)}, ph)
    g2 = w.s([g1, f4], 'eqtrd', '( %s -> %s = %s )' % (ph, PRE2, D1))
    t2r, _, _, _ = hrrw(w, ph, t2, CLN("A'", 'N', PRE2), CLN('A"', 'N', D2), '( ( # ` W ) + 1 )',
                        ceq=clneq(w, ph, "A'", 'N', g2, PRE2, D1))
    t12 = hrseq(w, ph, phm, t1, t2r, C0, CLN("A'", 'N', D1), CLN('A"', 'N', D2), '1', '( ( # ` W ) + 1 )')
    N12 = '( 1 + ( ( # ` W ) + 1 ) )'
    # ---- stage 3: push Y on K
    D1K = UP(D1, 'K', 'X')
    d1kcl = updcl(w, ph, D1, 'K', 'X', tv, d1cl, kk, xx)
    d2cl = updcl(w, ph, D1K, 'J', RWH, tv, d1kcl, jj, rwhw)
    t3, D3 = pushstep(w, ph, phm, meqA2, a2, e1, kk, yk, d2cl, nss, 'A"', "E'", 'K', 'N', D2)
    rwhv = elv(w, ph, rwhw, RWH); xv = elv(w, ph, xx, 'X')
    d2k1 = updnv(w, ph, D1K, 'J', RWH, 'K', tv, d1kcl, jj, rwhv, kk, nkj)
    d2k2 = updkv(w, ph, D1, 'K', 'X', tv, d1cl, kk, xv)
    d2k = w.s([d2k1, d2k2], 'eqtrd', '( %s -> ( %s ` K ) = X )' % (ph, D2))
    r3, D3p = w.rewrite(D3, {'( %s ` K )' % D2: ('X', d2k)}, ph)
    assert D3p == UP(D2, 'K', YX), D3p
    t3r, _, _, _ = hrrw(w, ph, t3, CLN('A"', 'N', D2), CLN("E'", 'N', D3), '1', deq=clneq(w, ph, "E'", 'N', r3, D3, D3p))
    t123 = hrseq(w, ph, phm, t12, t3r, C0, CLN('A"', 'N', D2), CLN("E'", 'N', D3p), N12, '1')
    N123 = '( %s + 1 )' % N12
    # ---- stage 4: push Y on I
    d3cl = updcl(w, ph, D2, 'K', YX, tv, d2cl, kk, yxw)
    t4, D4 = pushstep(w, ph, phm, meqE1, e1, e2, ii, yi, d3cl, nss, "E'", 'E"', 'I', 'N', D3p)
    yxv = elv(w, ph, yxw, YX)
    d3i1 = updnv(w, ph, D2, 'K', YX, 'I', tv, d2cl, kk, yxv, ii, nik)
    d3i2 = updnv(w, ph, D1K, 'J', RWH, 'I', tv, d1kcl, jj, rwhv, ii, nij)
    d3i3 = updnv(w, ph, D1, 'K', 'X', 'I', tv, d1cl, kk, xv, ii, nik)
    d3i4 = updnv(w, ph, 'D', 'J', YDJ, 'I', tv, dd, jj, ydjv, ii, nij)
    d3i = d3i1
    for st, mid_ in ((d3i2, '( %s ` I )' % D1K), (d3i3, '( %s ` I )' % D1), (d3i4, DI)):
        d3i = w.s([d3i, st], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, D3p, mid_))
    r4, D4p = w.rewrite(D4, {'( %s ` I )' % D3p: (DI, d3i)}, ph)
    assert D4p == UP(D3p, 'I', YDI), D4p
    t4r, _, _, _ = hrrw(w, ph, t4, CLN("E'", 'N', D3p), CLN('E"', 'N', D4), '1', deq=clneq(w, ph, 'E"', 'N', r4, D4, D4p))
    t1234 = hrseq(w, ph, phm, t123, t4r, C0, CLN("E'", 'N', D3p), CLN('E"', 'N', D4p), N123, '1')
    N1234 = '( %s + 1 )' % N123
    # ---- stage 5: the load
    d4cl = updcl(w, ph, D3p, 'I', YDI, tv, d3cl, ii, ydiw)
    t5 = ldstep(w, ph, phm, meqE2, e2, el, d4cl, ll, nss, n2s, hld, 'E"', 'E', 'N', "N'", D4p)
    tall = hrseq(w, ph, phm, t1234, t5, C0, CLN('E"', 'N', D4p), CLN('E', "N'", D4p), N1234, '1')
    NALL = '( %s + 1 )' % N1234
    # collapse: the four updates at J , K collapse to two
    col = up4(w, ph, 'D', 'J', YDJ, 'K', 'X', RWH, YX, tv, dd, njk, jj, ydjw, rwhw, kk, xx, yxw)
    FIN = UP3('D', 'J', RWH, 'K', YX, 'I', YDI)
    r5, D5 = w.rewrite(D4p, {D3p: (UP(UP('D', 'J', RWH), 'K', YX), col)}, ph)
    assert D5 == FIN, D5
    tfin, _, _, _ = hrrw(w, ph, tall, C0, CLN('E', "N'", D4p), NALL, deq=clneq(w, ph, 'E', "N'", r5, D4p, FIN))
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    bound(w, ph, phm, tfin, C0, CLN('E', "N'", FIN), NALL, '( ( # ` W ) + 5 )', {'( # ` W )': nw}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fblp'): tm2fblp()
