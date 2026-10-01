"""T5: the composite `dup` of TM/Prims.lean --- five stages sequenced by
~ tm2hseq over ~ tm2fpush , ~ tm2fmov , ~ tm2fmv2 (blueprint D1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GJ, GI = GX('K'), GX('J'), GX('I')
HDL = lambda k: '( %s ^m ( %s X. ( %s |_| 1o ) ) )' % (SS, SS, GX(k))
YS = '<" Y ">'
WYX = '( W ++ ( <" Y "> ++ X ) )'
YX = '( <" Y "> ++ X )'
DK, DJ, DI = '( D ` K )', '( D ` J )', '( D ` I )'
YDI = '( <" Y "> ++ %s )' % DI
YDJ = '( <" Y "> ++ %s )' % DJ
RW = '( reverse ` W )'
RWH = '( %s ++ %s )' % (RW, YDI)

# the five statements
ST1 = PUSH('I', CONSTF('T', 'Y'), GT("A'"))
STMOV = POP('K', 'F', BRANCH('C', PUSH('I', 'P', GT("A'")), GT('A"')))
ST3 = PUSH('K', CONSTF('T', 'Y'), GT("E'"))
ST4 = PUSH('J', CONSTF('T', 'Y'), GT('E"'))
STMV2 = POP('I', "F'", BRANCH('C', PUSH('K', "P'", PUSH('J', 'O', GT('E"'))), GT('E')))

HCmov = 'A. r e. %s A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z )' % (SS, NVF('F', 'r', 'z'), NVF('F', 'r', 'z'))
HEmov = 'A. r e. %s -. ( C ` %s ) = 1o' % (SS, NVF('F', 'r', 'Y'))
HCmv2 = ('A. r e. %s A. z e. B ( ( C ` %s ) = 1o /\\ ( P\' ` %s ) = z /\\ ( O ` %s ) = z )'
         % (SS, NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z')))
HEmv2 = 'A. r e. %s -. ( C ` %s ) = 1o' % (SS, NVF("F'", 'r', 'Y'))

TREE = (
    ((PHM, '( M ` A ) = %s' % ST1, "( M ` A' ) = %s" % STMOV),
     ('( M ` A" ) = %s' % ST3, "( M ` E' ) = %s" % ST4, '( M ` E" ) = %s' % STMV2)),
    ((('A e. %s' % LL, "A' e. %s" % LL, 'A" e. %s' % LL),
      ("E' e. %s" % LL, 'E" e. %s' % LL, 'E e. %s' % LL)),
     ('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG),
     ('K =/= J', 'K =/= I', 'J =/= I')),
    ((('F e. %s' % HDL('K'), "F' e. %s" % HDL('I'), 'C e. ( 2o ^m %s )' % SS),
      ('P e. ( %s ^m %s )' % (GI, SS), "P' e. ( %s ^m %s )" % (GK, SS), 'O e. ( %s ^m %s )' % (GJ, SS))),
     (('B C_ %s' % GK, 'B C_ %s' % GJ, 'B C_ %s' % GI),
      ('Y e. %s' % GK, 'Y e. %s' % GJ, 'Y e. %s' % GI),
      ('W e. Word B', 'X e. Word %s' % GK, 'D e. %s' % STK_T)),
     ('( D ` K ) = %s' % WYX, (HCmov, HEmov), (HCmv2, HEmv2))))
PH = cj(TREE)


def tm2fdup():
    lab = 'tm2fdup'
    ph = PH
    w = W(lab, 'The composite ` dup ` of TM/Prims.lean: ` push comma s ; moveNum x s ; '
               'push comma x ; push comma y ; move2Num s x y ` copies the top number of '
               'stack ` K ` (with its terminator) onto stack ` J ` , leaves ` K ` as it '
               'was and restores the scratch stack ` I ` , in ` ( 2 x. ( # ` W ) ) + 5 ` '
               'steps.  Lean: ` dup_runs ` .  Five instances of ~ tm2hseq over '
               '~ tm2fpush , ~ tm2fmov and ~ tm2fmv2 ; the work is the stack algebra '
               'between the stages.')
    c = Ctx(w, ph, TREE)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)
    nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    dd = c['D e. %s' % STK_T]
    ww = c['W e. Word B']; xx = c['X e. Word %s' % GK]
    yk, yj, yi = c['Y e. %s' % GK], c['Y e. %s' % GJ], c['Y e. %s' % GI]
    bk, bj, bi = c['B C_ %s' % GK], c['B C_ %s' % GJ], c['B C_ %s' % GI]
    dke = c['( D ` K ) = %s' % WYX]
    # words
    dkw = stkfv(w, ph, 'D', 'K', tv, dd, kk)
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    ysk = s1w(w, ph, yk, 'Y', GK); ysj = s1w(w, ph, yj, 'Y', GJ); ysi = s1w(w, ph, yi, 'Y', GI)
    yxw = ccatw(w, ph, ysk, xx, YS, 'X', GK)
    wk = sswordd(w, ph, ww, 'W', 'B', GK, bk)
    wyxw = ccatw(w, ph, wk, yxw, 'W', YX, GK)
    ydiw = ccatw(w, ph, ysi, diw, YS, DI, GI)
    ydjw = ccatw(w, ph, ysj, djw, YS, DJ, GJ)
    rwb = revw(w, ph, ww, 'W', 'B')
    rwi = sswordd(w, ph, rwb, RW, 'B', GI, bi)
    rwhw = ccatw(w, ph, rwi, ydiw, RW, YDI, GI)
    # ---- stage 1: push Y on I
    D1 = UP('D', 'I', YDI)
    d1cl = updcl(w, ph, 'D', 'I', YDI, tv, dd, ii, ydiw)
    t1 = applylem(w, ph, 'tm2fpush',
                  ((phm, c['( M ` A ) = %s' % ST1]),
                   (c['A e. %s' % LL], c["A' e. %s" % LL], (ii, yi)), dd),
                  HR(CLN('A', SS, 'D'), 'T', 'M', CLN("A'", SS, D1), '1'))
    # ---- stage 2: moveNum K -> I
    PRE2 = UP(UP(D1, 'K', WYX), 'I', YDI)
    D2 = UP(UP(D1, 'K', 'X'), 'I', RWH)
    t2 = applylem(w, ph, 'tm2fmov',
                  ((((phm, c["( M ` A' ) = %s" % STMOV]),
                     ((c["A' e. %s" % LL], c['A" e. %s' % LL]), (kk, ii), nki),
                     ((c['F e. %s' % HDL('K')], c['C e. ( 2o ^m %s )' % SS], c['P e. ( %s ^m %s )' % (GI, SS)]),
                      ((bk, bi), (yk, xx, ydiw), d1cl),
                      (c[HCmov], c[HEmov]))),
                    ww)),
                  HR(CLN("A'", SS, PRE2), 'T', 'M', CLN('A"', SS, D2), '( ( # ` W ) + 1 )'))
    # PRE2 = D1
    ydiv = elv(w, ph, ydiw, YDI)
    d1k = updnv(w, ph, 'D', 'I', YDI, 'K', tv, dd, ii, ydiv, kk, nki)      # ( D1 ` K ) = ( D ` K )
    d1k2 = w.s([d1k, dke], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, WYX))
    d1k2c = w.s([d1k2], 'eqcomd', '( %s -> %s = ( %s ` K ) )' % (ph, WYX, D1))
    u1 = upid(w, ph, D1, 'K', tv, d1cl, kk)
    e1 = w.s([d1k2c], 'opeq2d', '( %s -> <. K , %s >. = <. K , ( %s ` K ) >. )' % (ph, WYX, D1))
    e2 = w.s([e1], 'sneqd', '( %s -> { <. K , %s >. } = { <. K , ( %s ` K ) >. } )' % (ph, WYX, D1))
    e3 = w.s([e2], 'uneq2d', '( %s -> %s = %s )' % (ph, UP(D1, 'K', WYX), UP(D1, 'K', '( %s ` K )' % D1)))
    e4 = w.s([e3, u1], 'eqtrd', '( %s -> %s = %s )' % (ph, UP(D1, 'K', WYX), D1))
    d1i = updkv(w, ph, 'D', 'I', YDI, tv, dd, ii, ydiv)                    # ( D1 ` I ) = YDI
    d1ic = w.s([d1i], 'eqcomd', '( %s -> %s = ( %s ` I ) )' % (ph, YDI, D1))
    u2 = upid(w, ph, D1, 'I', tv, d1cl, ii)
    f1 = w.s([d1ic], 'opeq2d', '( %s -> <. I , %s >. = <. I , ( %s ` I ) >. )' % (ph, YDI, D1))
    f2 = w.s([f1], 'sneqd', '( %s -> { <. I , %s >. } = { <. I , ( %s ` I ) >. } )' % (ph, YDI, D1))
    f3 = w.s([f2], 'uneq2d', '( %s -> %s = %s )' % (ph, UP(D1, 'I', YDI), UP(D1, 'I', '( %s ` I )' % D1)))
    f4 = w.s([f3, u2], 'eqtrd', '( %s -> %s = %s )' % (ph, UP(D1, 'I', YDI), D1))
    g1, mid = w.rewrite(PRE2, {UP(D1, 'K', WYX): (D1, e4)}, ph)
    assert mid == UP(D1, 'I', YDI), mid
    g2 = w.s([g1, f4], 'eqtrd', '( %s -> %s = %s )' % (ph, PRE2, D1))
    g2c = w.s([g2], 'eqcomd', '( %s -> %s = %s )' % (ph, D1, PRE2))
    cl2 = w.s([g2c], 'sneqd', '( %s -> { %s } = { %s } )' % (ph, D1, PRE2))
    cl3 = w.s([cl2], 'xpeq2d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ph, SS, D1, SS, PRE2))
    cl4 = w.s([cl3], 'xpeq2d', '( %s -> %s = %s )' % (ph, CLN("A'", SS, D1), CLN("A'", SS, PRE2)))
    t2r, _, _, _ = hrrw(w, ph, t2, CLN("A'", SS, PRE2), CLN('A"', SS, D2), '( ( # ` W ) + 1 )',
                        ceq=w.s([cl4], 'eqcomd', '( %s -> %s = %s )' % (ph, CLN("A'", SS, PRE2), CLN("A'", SS, D1))))
    t12 = hrseq(w, ph, phm, t1, t2r, CLN('A', SS, 'D'), CLN("A'", SS, D1), CLN('A"', SS, D2), '1', '( ( # ` W ) + 1 )')
    N12 = '( 1 + ( ( # ` W ) + 1 ) )'
    # ---- stage 3: push Y on K
    D1K = UP(D1, 'K', 'X')
    d1kcl = updcl(w, ph, D1, 'K', 'X', tv, d1cl, kk, xx)
    d2cl = updcl(w, ph, D1K, 'I', RWH, tv, d1kcl, ii, rwhw)
    D3 = UP(D2, 'K', '( <" Y "> ++ ( %s ` K ) )' % D2)
    t3 = applylem(w, ph, 'tm2fpush',
                  ((phm, c['( M ` A" ) = %s' % ST3]),
                   (c['A" e. %s' % LL], c["E' e. %s" % LL], (kk, yk)), d2cl),
                  HR(CLN('A"', SS, D2), 'T', 'M', CLN("E'", SS, D3), '1'))
    rwhv = elv(w, ph, rwhw, RWH); xv = elv(w, ph, xx, 'X')
    d2k1 = updnv(w, ph, D1K, 'I', RWH, 'K', tv, d1kcl, ii, rwhv, kk, nki)   # ( D2 ` K ) = ( D1K ` K )
    d2k2 = updkv(w, ph, D1, 'K', 'X', tv, d1cl, kk, xv)                    # ( D1K ` K ) = X
    d2k = w.s([d2k1, d2k2], 'eqtrd', '( %s -> ( %s ` K ) = X )' % (ph, D2))
    r3, D3p = w.rewrite(D3, {'( %s ` K )' % D2: ('X', d2k)}, ph)
    assert D3p == UP(D2, 'K', YX), D3p
    cl5 = w.s([r3], 'sneqd', '( %s -> { %s } = { %s } )' % (ph, D3, D3p))
    cl6 = w.s([cl5], 'xpeq2d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ph, SS, D3, SS, D3p))
    cl7 = w.s([cl6], 'xpeq2d', '( %s -> %s = %s )' % (ph, CLN("E'", SS, D3), CLN("E'", SS, D3p)))
    t3r, _, _, _ = hrrw(w, ph, t3, CLN('A"', SS, D2), CLN("E'", SS, D3), '1', deq=cl7)
    t123 = hrseq(w, ph, phm, t12, t3r, CLN('A', SS, 'D'), CLN('A"', SS, D2), CLN("E'", SS, D3p), N12, '1')
    N123 = '( %s + 1 )' % N12
    # ---- stage 4: push Y on J
    d3cl = updcl(w, ph, D2, 'K', YX, tv, d2cl, kk, yxw)
    D4 = UP(D3p, 'J', '( <" Y "> ++ ( %s ` J ) )' % D3p)
    t4 = applylem(w, ph, 'tm2fpush',
                  ((phm, c["( M ` E' ) = %s" % ST4]),
                   (c["E' e. %s" % LL], c['E" e. %s' % LL], (jj, yj)), d3cl),
                  HR(CLN("E'", SS, D3p), 'T', 'M', CLN('E"', SS, D4), '1'))
    yxv = elv(w, ph, yxw, YX)
    d3j1 = updnv(w, ph, D2, 'K', YX, 'J', tv, d2cl, kk, yxv, jj, njk)      # ( D3p ` J ) = ( D2 ` J )
    d3j2 = updnv(w, ph, D1K, 'I', RWH, 'J', tv, d1kcl, ii, rwhv, jj, nji)  # ( D2 ` J ) = ( D1K ` J )
    d3j3 = updnv(w, ph, D1, 'K', 'X', 'J', tv, d1cl, kk, xv, jj, njk)      # ( D1K ` J ) = ( D1 ` J )
    d3j4 = updnv(w, ph, 'D', 'I', YDI, 'J', tv, dd, ii, ydiv, jj, nji)     # ( D1 ` J ) = ( D ` J )
    d3j = w.s([d3j1, w.s([d3j2, w.s([d3j3, d3j4], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D1K, DJ))],
                        'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D2, DJ))],
              'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D3p, DJ))
    r4, D4p = w.rewrite(D4, {'( %s ` J )' % D3p: (DJ, d3j)}, ph)
    assert D4p == UP(D3p, 'J', YDJ), D4p
    cl8 = w.s([r4], 'sneqd', '( %s -> { %s } = { %s } )' % (ph, D4, D4p))
    cl9 = w.s([cl8], 'xpeq2d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ph, SS, D4, SS, D4p))
    cl10 = w.s([cl9], 'xpeq2d', '( %s -> %s = %s )' % (ph, CLN('E"', SS, D4), CLN('E"', SS, D4p)))
    t4r, _, _, _ = hrrw(w, ph, t4, CLN("E'", SS, D3p), CLN('E"', SS, D4), '1', deq=cl10)
    t1234 = hrseq(w, ph, phm, t123, t4r, CLN('A', SS, 'D'), CLN("E'", SS, D3p), CLN('E"', SS, D4p), N123, '1')
    N1234 = '( %s + 1 )' % N123
    # ---- stage 5: move2Num I -> K , J
    RRW = '( reverse ` %s )' % RW
    PRE5 = UP(UP(UP('D', 'I', RWH), 'K', YX), 'J', YDJ)
    POST5 = UP(UP(UP('D', 'I', DI), 'K', '( %s ++ %s )' % (RRW, YX)), 'J', '( %s ++ %s )' % (RRW, YDJ))
    N5 = '( ( # ` %s ) + 1 )' % RW
    t5 = applylem(w, ph, 'tm2fmv2',
                  ((((phm, c['( M ` E" ) = %s' % STMV2]),
                     ((c['E" e. %s' % LL], c['E e. %s' % LL]), (ii, kk, jj), (nik, nij, nkj)),
                     (((c["F' e. %s" % HDL('I')], c['C e. ( 2o ^m %s )' % SS]),
                       (c["P' e. ( %s ^m %s )" % (GK, SS)], c['O e. ( %s ^m %s )' % (GJ, SS)])),
                      ((bi, bk, bj), ((yi, diw), (yxw, ydjw)), dd),
                      (c[HCmv2], c[HEmv2]))),
                    rwb)),
                  HR(CLN('E"', SS, PRE5), 'T', 'M', CLN('E', SS, POST5), N5))
    # D4p = PRE5
    DA = UP(UP(UP('D', 'I', YDI), 'K', 'X'), 'I', RWH)     # = D2
    assert DA == D2
    col1 = up3(w, ph, 'D', 'I', YDI, 'K', 'X', RWH, tv, dd, nik, ii, ydiw, rwhw, kk, xx)
    DB = UP(UP('D', 'I', RWH), 'K', 'X')
    dirw = updcl(w, ph, 'D', 'I', RWH, tv, dd, ii, rwhw)
    col2 = up2(w, ph, UP('D', 'I', RWH), 'K', 'X', YX, tv, dirw, kk, xx, yxw)
    h1, D4a = w.rewrite(D4p, {D2: (DB, col1)}, ph)
    assert D4a == UP(UP(DB, 'K', YX), 'J', YDJ), D4a
    h2, D4b = w.rewrite(D4a, {UP(DB, 'K', YX): (UP(UP('D', 'I', RWH), 'K', YX), col2)}, ph)
    assert D4b == PRE5, (D4b, PRE5)
    h3 = w.s([h1, h2], 'eqtrd', '( %s -> %s = %s )' % (ph, D4p, PRE5))
    cl11 = w.s([h3], 'sneqd', '( %s -> { %s } = { %s } )' % (ph, D4p, PRE5))
    cl12 = w.s([cl11], 'xpeq2d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ph, SS, D4p, SS, PRE5))
    cl13 = w.s([cl12], 'xpeq2d', '( %s -> %s = %s )' % (ph, CLN('E"', SS, D4p), CLN('E"', SS, PRE5)))
    cl13c = w.s([cl13], 'eqcomd', '( %s -> %s = %s )' % (ph, CLN('E"', SS, PRE5), CLN('E"', SS, D4p)))
    # POST5 = UP( D , J , ( W ++ ( <" Y "> ++ ( D ` J ) ) ) )
    rr = w.s([ww, w.inst('revrev')], 'syl', '( %s -> %s = W )' % (ph, RRW))
    ui = upid(w, ph, 'D', 'I', tv, dd, ii)
    dkec = w.s([dke], 'eqcomd', '( %s -> %s = %s )' % (ph, WYX, DK))
    uk = upid(w, ph, 'D', 'K', tv, dd, kk)
    tbl = {RRW: ('W', rr), UP('D', 'I', DI): ('D', ui), WYX: (DK, dkec), UP('D', 'K', DK): ('D', uk)}
    ps, POSTn = evaluate(w, ph, POST5, {}, extra_rules=(lambda n: tbl.get(n.text())))
    FIN = UP('D', 'J', '( W ++ %s )' % YDJ)
    assert POSTn == FIN, (POSTn, FIN)
    cl14 = w.s([ps], 'sneqd', '( %s -> { %s } = { %s } )' % (ph, POST5, FIN))
    cl15 = w.s([cl14], 'xpeq2d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ph, SS, POST5, SS, FIN))
    cl16 = w.s([cl15], 'xpeq2d', '( %s -> %s = %s )' % (ph, CLN('E', SS, POST5), CLN('E', SS, FIN)))
    rl = w.s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))
    n5 = w.s([rl], 'oveq1d', '( %s -> %s = ( ( # ` W ) + 1 ) )' % (ph, N5))
    t5r, _, _, _ = hrrw(w, ph, t5, CLN('E"', SS, PRE5), CLN('E', SS, POST5), N5, ceq=cl13c, deq=cl16, neq=n5)
    tall = hrseq(w, ph, phm, t1234, t5r, CLN('A', SS, 'D'), CLN('E"', SS, D4p), CLN('E', SS, FIN), N1234, '( ( # ` W ) + 1 )')
    NALL = '( %s + ( ( # ` W ) + 1 ) )' % N1234
    # the bound
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    bound(w, ph, phm, tall, CLN('A', SS, 'D'), CLN('E', SS, FIN), NALL, '( ( 2 x. ( # ` W ) ) + 5 )',
          {'( # ` W )': nw}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fdup'): tm2fdup()
