"""T5: the composite `isZero` of TM/Prims.lean in the state-class form: the
state summary ` S' ` may be pair-valued, so Lean's ` v'.cmp = v.cmp ` is
carried by the same theorem (blueprint D2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GI = GX('K'), GX('I')
HDL = lambda k: '( %s ^m ( %s X. ( %s |_| 1o ) ) )' % (SS, SS, GX(k))
YS = '<" Y ">'
WYX = '( W ++ ( <" Y "> ++ X ) )'
YX = '( <" Y "> ++ X )'
DK, DI = '( D ` K )', '( D ` I )'
YDI = '( <" Y "> ++ %s )' % DI
RW = '( reverse ` W )'
RWH = '( %s ++ %s )' % (RW, YDI)
LTY = lambda f: '%s e. ( %s ^m %s )' % (f, SS, SS)
NC = lambda t: "{ q e. %s | ( S' ` q ) = ( O ` %s ) }" % (SS, t)

ST1 = PUSH('I', CONSTF('T', 'Y'), GT("A'"))
STMOV = POP('K', 'F', BRANCH('C', PUSH('I', 'P', GT("A'")), GT('A"')))
ST3 = PUSH('K', CONSTF('T', 'Y'), GT("E'"))
ST4 = LOAD('L', GT('E"'))
STZS = POP('I', "F'", BRANCH('C', PUSH('K', "P'", LOAD("L'", GT('E"'))), GT('E')))

NV = lambda r, z: NVF('F', r, z)
NV2 = lambda r, z: NVF("F'", r, z)
HCmvn = ('A. r e. N A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. N )'
         % (NV('r', 'z'), NV('r', 'z'), NV('r', 'z')))
HEmvn = 'A. r e. N ( -. ( C ` %s ) = 1o /\\ %s e. N )' % (NV('r', 'Y'), NV('r', 'Y'))
NCS0 = "{ s e. %s | ( S' ` s ) = ( O ` (/) ) }" % SS
HLD = 'A. r e. N ( L ` r ) e. %s' % NCS0
HCzs = ('A. m e. %s A. n e. B A. t e. Word B ( ( S\' ` m ) = ( O ` t ) -> '
        '( ( C ` %s ) = 1o /\\ ( P\' ` %s ) = n /\\ ( S\' ` ( L\' ` %s ) ) = ( O ` ( <" n "> ++ t ) ) ) )'
        % (SS, NV2('m', 'n'), NV2('m', 'n'), NV2('m', 'n')))
HEzs = "A. n e. %s ( -. ( C ` %s ) = 1o /\\ ( S' ` %s ) = ( S' ` n ) )" % (SS, NV2('n', 'Y'), NV2('n', 'Y'))

TREE = (
    ((PHM, '( M ` A ) = %s' % ST1, "( M ` A' ) = %s" % STMOV),
     ('( M ` A" ) = %s' % ST3, "( M ` E' ) = %s" % ST4, '( M ` E" ) = %s' % STZS)),
    ((('A e. %s' % LL, "A' e. %s" % LL, 'A" e. %s' % LL),
      ("E' e. %s" % LL, 'E" e. %s' % LL, 'E e. %s' % LL)),
     ('K e. %s' % DG, 'I e. %s' % DG, 'K =/= I'),
     (('F e. %s' % HDL('K'), "F' e. %s" % HDL('I'), 'C e. ( 2o ^m %s )' % SS),
      ('P e. ( %s ^m %s )' % (GI, SS), "P' e. ( %s ^m %s )" % (GK, SS)),
      (LTY('L'), LTY("L'")))),
    ((('B C_ %s' % GK, 'B C_ %s' % GI), ('Y e. %s' % GK, 'Y e. %s' % GI),
      ('W e. Word B', 'X e. Word %s' % GK, 'D e. %s' % STK_T)),
     ('( D ` K ) = %s' % WYX, ('N C_ %s' % SS, HCmvn, HEmvn)),
     (HLD, (HCzs, HEzs))))
PH = cj(TREE)


def tm2fiz():
    lab = 'tm2fiz'
    ph = PH
    w = W(lab, 'The composite ` isZero ` of TM/Prims.lean in the state-class form: '
               '` push comma s ; moveNum x s ; push comma x ; flag := true ; zeroScan s x ` '
               'tests the top number of stack ` K ` for zero without consuming it, '
               'restores ` K ` and the scratch stack ` I ` , and leaves the state summary '
               '` S\' ` at the fold ` ( O ` W ) ` of the number\'s digits.  Lean: '
               '` isZero_runs ` , whose ` flag = decide ( toNat l = 0 ) ` is the fold and '
               'whose ` cmp ` is preserved by choosing the summary pair-valued.  Five '
               'instances of ~ tm2hseq over ~ tm2fpshn , ~ tm2fmvn , ~ tm2flg and '
               '~ tm2fzs .')
    c = Ctx(w, ph, TREE)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, ii = c['K e. %s' % DG], c['I e. %s' % DG]
    nki = c['K =/= I']
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)
    dd = c['D e. %s' % STK_T]
    ww = c['W e. Word B']; xx = c['X e. Word %s' % GK]
    yk, yi = c['Y e. %s' % GK], c['Y e. %s' % GI]
    bk, bi = c['B C_ %s' % GK], c['B C_ %s' % GI]
    dke = c['( D ` K ) = %s' % WYX]
    nss = c['N C_ %s' % SS]
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    ysk = s1w(w, ph, yk, 'Y', GK); ysi = s1w(w, ph, yi, 'Y', GI)
    yxw = ccatw(w, ph, ysk, xx, YS, 'X', GK)
    wk = sswordd(w, ph, ww, 'W', 'B', GK, bk)
    ydiw = ccatw(w, ph, ysi, diw, YS, DI, GI)
    rwb = revw(w, ph, ww, 'W', 'B')
    rwi = sswordd(w, ph, rwb, RW, 'B', GI, bi)
    rwhw = ccatw(w, ph, rwi, ydiw, RW, YDI, GI)
    # the fold classes
    NC0, NCW = NC('(/)'), NC('W')
    nc0ss = w.s([], 'ssrab2', '%s C_ %s' % (NC0, SS))
    nc0ssa = w.s([nc0ss], 'a1i', '( %s -> %s C_ %s )' % (ph, NC0, SS))
    # ---- stage 1: push Y on I (class N)
    D1 = UP('D', 'I', YDI)
    d1cl = updcl(w, ph, 'D', 'I', YDI, tv, dd, ii, ydiw)
    t1 = applylem(w, ph, 'tm2fpshn',
                  ((phm, c['( M ` A ) = %s' % ST1]),
                   (c['A e. %s' % LL], c["A' e. %s" % LL], (ii, yi)), (dd, nss)),
                  HR(CLN('A', 'N', 'D'), 'T', 'M', CLN("A'", 'N', D1), '1'))
    # ---- stage 2: moveNum K -> I (class N)
    PRE2 = UP(UP(D1, 'K', WYX), 'I', YDI)
    D2 = UP(UP(D1, 'K', 'X'), 'I', RWH)
    t2 = applylem(w, ph, 'tm2fmvn',
                  ((((phm, c["( M ` A' ) = %s" % STMOV]),
                     ((c["A' e. %s" % LL], c['A" e. %s' % LL]), (kk, ii), nki),
                     ((c['F e. %s' % HDL('K')], c['C e. ( 2o ^m %s )' % SS], c['P e. ( %s ^m %s )' % (GI, SS)]),
                      ((bk, bi), (yk, xx, ydiw), d1cl),
                      (nss, (c[HCmvn], c[HEmvn])))),
                    ww)),
                  HR(CLN("A'", 'N', PRE2), 'T', 'M', CLN('A"', 'N', D2), '( ( # ` W ) + 1 )'))
    ydiv = elv(w, ph, ydiw, YDI)
    d1k = updnv(w, ph, 'D', 'I', YDI, 'K', tv, dd, ii, ydiv, kk, nki)
    d1k2 = w.s([d1k, dke], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, WYX))
    e4 = upidv(w, ph, D1, 'K', WYX, d1k2, tv, d1cl, kk)
    d1i = updkv(w, ph, 'D', 'I', YDI, tv, dd, ii, ydiv)
    f4 = upidv(w, ph, D1, 'I', YDI, d1i, tv, d1cl, ii)
    g1, mid = w.rewrite(PRE2, {UP(D1, 'K', WYX): (D1, e4)}, ph)
    g2 = w.s([g1, f4], 'eqtrd', '( %s -> %s = %s )' % (ph, PRE2, D1))
    t2r, _, _, _ = hrrw(w, ph, t2, CLN("A'", 'N', PRE2), CLN('A"', 'N', D2), '( ( # ` W ) + 1 )',
                        ceq=clneq(w, ph, "A'", 'N', g2, PRE2, D1))
    t12 = hrseq(w, ph, phm, t1, t2r, CLN('A', 'N', 'D'), CLN("A'", 'N', D1), CLN('A"', 'N', D2), '1', '( ( # ` W ) + 1 )')
    N12 = '( 1 + ( ( # ` W ) + 1 ) )'
    # ---- stage 3: push Y on K (class N)
    D1K = UP(D1, 'K', 'X')
    d1kcl = updcl(w, ph, D1, 'K', 'X', tv, d1cl, kk, xx)
    d2cl = updcl(w, ph, D1K, 'I', RWH, tv, d1kcl, ii, rwhw)
    D3 = UP(D2, 'K', '( <" Y "> ++ ( %s ` K ) )' % D2)
    t3 = applylem(w, ph, 'tm2fpshn',
                  ((phm, c['( M ` A" ) = %s' % ST3]),
                   (c['A" e. %s' % LL], c["E' e. %s" % LL], (kk, yk)), (d2cl, nss)),
                  HR(CLN('A"', 'N', D2), 'T', 'M', CLN("E'", 'N', D3), '1'))
    rwhv = elv(w, ph, rwhw, RWH); xv = elv(w, ph, xx, 'X')
    d2k1 = updnv(w, ph, D1K, 'I', RWH, 'K', tv, d1kcl, ii, rwhv, kk, nki)
    d2k2 = updkv(w, ph, D1, 'K', 'X', tv, d1cl, kk, xv)
    d2k = w.s([d2k1, d2k2], 'eqtrd', '( %s -> ( %s ` K ) = X )' % (ph, D2))
    r3, D3p = w.rewrite(D3, {'( %s ` K )' % D2: ('X', d2k)}, ph)
    assert D3p == UP(D2, 'K', YX), D3p
    t3r, _, _, _ = hrrw(w, ph, t3, CLN('A"', 'N', D2), CLN("E'", 'N', D3), '1', deq=clneq(w, ph, "E'", 'N', r3, D3, D3p))
    t123 = hrseq(w, ph, phm, t12, t3r, CLN('A', 'N', 'D'), CLN('A"', 'N', D2), CLN("E'", 'N', D3p), N12, '1')
    N123 = '( %s + 1 )' % N12
    # ---- stage 4: load L (N -> NC0); the hypothesis binds s, tm2fzs's class binds q
    d3cl = updcl(w, ph, D2, 'K', YX, tv, d2cl, kk, yxw)
    cv1 = w.s([], 'fveq2', "( s = q -> ( S' ` s ) = ( S' ` q ) )")
    cv2 = w.s([cv1], 'eqeq1d', "( s = q -> ( ( S' ` s ) = ( O ` (/) ) <-> ( S' ` q ) = ( O ` (/) ) ) )")
    cv3 = w.s([cv2], 'cbvrabv', '%s = %s' % (NCS0, NC0))
    cv4 = w.s([cv3], 'eleq2i', '( ( L ` r ) e. %s <-> ( L ` r ) e. %s )' % (NCS0, NC0))
    cv5 = w.s([cv4], 'ralbii', '( %s <-> A. r e. N ( L ` r ) e. %s )' % (HLD, NC0))
    hld = w.s([c[HLD], cv5], 'sylib', '( %s -> A. r e. N ( L ` r ) e. %s )' % (ph, NC0))
    t4 = applylem(w, ph, 'tm2flg',
                  ((phm, c["( M ` E' ) = %s" % ST4]),
                   (c["E' e. %s" % LL], c['E" e. %s' % LL], d3cl),
                   (c[LTY('L')], (nss, nc0ssa), hld)),
                  HR(CLN("E'", 'N', D3p), 'T', 'M', CLN('E"', NC0, D3p), '1'))
    t1234 = hrseq(w, ph, phm, t123, t4, CLN('A', 'N', 'D'), CLN("E'", 'N', D3p), CLN('E"', NC0, D3p), N123, '1')
    N1234 = '( %s + 1 )' % N123
    # ---- stage 5: zeroScan I -> K
    RRW = '( reverse ` %s )' % RW
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    PRE5 = UP(UP(D3p, 'I', RWH), 'K', '( (/) ++ %s )' % YX)
    POST5 = UP(UP(D3p, 'I', DI), 'K', '( ( %s ++ (/) ) ++ %s )' % (RRW, YX))
    N5 = '( ( # ` %s ) + 1 )' % RW
    NCE = NC('( %s ++ (/) )' % RRW)
    t5 = applylem(w, ph, 'tm2fzs',
                  ((((phm, c['( M ` E" ) = %s' % STZS]),
                     ((c['E" e. %s' % LL], c['E e. %s' % LL]), (ii, kk), nik),
                     ((c["F' e. %s" % HDL('I')], c['C e. ( 2o ^m %s )' % SS], c["P' e. ( %s ^m %s )" % (GK, SS)]),
                      ((bi, bk), (yi, diw, yxw), d3cl),
                      (c[LTY("L'")], (c[HCzs], c[HEzs])))),
                    (rwb, w0a))),
                  HR(CLN('E"', NC0, PRE5), 'T', 'M', CLN('E', NCE, POST5), N5))
    # PRE5 = D3p
    d3i1 = updnv(w, ph, D2, 'K', YX, 'I', tv, d2cl, kk, elv(w, ph, yxw, YX), ii, nik)   # ( D3p ` I ) = ( D2 ` I )
    d3i2 = updkv(w, ph, D1K, 'I', RWH, tv, d1kcl, ii, rwhv)                             # ( D2 ` I ) = RWH
    d3i = w.s([d3i1, d3i2], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, D3p, RWH))
    e5 = upidv(w, ph, D3p, 'I', RWH, d3i, tv, d3cl, ii)
    lid = w.s([yxw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, YX, YX))
    d3k = updkv(w, ph, D2, 'K', YX, tv, d2cl, kk, elv(w, ph, yxw, YX))                 # ( D3p ` K ) = YX
    f5 = upidv(w, ph, D3p, 'K', YX, d3k, tv, d3cl, kk)
    tbl = {UP(D3p, 'I', RWH): (D3p, e5), '( (/) ++ %s )' % YX: (YX, lid), UP(D3p, 'K', YX): (D3p, f5)}
    g5, pre5n = evaluate(w, ph, PRE5, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert pre5n == D3p, pre5n
    g5c = w.s([g5], 'eqcomd', '( %s -> %s = %s )' % (ph, D3p, PRE5))
    # POST5 = D , NCE = NCW
    rr = w.s([ww, w.inst('revrev')], 'syl', '( %s -> %s = W )' % (ph, RRW))
    rid = w.s([ww, w.inst('ccatrid')], 'syl', '( %s -> ( W ++ (/) ) = W )' % ph)
    dkec = w.s([dke], 'eqcomd', '( %s -> %s = %s )' % (ph, WYX, DK))
    D3c = UP(UP('D', 'I', RWH), 'K', YX)
    col1 = up3(w, ph, 'D', 'I', YDI, 'K', 'X', RWH, tv, dd, nik, ii, ydiw, rwhw, kk, xx)
    dirw = updcl(w, ph, 'D', 'I', RWH, tv, dd, ii, rwhw)
    col2 = up2(w, ph, UP('D', 'I', RWH), 'K', 'X', YX, tv, dirw, kk, xx, yxw)
    dkw = stkfv(w, ph, 'D', 'K', tv, dd, kk)
    col3 = up4(w, ph, 'D', 'I', RWH, 'K', YX, DI, DK, tv, dd, nik, ii, rwhw, diw, kk, yxw, dkw)
    ui = upid(w, ph, 'D', 'I', tv, dd, ii)
    uk = upid(w, ph, 'D', 'K', tv, dd, kk)
    tbl2 = {RRW: ('W', rr), '( W ++ (/) )': ('W', rid), WYX: (DK, dkec),
            D2: (UP(UP('D', 'I', RWH), 'K', 'X'), col1),
            UP(UP(UP('D', 'I', RWH), 'K', 'X'), 'K', YX): (D3c, col2),
            UP(UP(D3c, 'I', DI), 'K', DK): (UP(UP('D', 'I', DI), 'K', DK), col3),
            UP('D', 'I', DI): ('D', ui), UP('D', 'K', DK): ('D', uk)}
    ps, postn = evaluate(w, ph, POST5, {}, extra_rules=(lambda n: tbl2.get(n.text())))
    assert postn == 'D', postn
    ne1 = w.s([rr], 'oveq1d', '( %s -> ( %s ++ (/) ) = ( W ++ (/) ) )' % (ph, RRW))
    ne2 = w.s([ne1, rid], 'eqtrd', '( %s -> ( %s ++ (/) ) = W )' % (ph, RRW))
    ne3 = w.s([ne2], 'fveq2d', '( %s -> ( O ` ( %s ++ (/) ) ) = ( O ` W ) )' % (ph, RRW))
    ne4 = w.s([ne3], 'eqeq2d', "( %s -> ( ( S' ` q ) = ( O ` ( %s ++ (/) ) ) <-> ( S' ` q ) = ( O ` W ) ) )" % (ph, RRW))
    ne5 = w.s([ne4], 'rabbidv', '( %s -> %s = %s )' % (ph, NCE, NCW))
    ceq5 = w.s([clneq(w, ph, 'E"', NC0, g5c, D3p, PRE5)], 'eqcomd', '( %s -> %s = %s )' % (ph, CLN('E"', NC0, PRE5), CLN('E"', NC0, D3p)))
    dq1 = clneq(w, ph, 'E', NCE, ps, POST5, 'D')
    dq2 = clnneq(w, ph, 'E', ne5, NCE, NCW, 'D')
    dq = w.s([dq1, dq2], 'eqtrd', '( %s -> %s = %s )' % (ph, CLN('E', NCE, POST5), CLN('E', NCW, 'D')))
    rl = w.s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))
    n5 = w.s([rl], 'oveq1d', '( %s -> %s = ( ( # ` W ) + 1 ) )' % (ph, N5))
    t5r, _, _, _ = hrrw(w, ph, t5, CLN('E"', NC0, PRE5), CLN('E', NCE, POST5), N5, ceq=ceq5, deq=dq, neq=n5)
    tall = hrseq(w, ph, phm, t1234, t5r, CLN('A', 'N', 'D'), CLN('E"', NC0, D3p), CLN('E', NCW, 'D'), N1234, '( ( # ` W ) + 1 )')
    NALL = '( %s + ( ( # ` W ) + 1 ) )' % N1234
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    bound(w, ph, phm, tall, CLN('A', 'N', 'D'), CLN('E', NCW, 'D'), NALL, '( ( 2 x. ( # ` W ) ) + 5 )',
          {'( # ` W )': nw}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fiz'): tm2fiz()
