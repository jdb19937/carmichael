"""T-MD: ` mul ` assembled (~ tm2fml ): ` push comma w ; popBit y ` (~ tm2fpshn ,
~ tm2fpopn ), the loop ~ tm2fmlq , the failed test (~ tm2fbrg ) and ` dropNum x `
(~ tm2fdrop ).  Lean: ` mul_runs ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fml():
    lab = 'tm2fml'
    tree, ph = TREE_ML, cj(TREE_ML)
    H0, X0_, Y0 = HF('0'), XF('0'), YF('0')
    HR_, XR_, YR_ = HF('R'), XF('R'), YF('R')
    YDI = CC(S1('Y'), '( D ` I )')
    U0Y0 = CC(S1(UF('0')), Y0)
    w = W(lab, 'The multiplication fragment ` mul ` of TM/MulDiv.lean: the accumulator\'s terminator '
               'is pushed on ` I ` and the first multiplier symbol popped from ` J ` (~ tm2fpshn , '
               '~ tm2fpopn ), the loop ~ tm2fmlq runs ` R ` iterations, the test fails (~ tm2fbrg ) '
               'and the doubled multiplicand is dropped from ` K ` (~ tm2fdrop ): ` K ` and ` J ` are '
               'consumed, ` I ` holds the product word ` ( H ` R ) ` .  Lean: ` mul_runs ` ; the '
               'conditional adds are the hypothesis triples of the loop (blueprint D4), the state '
               'after the run is any (D5).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    p0l, p1l, al, b0l, el, epl = [c[LAB(x)] for x in ('P0', 'P1', 'A', 'B0', 'E', "E'")]
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    c0t, cpt, fpt = c[CTY('C0')], c[CTY("C'")], c[RTY("F'", 'K')]
    bk, yk, yi, u0j = c['B C_ %s' % GK], c['Y e. %s' % GK], c['Y e. %s' % GI], c['%s e. %s' % (UF('0'), GJ)]
    dd, init = c[STKD('D')], c[INIT_ML]
    rr, tt, n0s, hp0 = c['R e. NN0'], c["T' e. NN0"], c[SSS('N0')], c[HPB('N0', UF('0'), NF('0'))]
    hcdr, hedr, fam = c[HCDR], c[HEDR], c[FAM_MQ]
    fin = c[FIN_ML]
    x0e = w.s([init, w.inst('simp1')], 'syl', '( %s -> %s = ( D ` K ) )' % (ph, X0_))
    h0e = w.s([init, w.inst('simp2')], 'syl', '( %s -> %s = %s )' % (ph, H0, YDI))
    dje = w.s([init, w.inst('simp3')], 'syl', '( %s -> ( D ` J ) = %s )' % (ph, U0Y0))
    fin1 = w.s([fin], 'simpld', '( %s -> ( %s = %s /\\ %s ) )' % (ph, XR_, CC('W', YX0), WRD('W', 'B')))
    fin2 = w.s([fin], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, WRD('X0', GK), HTF(NF('R'), 'C0')))
    xre = w.s([fin1], 'simpld', '( %s -> %s = %s )' % (ph, XR_, CC('W', YX0)))
    ww = w.s([fin1], 'simprd', '( %s -> W e. Word B )' % ph)
    x0w = w.s([fin2], 'simpld', '( %s -> X0 e. Word %s )' % (ph, GK))
    htf = w.s([fin2], 'simprd', '( %s -> %s )' % (ph, HTF(NF('R'), 'C0')))
    sss = w.s([], 'ssid', '%s C_ %s' % (SS, SS)); sssa = w.s([sss], 'a1i', '( %s -> %s C_ %s )' % (ph, SS, SS))
    gb0 = gotocl(w, ph, tv, 'B0', b0l)

    def famat(X, xfz):
        st, _ = inst_v(w, ph, fam, cj(FAMB_MQ('i')), 'i', X, xfz)
        cx = Ctx(w, ph, FAMB_MQ(X), root=st)
        return dict(xw=cx[WRD(XF(X), GK)], yw=cx[WRD(YF(X), GJ)], hw=cx[WRD(HF(X), GI)], nss=cx[SSS(NF(X))])

    def fzmem(X, xnn, xle):
        return w.s([w.s([xnn, rr, xle], '3jca', '( %s -> ( %s e. NN0 /\\ R e. NN0 /\\ %s <_ R ) )' % (ph, X, X)),
                    w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... R ) )' % (ph, X))
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ R )' % ph)
    rnn = w.s([rr, w.inst('nn0red')], 'syl', '( %s -> R e. RR )' % ph)
    rle = w.s([rnn, w.inst('leidd')], 'syl', '( %s -> R <_ R )' % ph)
    f0 = famat('0', fzmem('0', z0a, ge0))
    fR = famat('R', fzmem('R', rr, rle))
    # ---- stage 1: push Y on I at N0
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    ydiw = ccatw(w, ph, s1w(w, ph, yi, 'Y', GI), diw, S1('Y'), '( D ` I )', GI)
    bld1 = bldr(w, ph, c, phm)
    s1, c1 = inst(w, ph, 'tm2fpshn', {'A': 'P0', 'E': 'P1', 'K': 'I', 'Z': 'Y', 'N': 'N0'}, bld1)
    C0, D1c, B1 = triple_parts(c1)
    D1y = UP('D', 'I', YDI)
    assert C0 == CLN('P0', 'N0', 'D') and D1c == CLN('P1', 'N0', D1y), (C0, D1c)
    D1 = UP('D', 'I', H0)
    h0ec = w.s([h0e], 'eqcomd', '( %s -> %s = %s )' % (ph, YDI, H0))
    s1r, _, _, _ = hrrw(w, ph, s1, C0, D1c, B1, deq=clneq(w, ph, 'P1', 'N0', upeq(w, ph, 'D', 'I', h0ec, YDI, H0), D1y, D1))
    # ---- stage 2: pop U_0 from J at P1, N0 -> ( N ` 0 )
    d1cl = updcl(w, ph, 'D', 'I', H0, tv, dd, ii, f0['hw'])
    d1j = updnv(w, ph, 'D', 'I', H0, 'J', tv, dd, ii, elv(w, ph, f0['hw'], H0), jj, nji)
    d1je = w.s([d1j, dje], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D1, U0Y0))
    bld2 = bldr(w, ph, c, phm, {STKD(D1): d1cl, '( %s ` J ) = %s' % (D1, U0Y0): d1je, WRD(Y0, GJ): f0['yw'], SSS(NF('0')): f0['nss']})
    s2, c2 = inst(w, ph, 'tm2fpopn', {'A': 'P1', 'E': 'A', 'K': 'J', 'Z': UF('0'), 'X': Y0, 'N': 'N0', "N'": NF('0'), 'D': D1}, bld2)
    C2a, D2c, B2 = triple_parts(c2)
    D2 = UP(D1, 'J', Y0)
    assert C2a == CLN('P1', 'N0', D1) and D2c == CLN('A', NF('0'), D2), (C2a, D2c)
    s12 = hrseq(w, ph, phm, s1r, s2, C0, CLN('P1', 'N0', D1), D2c, B1, B2)
    N12 = '( %s + %s )' % (B1, B2)
    # ---- stage 3: the loop; DPM( 0 ) = D2
    d1k = updnv(w, ph, 'D', 'I', H0, 'K', tv, dd, ii, elv(w, ph, f0['hw'], H0), kk, nki)
    x0k = w.s([x0e, w.s([d1k], 'eqcomd', '( %s -> ( D ` K ) = ( %s ` K ) )' % (ph, D1))], 'eqtrd', '( %s -> %s = ( %s ` K ) )' % (ph, X0_, D1))
    u1 = upidv(w, ph, D1, 'K', X0_, w.s([x0k], 'eqcomd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, X0_)), tv, d1cl, kk)
    r0, dpm0n = w.rewrite(DPM('0'), {UP(D1, 'K', X0_): (D1, u1)}, ph)
    assert dpm0n == D2, dpm0n
    s3 = applylem(w, ph, 'tm2fmlq', leafsteps(TREE_MLQ, lambda t: c[t]), CONCL_MLQ)
    CL0, CLR = CLN('A', NF('0'), DPM('0')), CLN('A', NF('R'), DPM('R'))
    s3r, _, _, _ = hrrw(w, ph, s3, CL0, CLR, "( R x. ( T' + 4 ) )", ceq=clneq(w, ph, 'A', NF('0'), r0, DPM('0'), D2))
    s123 = hrseq(w, ph, phm, s12, s3r, C0, D2c, CLR, N12, "( R x. ( T' + 4 ) )")
    N123 = "( %s + ( R x. ( T' + 4 ) ) )" % N12
    # ---- stage 4: the failed test at A -> E on ( N ` R )
    dpR, viR, vkR, vjR = dpmfacts(w, ph, 'R', tv, dd, kk, jj, ii, nkj, nki, nji, fR['hw'], fR['xw'], fR['yw'])
    s4 = applylem(w, ph, 'tm2fbrg', ((phm, c[MEQ('A', STM_MTE)]), (al, el, dpR), ((c0t, gb0), (fR['nss'], htf))),
                  TRI(CLR, CLN('E', NF('R'), DPM('R')), '1'))
    s1234 = hrseq(w, ph, phm, s123, s4, C0, CLR, CLN('E', NF('R'), DPM('R')), N123, '1')
    N1234 = '( %s + 1 )' % N123
    # ---- stage 5: dropNum K at E (tm2fdrop at S)
    U1 = UP('D', 'I', HR_)
    u1cl = updcl(w, ph, 'D', 'I', HR_, tv, dd, ii, fR['hw'])
    DB = UP(U1, 'J', YR_)
    dbcl = updcl(w, ph, U1, 'J', YR_, tv, u1cl, jj, fR['yw'])
    WYX0 = CC('W', YX0)
    yx0w = ccatw(w, ph, s1w(w, ph, yk, 'Y', GK), x0w, S1('Y'), 'X0', GK)
    cm = upc(w, ph, U1, 'K', XR_, 'J', YR_, tv, u1cl, nkj, kk, fR['xw'], jj, fR['yw'])
    r5, dpRn = w.rewrite(DPM('R'), {DPM('R'): (UP(DB, 'K', XR_), cm)}, ph)
    r6, dpRn2 = w.rewrite(dpRn, {XR_: (WYX0, xre)}, ph)
    PRE5 = UP(DB, 'K', WYX0)
    assert dpRn2 == PRE5, dpRn2
    r56 = w.s([r5, r6], 'eqtrd', '( %s -> %s = %s )' % (ph, DPM('R'), PRE5))
    bld5 = bldr(w, ph, c, phm, {STKD(DB): dbcl, WRD(YX0, GK): yx0w, WRD('X0', GK): x0w, WRD('W', 'B'): ww})
    s5, c5 = inst(w, ph, 'tm2fdrop', {'A': 'E', 'E': "E'", 'F': "F'", 'C': "C'", 'X': 'X0', 'D': DB}, bld5)
    C5a, D5c, B5 = triple_parts(c5)
    POST5 = UP(DB, 'K', 'X0')
    assert C5a == CLN('E', SS, PRE5) and D5c == CLN("E'", SS, POST5), (C5a, D5c)
    # shrink the precondition to ( N ` R ) and present it as the stage-4 post
    s5s = hrssc(w, ph, phm, s5, C5a, D5c, B5, CLN('E', NF('R'), PRE5), clnss(w, ph, 'E', NF('R'), SS, PRE5, fR['nss']))
    s5r, _, _, _ = hrrw(w, ph, s5s, CLN('E', NF('R'), PRE5), D5c, B5,
                        ceq=w.s([clneq(w, ph, 'E', NF('R'), r56, DPM('R'), PRE5)], 'eqcomd', '( %s -> %s = %s )' % (ph, CLN('E', NF('R'), PRE5), CLN('E', NF('R'), DPM('R')))))
    # POST5 = UPD3( D ; I , H_R ; K , X0 ; J , Y_R )
    FIN = UP3('D', 'I', HR_, 'K', 'X0', 'J', YR_)
    cm2 = upc(w, ph, U1, 'J', YR_, 'K', 'X0', tv, u1cl, njk, jj, fR['yw'], kk, x0w)
    assert concl(w, ph, cm2) == '%s = %s' % (POST5, FIN), concl(w, ph, cm2)
    s5f, _, _, _ = hrrw(w, ph, s5r, CLN('E', NF('R'), DPM('R')), D5c, B5, deq=clneq(w, ph, "E'", SS, cm2, POST5, FIN))
    tall = hrseq(w, ph, phm, s1234, s5f, C0, CLN('E', NF('R'), DPM('R')), CLN("E'", SS, FIN), N1234, B5)
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    bound(w, ph, phm, tall, C0, CLN("E'", SS, FIN), '( %s + %s )' % (N1234, B5), "( ( R x. ( T' + 4 ) ) + ( ( # ` W ) + 4 ) )",
          {'R': rr, "T'": tt, '( # ` W )': nw}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fml'): tm2fml()
