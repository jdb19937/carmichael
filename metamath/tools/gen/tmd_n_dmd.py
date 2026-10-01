"""T-MD: the shift-down loop of ` divmod ` (TM/MulDiv.lean ` dmDownBody ` , blueprint
6.1 and D8).  One iteration ~ tm2fdmdb : the test (~ tm2lbrt ), ` predNum j s ` as a
hypothesis triple, ` popBit y ` (~ tm2fpopn ), a zero pushed on the quotient ` I `
(~ tm2fpshn ), ` dup y t s ; dup x s t ; cmpFrag t s ` as a triple, ` Frag.ite ` on
` cmp =/= gt ` dispatching (~ tm2lbrt / ~ tm2fbrg , ~ tm2flg ) to the conditional
` dup y t s ; sub x t s x ; incr q s ` triple or to ` skip ` , and ` isZero j s ` as a
triple; the loop ~ tm2fdmdq : ~ tm2hitr over the stack family ` ( P ` i ) ` whose
step equation is a hypothesis (no collapse inside the loop)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
from tmd_f_mulb import brstep, loadcls

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

Z0YP = CC(S1('Z0'), "Y'")


def tm2fdmdb():
    lab = 'tm2fdmdb'
    tree, ph = TREE_DMDB, cj(TREE_DMDB)
    w = W(lab, 'One iteration of the shift-down loop of ` divmod ` (` dmDownBody ` of TM/MulDiv.lean): '
               'the loop test at ` A ` succeeds (~ tm2lbrt ); ` predNum j s ` is a hypothesis triple from '
               '` B0 ` to ` B\' ` leaving the counter ` Q\' ` on ` I\' ` (T7: ~ tm2fprdn ); ` popBit y ` at '
               '` B\' ` removes the divisor\'s low zero (~ tm2fpopn , ` sh := sh / 2 ` ); a zero is pushed on '
               'the quotient ` I ` (~ tm2fpshn ); ` dup y t s ; dup x s t ; cmpFrag t s ` is a triple from '
               '` D0 ` to ` E0 ` (T7: ~ tm2fdup twice, ~ tm2fcmp ); ` Frag.ite ` at ` E0 ` on ` cmp =/= gt ` '
               'runs ` dup y t s ; sub x t s x ; incr q s ` --- a triple from ` B1_ ` to ` G0 ` leaving the '
               'remainder ` X\' ` on ` K ` and the quotient ` H\' ` on ` I ` (T7: ~ tm2fdup , ~ tm2fsubx , '
               '~ tm2fincr ) --- or ` skip ` at ` E" ` (~ tm2fbrg , ~ tm2flg ) with the stacks unchanged; '
               '` isZero j s ` is a triple from ` G0 ` back to ` A ` into the class ` N\' ` (T7: ~ tm2fisz ).  '
               'Lean: ` dmDownBody_runs ` ; the two cases of the ite are the disjunction (blueprint D4).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, b0l, bpl, bql, d0l, e0l, b1l, eql, g0l = [c[LAB(x)] for x in ('A', 'B0', "B'", 'B"', 'D0', 'E0', 'B1_', 'E"', 'G0')]
    kk, jj, ii, ip = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG], c["I' e. %s" % DG]
    nkj, nki, nkip, nji, njip, niip = [c[x] for x in ('K =/= J', 'K =/= I', "K =/= I'", 'J =/= I', "J =/= I'", "I =/= I'")]
    c0t, ct, lpt, ff, qq = c[CTY('C0')], c[CTY('C')], c[LTY("L'")], c[RTY('F', 'J')], c[STMT('Q')]
    z0j, z0i = c['Z0 e. %s' % GJ], c['Z0 e. %s' % GI]
    dd, dje = c[STKD('D')], c['( D ` J ) = %s' % Z0YP]
    qpw, ypw, xpw, hpw = c[WRD("Q'", GIP)], c[WRD("Y'", GJ)], c[WRD("X'", GK)], c[WRD("H'", GI)]
    t1c, t2c, t3c, t4c, le1 = c['T1 e. NN0'], c['T" e. NN0'], c['T0 e. NN0'], c["T' e. NN0"], c['1 <_ T0']
    nss, n1s, n2s, n3s, nps = c[SSS('N')], c[SSS('N1')], c[SSS('N"')], c[SSS('N0')], c[SSS("N'")]
    ht, hpb = c[HT('N')], c[HPB('N1', 'Z0', 'N"')]
    tr1, tr2, tr4, disj = c[TRIP_D1], c[TRIP_D2], c[TRIP_D4], c[DISJ_DL]
    meqA, meqBp, meqBq, meqE0, meqEq = [c[MEQ(a, s)] for a, s in (('A', STM_DT), ("B'", STM_DPB), ('B"', STM_DPZ), ('E0', STM_DI), ('E"', STM_DSK))]
    sss = w.s([], 'ssid', '%s C_ %s' % (SS, SS)); sssa = w.s([sss], 'a1i', '( %s -> %s C_ %s )' % (ph, SS, SS))
    gb1, geq = gotocl(w, ph, tv, 'B1_', b1l), gotocl(w, ph, tv, 'E"', eql)
    # ---- stage 1: the loop test at A
    C0 = CLN('A', 'N', 'D'); C1 = CLN('B0', 'N', 'D')
    t1s = brstep(w, ph, 'tm2lbrt', phm, meqA, al, b0l, dd, c0t, qq, nss, ht, 'A', 'B0', 'N', 'D')
    # ---- stage 2: predNum, the triple
    C2 = CLN("B'", 'N1', D1D)
    t12 = hrseq(w, ph, phm, t1s, tr1, C0, C1, C2, '1', 'T1')
    N2 = '( 1 + T1 )'
    # ---- stage 3: popBit on J at B' from N1 into N"
    d1cl = updcl(w, ph, 'D', "I'", "Q'", tv, dd, ip, qpw)
    qpv = elv(w, ph, qpw, "Q'")
    d1j = updnv(w, ph, 'D', "I'", "Q'", 'J', tv, dd, ip, qpv, jj, njip)
    d1je = w.s([d1j, dje], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D1D, Z0YP))
    bld3 = bldr(w, ph, c, phm, {STKD(D1D): d1cl, '( %s ` J ) = %s' % (D1D, Z0YP): d1je})
    s3, c3 = inst(w, ph, 'tm2fpopn', {'A': "B'", 'E': 'B"', 'K': 'J', 'Z': 'Z0', 'X': "Y'", 'N': 'N1', "N'": 'N"', 'D': D1D}, bld3)
    C3a, D3c, B3 = triple_parts(c3)
    assert C3a == C2 and D3c == CLN('B"', 'N"', D2D), (C3a, D3c)
    t123 = hrseq(w, ph, phm, t12, s3, C0, C2, D3c, N2, '1')
    N3 = '( %s + 1 )' % N2
    # ---- stage 4: push Z0 on I at B" (class N")
    d2cl = updcl(w, ph, D1D, 'J', "Y'", tv, d1cl, jj, ypw)
    bld4 = bldr(w, ph, c, phm, {STKD(D2D): d2cl})
    s4, c4 = inst(w, ph, 'tm2fpshn', {'A': 'B"', 'E': 'D0', 'K': 'I', 'Z': 'Z0', 'N': 'N"', 'D': D2D}, bld4)
    C4a, D4c, B4 = triple_parts(c4)
    D3x = UP(D2D, 'I', CC(S1('Z0'), '( %s ` I )' % D2D))
    assert C4a == D3c and D4c == CLN('D0', 'N"', D3x), (C4a, D4c)
    ypv = elv(w, ph, ypw, "Y'")
    nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    d2i = updnv(w, ph, D1D, 'J', "Y'", 'I', tv, d1cl, jj, ypv, ii, nij)
    d1i = updnv(w, ph, 'D', "I'", "Q'", 'I', tv, dd, ip, qpv, ii, niip)
    d2ie = w.s([d2i, d1i], 'eqtrd', '( %s -> ( %s ` I ) = ( D ` I ) )' % (ph, D2D))
    r4, D3n = w.rewrite(D3x, {'( %s ` I )' % D2D: ('( D ` I )', d2ie)}, ph)
    assert D3n == D3D, D3n
    s4r, _, _, _ = hrrw(w, ph, s4, C4a, D4c, B4, deq=clneq(w, ph, 'D0', 'N"', r4, D3x, D3D))
    C4 = CLN('D0', 'N"', D3D)
    t1234 = hrseq(w, ph, phm, t123, s4r, C0, D3c, C4, N3, '1')
    N4 = '( %s + 1 )' % N3
    # ---- stage 5: dup, dup, cmpFrag, the triple
    C5 = CLN('E0', 'N0', D3D)
    t5 = hrseq(w, ph, phm, t1234, tr2, C0, C4, C5, N4, 'T"')
    N5 = '( %s + T" )' % N4
    # ---- stage 6: the ite at E0
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    z0diw = ccatw(w, ph, s1w(w, ph, z0i, 'Z0', GI), diw, S1('Z0'), '( D ` I )', GI)
    d3cl = updcl(w, ph, D2D, 'I', Z0DI, tv, d2cl, ii, z0diw)
    C6 = CLN('G0', SS, D7D)
    hld = loadcls(w, ph, "L'", lpt, n3s, Nc='N0')
    cases = []
    # the subtract case
    pha = '( %s /\\ ( %s /\\ %s ) )' % (ph, HTC('N0'), TRIP_D3)
    A_ = Lifter(w, pha)
    cs = w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (pha, HTC('N0'), TRIP_D3))
    tsa = w.s([cs], 'simpld', '( %s -> %s )' % (pha, HTC('N0')))
    tra = w.s([cs], 'simprd', '( %s -> %s )' % (pha, TRIP_D3))
    ta = brstep(w, pha, 'tm2lbrt', A_(phm, PHM), A_(meqE0, MEQ('E0', STM_DI)), A_(e0l, LAB('E0')), A_(b1l, LAB('B1_')), A_(d3cl, STKD(D3D)),
                A_(ct, CTY('C')), A_(geq, STMT(GT('E"'))), A_(n3s, SSS('N0')), tsa, 'E0', 'B1_', 'N0', D3D)
    tab = hrseq(w, pha, A_(phm, PHM), ta, tra, C5, CLN('B1_', 'N0', D3D), C6, '1', 'T0')
    cases.append(tab)
    # the skip case
    EQS = '( X\' = ( D ` K ) /\\ H\' = %s )' % Z0DI
    phb = '( %s /\\ ( %s /\\ %s ) )' % (ph, HTCF('N0'), EQS)
    B_ = Lifter(w, phb)
    cs2 = w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (phb, HTCF('N0'), EQS))
    tsb = w.s([cs2], 'simpld', '( %s -> %s )' % (phb, HTCF('N0')))
    eqs = w.s([cs2], 'simprd', '( %s -> %s )' % (phb, EQS))
    xe = w.s([eqs], 'simpld', "( %s -> X' = ( D ` K ) )" % phb)
    he = w.s([eqs], 'simprd', "( %s -> H' = %s )" % (phb, Z0DI))
    tb = brstep(w, phb, 'tm2fbrg', B_(phm, PHM), B_(meqE0, MEQ('E0', STM_DI)), B_(e0l, LAB('E0')), B_(eql, LAB('E"')), B_(d3cl, STKD(D3D)),
                B_(ct, CTY('C')), B_(gb1, STMT(GT('B1_'))), B_(n3s, SSS('N0')), tsb, 'E0', 'E"', 'N0', D3D)
    tl = applylem(w, phb, 'tm2flg', ((B_(phm, PHM), B_(meqEq, MEQ('E"', STM_DSK))), (B_(eql, LAB('E"')), B_(g0l, LAB('G0')), B_(d3cl, STKD(D3D))),
                                     (B_(lpt, LTY("L'")), (B_(n3s, SSS('N0')), B_(sssa, '%s C_ %s' % (SS, SS))), B_(hld, 'A. r e. N0 ( L\' ` r ) e. %s' % SS))),
                  TRI(CLN('E"', 'N0', D3D), CLN('G0', SS, D3D), '1'))
    # D3D = D7D under phb: ( D3D ` K ) = ( D ` K ) = X' and ( D3D ` I ) = Z0DI = H'
    tvb, ddb, d1clb, d2clb, d3clb = B_(tv, 'T e. V'), B_(dd, STKD('D')), B_(d1cl, STKD(D1D)), B_(d2cl, STKD(D2D)), B_(d3cl, STKD(D3D))
    kkb, jjb, iib, ipb = B_(kk, 'K e. %s' % DG), B_(jj, 'J e. %s' % DG), B_(ii, 'I e. %s' % DG), B_(ip, "I' e. %s" % DG)
    k1 = updnv(w, phb, D2D, 'I', Z0DI, 'K', tvb, d2clb, iib, B_(elv(w, ph, z0diw, Z0DI), '%s e. _V' % Z0DI), kkb, B_(nki, 'K =/= I'))
    k2 = updnv(w, phb, D1D, 'J', "Y'", 'K', tvb, d1clb, jjb, B_(ypv, "Y' e. _V"), kkb, B_(nkj, 'K =/= J'))
    k3 = updnv(w, phb, 'D', "I'", "Q'", 'K', tvb, ddb, ipb, B_(qpv, "Q' e. _V"), kkb, B_(nkip, "K =/= I'"))
    k123 = w.s([w.s([k1, k2], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` K ) )' % (phb, D3D, D1D)), k3], 'eqtrd', '( %s -> ( %s ` K ) = ( D ` K ) )' % (phb, D3D))
    d3k = w.s([k123, w.s([xe], 'eqcomd', "( %s -> ( D ` K ) = X' )" % phb)], 'eqtrd', "( %s -> ( %s ` K ) = X' )" % (phb, D3D))
    u1 = upidv(w, phb, D3D, 'K', "X'", d3k, tvb, d3clb, kkb)
    i1 = updkv(w, phb, D2D, 'I', Z0DI, tvb, d2clb, iib, B_(elv(w, ph, z0diw, Z0DI), '%s e. _V' % Z0DI))
    d3i = w.s([i1, w.s([he], 'eqcomd', "( %s -> %s = H' )" % (phb, Z0DI))], 'eqtrd', "( %s -> ( %s ` I ) = H' )" % (phb, D3D))
    u2 = upidv(w, phb, D3D, 'I', "H'", d3i, tvb, d3clb, iib)
    r1, m1 = w.rewrite(D7D, {UP(D3D, 'K', "X'"): (D3D, u1)}, phb)
    assert m1 == UP(D3D, 'I', "H'"), m1
    r12 = w.s([r1, u2], 'eqtrd', '( %s -> %s = %s )' % (phb, D7D, D3D))
    r12c = w.s([r12], 'eqcomd', '( %s -> %s = %s )' % (phb, D3D, D7D))
    tl2, _, _, _ = hrrw(w, phb, tl, CLN('E"', 'N0', D3D), CLN('G0', SS, D3D), '1', deq=clneq(w, phb, 'G0', SS, r12c, D3D, D7D))
    tbl = hrseq(w, phb, B_(phm, PHM), tb, tl2, C5, CLN('E"', 'N0', D3D), C6, '1', '1')
    tblr = bound(w, phb, B_(phm, PHM), tbl, C5, C6, '( 1 + 1 )', '( 1 + T0 )', {'T0': B_(t3c, 'T0 e. NN0')}, hyps=[B_(le1, '1 <_ T0')])
    cases.append(tblr)
    both = w.s(cases, 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ_DL, TRI(C5, C6, '( 1 + T0 )')))
    t6s = w.s([disj, both], 'mpdan', '( %s -> %s )' % (ph, TRI(C5, C6, '( 1 + T0 )')))
    t6 = hrseq(w, ph, phm, t5, t6s, C0, C5, C6, N5, '( 1 + T0 )')
    N6 = '( %s + ( 1 + T0 ) )' % N5
    # ---- stage 7: isZero, the triple
    C7 = CLN('A', "N'", D7D)
    t7 = hrseq(w, ph, phm, t6, tr4, C0, C6, C7, N6, "T'")
    N7 = "( %s + T' )" % N6
    # ---- stage 8: D7D collapses to POST_DMDB
    cm = upc(w, ph, D3D, 'K', "X'", 'I', "H'", tv, d3cl, nki, kk, xpw, ii, hpw)
    u2s = up2(w, ph, D2D, 'I', Z0DI, "H'", tv, d2cl, ii, z0diw, hpw)
    MID = UP(UP(D3D, 'I', "H'"), 'K', "X'")
    ps1, mid = w.rewrite(D7D, {D7D: (MID, cm)}, ph)
    assert mid == MID, mid
    ps2, fin = w.rewrite(MID, {UP(D3D, 'I', "H'"): (UP(D2D, 'I', "H'"), u2s)}, ph)
    assert fin == POST_DMDB, fin
    ps = w.s([ps1, ps2], 'eqtrd', '( %s -> %s = %s )' % (ph, D7D, POST_DMDB))
    t8, _, _, _ = hrrw(w, ph, t7, C0, C7, N7, deq=clneq(w, ph, 'A', "N'", ps, D7D, POST_DMDB))
    bound(w, ph, phm, t8, C0, CLN('A', "N'", POST_DMDB), N7, TD4, {'T1': t1c, 'T"': t2c, 'T0': t3c, "T'": t4c}, qed=True)
    return w.run()


IFD = '( j e. NN0 |-> %s )' % CLN('A', NF('j'), PF('j'))
BODYD = CLN('A', NF('j'), PF('j'))


def tm2fdmdq():
    lab = 'tm2fdmdq'
    tree, ph = TREE_DMDQ, cj(TREE_DMDQ)
    w = W(lab, 'The shift-down loop of ` divmod ` from its test label ` A ` : the stacks after ` i ` '
               'iterations are the family ` ( P ` i ) ` , each iteration ~ tm2fdmdb at ` D := ( P ` i ) ` '
               'with its triples as hypotheses and the step equation ` ( P ` ( i + 1 ) ) = ... ` '
               '(the four-stack update of the iteration, blueprint D8; T7 discharges it by ~ tm2stkup8 '
               'once, generically in ` i ` ); ~ tm2hitr over ` ( 0 ..^ R ) ` .  Lean: ` Frag.loop_runs ` '
               'at ` DmDownInv ` in ` divmodCore_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, el = c[LAB('A')], c[LAB('E')]
    rr, fam, hyps = c['R e. NN0'], c[FAM_DQ], c[HYPS_DQ]
    t1c, t2c, t3c, t4c = c['T1 e. NN0'], c['T" e. NN0'], c['T0 e. NN0'], c["T' e. NN0"]
    meqA = c[MEQ('A', STM_DTE)]
    ge = gotocl(w, ph, tv, 'E', el)

    def famat(ph2, X, xfz, Lf):
        st, _ = inst_v(w, ph2, Lf(fam, FAM_DQ), cj(FAMB_DQ('i')), 'i', X, xfz)
        cx = Ctx(w, ph2, FAMB_DQ(X), root=st)
        return dict(xw=cx[WRD(XF(X), GK)], yw=cx[WRD(YF(X), GJ)], hw=cx[WRD(HF(X), GI)], qw=cx[WRD(QF(X), GIP)],
                    pst=cx[STKD(PF(X))], nss=cx[SSS(NF(X))])

    def fzmem(ph2, X, xnn, xle, rr2):
        return w.s([w.s([xnn, rr2, xle], '3jca', '( %s -> ( %s e. NN0 /\\ R e. NN0 /\\ %s <_ R ) )' % (ph2, X, X)),
                    w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... R ) )' % (ph2, X))
    # ---------------- the iteration at k
    pk = '( %s /\\ k e. ( 0 ..^ R ) )' % ph
    Lk = Lifter(w, pk)
    kin = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ R ) )' % pk)
    kfz = w.s([kin, w.inst('elfzofz')], 'syl', '( %s -> k e. ( 0 ... R ) )' % pk)
    k1fz = w.s([kin, w.inst('fzofzp1')], 'syl', '( %s -> ( k + 1 ) e. ( 0 ... R ) )' % pk)
    knn = w.s([kin, w.inst('elfzonn0')], 'syl', '( %s -> k e. NN0 )' % pk)
    k1nn = w.s([knn, w.inst('peano2nn0')], 'syl', '( %s -> ( k + 1 ) e. NN0 )' % pk)
    fk = famat(pk, 'k', kfz, Lk)
    fk1 = famat(pk, '( k + 1 )', k1fz, Lk)
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS_DQ), cj(HYP_DQ_TREE('i')), 'i', 'k', kin)
    ck = Ctx(w, pk, HYP_DQ_TREE('k'), root=hyk)
    K1 = '( k + 1 )'
    t1, t2, t4, dj, post = DMD_AT('k')
    PJE = '( %s ` J ) = %s' % (PF('k'), CC(S1('Z0'), YF(K1)))
    STEP = '%s = %s' % (PF(K1), post)
    pje, step = ck[PJE], ck[STEP]
    htk, hpbk = ck[HT(NF('k'))], ck[HPB(N1F('k'), 'Z0', N2F('k'))]
    n1s, n2s, n3s = ck[SSS(N1F('k'))], ck[SSS(N2F('k'))], ck[SSS(N3F('k'))]
    tr1, tr2, tr4, djs = ck[t1], ck[t2], ck[t4], ck[dj]
    MAPK = dict(DMD_MAP('k'), Q=GT('E'))
    instk = ren(TREE_DMDB, MAPK)
    derived = {STKD(PF('k')): fk['pst'], PJE: pje,
               WRD(QF(K1), GIP): fk1['qw'], WRD(YF(K1), GJ): fk1['yw'], WRD(XF(K1), GK): fk1['xw'], WRD(HF(K1), GI): fk1['hw'],
               SSS(NF('k')): fk['nss'], SSS(N1F('k')): n1s, SSS(N2F('k')): n2s, SSS(N3F('k')): n3s, SSS(NF(K1)): fk1['nss'],
               HT(NF('k')): htk, HPB(N1F('k'), 'Z0', N2F('k')): hpbk, t1: tr1, t2: tr2, t4: tr4, dj: djs,
               STMT(GT('E')): Lk(ge, STMT(GT('E'))), MEQ('A', STM_DTE): Lk(meqA, MEQ('A', STM_DTE))}
    def look(t):
        if t in derived:
            return derived[t]
        return Lk(c[t], t)
    CLk, CLk1 = CLN('A', NF('k'), PF('k')), CLN('A', NF(K1), PF(K1))
    trik = applylem(w, pk, 'tm2fdmdb', leafsteps(instk, look), TRI(CLk, CLN('A', NF(K1), post), TD4))
    stepc = w.s([step], 'eqcomd', '( %s -> %s = %s )' % (pk, post, PF(K1)))
    trik2, _, _, _ = hrrw(w, pk, trik, CLk, CLN('A', NF(K1), post), TD4, deq=clneq(w, pk, 'A', NF(K1), stepc, post, PF(K1)))
    jvk = ifval(w, pk, IFD, BODYD, 'k', knn, CLk, clnex(w, pk, 'A', NF('k'), PF('k')))
    jvk1 = ifval(w, pk, IFD, BODYD, K1, k1nn, CLk1, clnex(w, pk, 'A', NF(K1), PF(K1)))
    trik3, _, _, _ = hrrw(w, pk, trik2, CLk, CLk1, TD4,
                          ceq=w.s([jvk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (pk, CLk, IFD)),
                          deq=w.s([jvk1], 'eqcomd', '( %s -> %s = ( %s ` ( k + 1 ) ) )' % (pk, CLk1, IFD)))
    HYPI = 'A. k e. ( 0 ..^ R ) %s' % TRI('( %s ` k )' % IFD, '( %s ` ( k + 1 ) )' % IFD, TD4)
    hypi = w.s([trik3], 'ralrimiva', '( %s -> %s )' % (ph, HYPI))
    # ---------------- tm2hitr
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ R )' % ph)
    z0fz = fzmem(ph, '0', z0a, ge0, rr)
    f0 = famat(ph, '0', z0fz, lambda st, f: st)
    CL0, CLR = CLN('A', NF('0'), PF('0')), CLN('A', NF('R'), PF('R'))
    jv0 = ifval(w, ph, IFD, BODYD, '0', z0a, CL0, clnex(w, ph, 'A', NF('0'), PF('0')))
    jvR = ifval(w, ph, IFD, BODYD, 'R', rr, CLR, clnex(w, ph, 'A', NF('R'), PF('R')))
    ss0 = cfgcl(w, ph, 'A', NF('0'), PF('0'), tv, al, f0['nss'], f0['pst'])
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IFD, CFG_T))
    tdn = nn0cl(w, ph, TD4, {'T1': t1c, 'T"': t2c, 'T0': t3c, "T'": t4c})
    pj = w.s([ss0j, tdn], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) )' % (ph, IFD, CFG_T, TD4))
    ant = w.s([phm, pj, hypi], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) )' % (ph, PHM, IFD, CFG_T, TD4, HYPI))
    RUN = TRI('( %s ` 0 )' % IFD, '( %s ` R )' % IFD, '( R x. %s )' % TD4)
    itr0 = w.s([rr, w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IFD, CFG_T, TD4, HYPI, RUN))
    run = w.s([itr0, ant], 'mpd', '( %s -> %s )' % (ph, RUN))
    hrrw(w, ph, run, '( %s ` 0 )' % IFD, '( %s ` R )' % IFD, '( R x. %s )' % TD4, ceq=jv0, deq=jvR, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fdmdb'): tm2fdmdb()
    if want('tm2fdmdq'): tm2fdmdq()
