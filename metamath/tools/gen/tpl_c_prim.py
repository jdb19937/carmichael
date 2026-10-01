"""T-PL: the fragments of TM/PrimTD.lean at the generic level (blueprint D1-D5):
~ tm2fpgb (` primeGoBody ` , the three-way body), ~ tm2fpgq (its loop, ~ tm2floopu
with ~ tm2fpgb at every iteration), ~ tm2fpg (` primeGoF `), ~ tm2fipt
(` isPrimeTDF `), ~ tm2fdot (` divOutTest `), ~ tm2fdo (` divOutF `), ~ tm2fsg
(` smoothGoF ` , the Sigma loop), ~ tm2fstd (` smoothTDF `).  Every composite
call is a hypothesis triple; the theorems execute the tests, the loads and the
loops."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def L_(w, ph):
    """a lifter taking (step, formula) pairs"""
    Lk = Lifter(w, ph)
    return lambda p: Lk(p[0], p[1])


def tm2fpgb():
    lab = 'tm2fpgb'
    tree, ph = TREE_PGB, cj(TREE_PGB)
    w = W(lab, 'One iteration of the trial-division loop ` primeGoBody ` (TM/PrimTD.lean) from the body entry '
               '` B0 ` back to the test ` A ` : ` dup ; dup ; mulC ; dup ; cmpFrag ` is a hypothesis triple into the '
               'class ` N1 ` (T7: ~ tm2fdup , ~ tm2fml + ~ tm2fcan , ~ tm2fcmp ); ` Frag.ite ` at ` B\' ` on '
               '` cmp = lt ` either loads the result (~ tm2lbrt , ~ tm2flg ; ` d * d > m ` , prime) or runs '
               '` dup ; dup ; modC ; isZero ; dropNum ` as a triple into ` N" ` (~ tm2fmod ); ` Frag.ite ` at ` E\' ` '
               'on ` flag ` either loads the result (` d | m ` , composite) or runs ` incr xd ; predNum xf ; isZero xf ` '
               'as a triple into ` N0 ` at the stacks ` D\' ` and loads ` carry := fuel =/= 0 ` .  The three exits are '
               'the nested disjunction (blueprint D5), the post stacks ` D\' ` are ` D ` in the two stopping cases.  '
               'Lean: ` primeGoBody_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    meqBp, meqBq, meqEp, meqEq, meqAp = [(c[MEQ(a, s)], MEQ(a, s)) for a, s in
                                         (("B'", BR('C', 'B"', 'E0')), ('B"', LD('L', 'A')), ("E'", BR("C'", 'E"', 'A0')),
                                          ('E"', LD("L'", 'A')), ("A'", LD('L"', 'A')))]
    lb = {x: (c[LAB(x)], LAB(x)) for x in ('B0', "B'", 'B"', 'E0', "E'", 'E"', 'A0', "A'", 'A')}
    ct, cpt = (c[CTY('C')], CTY('C')), (c[CTY("C'")], CTY("C'"))
    lt, lpt, lqt = [(c[LTY(x)], LTY(x)) for x in ('L', "L'", 'L"')]
    dd, dpd = (c[STKD('D')], STKD('D')), (c[STKD("D'")], STKD("D'"))
    t1c, t2c, t3c = [(c[x], x) for x in ('T1 e. NN0', 'T" e. NN0', 'T0 e. NN0')]
    ns = {x: (c[SSS(x)], SSS(x)) for x in ('N', 'N1', 'N"', 'N0', "N'")}
    trip1, disj = c[TRIP_PG1], c[DISJ_PG]
    P = (phm, PHM)
    gbq = (gotocl(w, ph, tv, 'B"', lb['B"'][0]), STMT(GT('B"')))
    ge0 = (gotocl(w, ph, tv, 'E0', lb['E0'][0]), STMT(GT('E0')))
    geq = (gotocl(w, ph, tv, 'E"', lb['E"'][0]), STMT(GT('E"')))
    ga0 = (gotocl(w, ph, tv, 'A0', lb['A0'][0]), STMT(GT('A0')))
    C_B0, C_Bp, C_A = CLN('B0', 'N', 'D'), CLN("B'", 'N1', 'D'), CLN('A', "N'", "D'")
    MB = '( ( T" + T0 ) + 3 )'

    def stopcase(pha, cs, Bl, Ll, Al, meqB, meqL, Nc, cct, ltt, Ecl):
        """the branch at Bl succeeds on Nc, the load at Ll lands in N', D' = D; Ecl the other branch's goto"""
        L = L_(w, pha)
        cx = Ctx(w, pha, (HT(Nc, cct[1].split(' e. ')[0]), HLD(Nc, "N'", ltt[1].split(' e. ')[0]), "D' = D"), root=cs)
        ht = cx[HT(Nc, cct[1].split(' e. ')[0])]
        hl = cx[HLD(Nc, "N'", ltt[1].split(' e. ')[0])]
        de = cx["D' = D"]
        b = brstep(w, pha, 'tm2lbrt', L(P), L(meqB), L(lb[Bl]), L(lb[Ll]), L(dd), L(cct), L(Ecl), L(ns[Nc]), ht, Bl, Ll, Nc, 'D')
        l = ldstep(w, pha, L(P), L(meqL), L(lb[Ll]), L(lb['A']), L(dd), L(ltt), L(ns[Nc]), L(ns["N'"]), hl, Ll, 'A', Nc, "N'", 'D')
        s = hrseq(w, pha, L(P), b, l, CLN(Bl, Nc, 'D'), CLN(Ll, Nc, 'D'), CLN('A', "N'", 'D'), '1', '1')
        dec = w.s([de], 'eqcomd', "( %s -> D = D' )" % pha)
        sr, _, _, _ = hrrw(w, pha, s, CLN(Bl, Nc, 'D'), CLN('A', "N'", 'D'), '( 1 + 1 )', deq=clneq(w, pha, 'A', "N'", dec, 'D', "D'"))
        return sr, L

    def caseA(pha, cs):
        sr, L = stopcase(pha, cs, "B'", 'B"', 'A', meqBp, meqBq, 'N1', ct, lt, ge0)
        return bound0(w, pha, L(P), sr, C_Bp, C_A, '( 1 + 1 )', MB, {'T"': L(t2c), 'T0': L(t3c)})

    def caseB(phb, cs):
        L = L_(w, phb)
        cx = Ctx(w, phb, (HTF('N1', 'C'), TRIP_PG2, DISJ_PG2), root=cs)
        htf1, tr2, dj2 = cx[HTF('N1', 'C')], cx[TRIP_PG2], cx[DISJ_PG2]
        b = brstep(w, phb, 'tm2fbrg', L(P), L(meqBp), L(lb["B'"]), L(lb['E0']), L(dd), L(ct), L(gbq), L(ns['N1']), htf1, "B'", 'E0', 'N1', 'D')
        C_Ep = CLN("E'", 'N"', 'D')
        s12 = hrseq(w, phb, L(P), b, tr2, C_Bp, CLN('E0', 'N1', 'D'), C_Ep, '1', 'T"')
        MB2 = '( T0 + 2 )'
        # the steps the inner cases lift, already at phb
        lb2 = {x: (L(lb[x]), lb[x][1]) for x in ("E'", 'E"', 'A0', "A'", 'A')}
        ns2 = {x: (L(ns[x]), ns[x][1]) for x in ('N"', 'N0', "N'")}
        P2, dd2, dpd2 = (L(P), PHM), (L(dd), dd[1]), (L(dpd), dpd[1])
        cpt2, lpt2, lqt2, t3c2 = (L(cpt), cpt[1]), (L(lpt), lpt[1]), (L(lqt), lqt[1]), (L(t3c), t3c[1])
        meqEp2, meqEq2, meqAp2 = (L(meqEp), meqEp[1]), (L(meqEq), meqEq[1]), (L(meqAp), meqAp[1])
        geq2, ga02 = (L(geq), geq[1]), (L(ga0), ga0[1])

        def caseB1(phc, cs2):
            L2 = L_(w, phc)
            cx2 = Ctx(w, phc, (HT('N"', "C'"), HLD('N"', "N'", "L'"), "D' = D"), root=cs2)
            ht, hl, de = cx2[HT('N"', "C'")], cx2[HLD('N"', "N'", "L'")], cx2["D' = D"]
            b1 = brstep(w, phc, 'tm2lbrt', L2(P2), L2(meqEp2), L2(lb2["E'"]), L2(lb2['E"']), L2(dd2), L2(cpt2), L2(ga02), L2(ns2['N"']), ht, "E'", 'E"', 'N"', 'D')
            l1 = ldstep(w, phc, L2(P2), L2(meqEq2), L2(lb2['E"']), L2(lb2['A']), L2(dd2), L2(lpt2), L2(ns2['N"']), L2(ns2["N'"]), hl, 'E"', 'A', 'N"', "N'", 'D')
            s1 = hrseq(w, phc, L2(P2), b1, l1, C_Ep, CLN('E"', 'N"', 'D'), CLN('A', "N'", 'D'), '1', '1')
            dec = w.s([de], 'eqcomd', "( %s -> D = D' )" % phc)
            sr, _, _, _ = hrrw(w, phc, s1, C_Ep, CLN('A', "N'", 'D'), '( 1 + 1 )', deq=clneq(w, phc, 'A', "N'", dec, 'D', "D'"))
            return bound0(w, phc, L2(P2), sr, C_Ep, C_A, '( 1 + 1 )', MB2, {'T0': L2(t3c2)})

        def caseB2(phd, cs2):
            L2 = L_(w, phd)
            cx2 = Ctx(w, phd, (HTF('N"', "C'"), TRIP_PG3, HLD('N0', "N'", 'L"')), root=cs2)
            htf2, tr3, hl3 = cx2[HTF('N"', "C'")], cx2[TRIP_PG3], cx2[HLD('N0', "N'", 'L"')]
            b2 = brstep(w, phd, 'tm2fbrg', L2(P2), L2(meqEp2), L2(lb2["E'"]), L2(lb2['A0']), L2(dd2), L2(cpt2), L2(geq2), L2(ns2['N"']), htf2, "E'", 'A0', 'N"', 'D')
            s1 = hrseq(w, phd, L2(P2), b2, tr3, C_Ep, CLN('A0', 'N"', 'D'), CLN("A'", 'N0', "D'"), '1', 'T0')
            l3 = ldstep(w, phd, L2(P2), L2(meqAp2), L2(lb2["A'"]), L2(lb2['A']), L2(dpd2), L2(lqt2), L2(ns2['N0']), L2(ns2["N'"]), hl3, "A'", 'A', 'N0', "N'", "D'")
            s2 = hrseq(w, phd, L2(P2), s1, l3, C_Ep, CLN("A'", 'N0', "D'"), C_A, '( 1 + T0 )', '1')
            return bound0(w, phd, L2(P2), s2, C_Ep, C_A, '( ( 1 + T0 ) + 1 )', MB2, {'T0': L2(t3c2)})

        inner = casesplit(w, phb, dj2, DISJ_PG2, CASE_PGB1, CASE_PGB2, caseB1, caseB2, TRI(C_Ep, C_A, MB2))
        s = hrseq(w, phb, L(P), s12, inner, C_Bp, C_Ep, C_A, '( 1 + T" )', MB2)
        return bound0(w, phb, L(P), s, C_Bp, C_A, '( ( 1 + T" ) + %s )' % MB2, MB, {'T"': L(t2c), 'T0': L(t3c)})

    s = casesplit(w, ph, disj, DISJ_PG, CASE_PGA, CASE_PGB, caseA, caseB, TRI(C_Bp, C_A, MB))
    tot = hrseq(w, ph, phm, trip1, s, C_B0, C_Bp, C_A, 'T1', MB)
    bound0(w, ph, phm, tot, C_B0, C_A, '( T1 + %s )' % MB, TD_PG, {'T1': t1c[0], 'T"': t2c[0], 'T0': t3c[0]}, qed=True)
    return w.run()


def ralk2i(w, ph, hyp_k, body_k, body_i):
    """( ph -> A. i e. ( 0 ..^ R ) body_i ) from hyp_k : ( ph -> A. k e. ( 0 ..^ R ) body_k ) (cbvralvw)"""
    cg, new = W.wcongr(w, body_k, {'k': 'i'}, 'k = i', {'k': w.s([], 'id', '( k = i -> k = i )')})
    assert new == body_i, (new[:100], body_i[:100])
    cb = w.s([cg], 'cbvralvw', '( A. k e. ( 0 ..^ R ) %s <-> A. i e. ( 0 ..^ R ) %s )' % (body_k, body_i))
    return w.s([hyp_k, cb], 'sylib', '( %s -> A. i e. ( 0 ..^ R ) %s )' % (ph, body_i))


def tm2fpgq():
    lab = 'tm2fpgq'
    tree, ph = TREE_PGQ, cj(TREE_PGQ)
    w = W(lab, 'The trial-division loop ` primeGoF ` from its test label ` A ` to the exit ` E ` : ~ tm2floopu over '
               'the class family ` ( N ` i ) ` and the stack family ` ( P ` i ) ` , each iteration ~ tm2fpgb with '
               'its triples and its three-way disjunction at ` i ` (blueprint D4, D5).  Lean: ` Frag.loop_runs ` '
               'at ` PGInv ` in ` primeGoF_le_B ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    fam, hyps, rr = c[FAM_L], c[HYPS_PGQ], c['R e. NN0']
    t1c, t2c, t3c = c['T1 e. NN0'], c['T" e. NN0'], c['T0 e. NN0']
    pk = '( %s /\\ k e. ( 0 ..^ R ) )' % ph
    Lk = Lifter(w, pk)
    kin, kfz, k1fz, knn, k1nn = kfacts(w, pk)
    K1 = '( k + 1 )'
    fk = famat(w, pk, Lk(fam, FAM_L), 'k', kfz)
    fk1 = famat(w, pk, Lk(fam, FAM_L), K1, k1fz)
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS_PGQ), cj(HYP_PGQ_TREE('i')), 'i', 'k', kin)
    ck = Ctx(w, pk, HYP_PGQ_TREE('k'), root=hyk)
    m = PGQ_MAP('k')
    derived = {SSS(NF('k')): fk['nss'], STKD(PF('k')): fk['pst'], SSS(NF(K1)): fk1['nss'], STKD(PF(K1)): fk1['pst'],
               SSS(N1F('k')): ck[SSS(N1F('k'))], SSS(N2F('k')): ck[SSS(N2F('k'))], SSS(N3F('k')): ck[SSS(N3F('k'))],
               sub(TRIP_PG1, m): ck[sub(TRIP_PG1, m)], sub(DISJ_PG, m): ck[sub(DISJ_PG, m)]}
    def look(t):
        return derived[t] if t in derived else Lk(c[t], t)
    trik = applylem(w, pk, 'tm2fpgb', leafsteps(ren(TREE_PGB, m), look), BODY_L('k', TD_PG))
    htk = ck[HT(NF('k'))]
    pair = w.s([htk, trik], 'jca', '( %s -> ( %s /\\ %s ) )' % (pk, HT(NF('k')), BODY_L('k', TD_PG)))
    body_k = '( %s /\\ %s )' % (HT(NF('k')), BODY_L('k', TD_PG))
    body_i = '( %s /\\ %s )' % (HT(NF('i')), BODY_L('i', TD_PG))
    hypk = w.s([pair], 'ralrimiva', '( %s -> A. k e. ( 0 ..^ R ) %s )' % (ph, body_k))
    hypi = ralk2i(w, ph, hypk, body_k, body_i)
    tdn = nn0cl(w, ph, TD_PG, {'T1': t1c, 'T"': t2c, 'T0': t3c})
    HYPS_U = sub(HYPS_LU, {"T'": TD_PG})
    assert HYPS_U == 'A. i e. ( 0 ..^ R ) %s' % body_i
    extra = {HYPS_U: hypi, '%s e. NN0' % TD_PG: tdn}
    def look2(t):
        return extra[t] if t in extra else c[t]
    concl = sub(CONCL_LOOPU, {"T'": TD_PG})
    assert concl == CONCL_PGQ, (concl, CONCL_PGQ)
    st, txt = jtree(w, ph, leafsteps(ren(TREE_LOOPU, {"T'": TD_PG}), look2))
    w.qed([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ph, concl))
    return w.run()


def tm2fpg():
    lab = 'tm2fpg'
    tree, ph = TREE_PG, cj(TREE_PG)
    w = W(lab, 'The trial-division fragment ` primeGoF ` of TM/PrimTD.lean: ` isZero xf s ` is a hypothesis triple '
               'from ` P0 ` into ` O\' ` (T7: ~ tm2fisz ), ` load\' ( carry := fuel =/= 0 , flag := true ) ` at ` P1 ` '
               'lands in ` ( N ` 0 ) ` (~ tm2flg ), then the loop ~ tm2fpgq .  Lean: the generic core of '
               '` primeGoF_le_B ` ; the class ` ( N ` R ) ` carries the result (T7: ` flag = ( primeGo m d fuel ).1 `).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    fam, rr, uc = c[FAM_L], c['R e. NN0'], c['U e. NN0']
    t1c, t2c, t3c = c['T1 e. NN0'], c['T" e. NN0'], c['T0 e. NN0']
    f0 = famat(w, ph, fam, '0', zmem(w, ph, rr))
    trip0, hld = c[TRIP_PG0], c[HLD("O'", NF('0'), 'L0')]
    C0, C1, C2 = CLN('P0', 'O', PF('0')), CLN('P1', "O'", PF('0')), CLN('A', NF('0'), PF('0'))
    l = ldstep(w, ph, phm, c[MEQ('P1', LD('L0', 'A'))], c[LAB('P1')], c[LAB('A')], f0['pst'], c[LTY('L0')], c[SSS("O'")], f0['nss'], hld,
               'P1', 'A', "O'", NF('0'), PF('0'))
    s01 = hrseq(w, ph, phm, trip0, l, C0, C1, C2, 'U', '1')
    lp = applylem(w, ph, 'tm2fpgq', leafsteps(TREE_PGQ, lambda t: c[t]), CONCL_PGQ)
    CE = CLN('E', NF('R'), PF('R'))
    w.qed([phm, s01, lp], 'syl3anc', '( %s -> %s )' % (ph, TRI(C0, CE, BND_PG)))
    return w.run()


def tm2fipt():
    lab = 'tm2fipt'
    tree, ph = TREE_IPT, cj(TREE_IPT)
    w = W(lab, 'The primality test ` isPrimeTDF ` of TM/PrimTD.lean: ` pushNum s 2 ; dup xm t u ; cmpFrag t s ` is a '
               'hypothesis triple into ` N1 ` with the stacks restored; ` Frag.ite ` at ` B\' ` on ` cmp = lt ` '
               '(` m < 2 `) loads ` flag := false ` (~ tm2lbrt , ~ tm2flg ), otherwise ` pushNum xd 2 ; dup xm xf s ` , '
               '` primeGoF ` (~ tm2fpg ) and ` dropNum xd ; dropNum xf ` are three triples at the stacks each leaves '
               '(~ tm2fbrg dispatches).  The two cases are the disjunction (blueprint D5).  Lean: the generic core of '
               '` isPrimeTDF_le_B ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    P = (phm, PHM)
    meqBp, meqBq = (c[MEQ("B'", BR('C', 'B"', 'E0'))], MEQ("B'", BR('C', 'B"', 'E0'))), (c[MEQ('B"', LD('L', 'E'))], MEQ('B"', LD('L', 'E')))
    lb = {x: (c[LAB(x)], LAB(x)) for x in ('P0', "B'", 'B"', 'E0', "E'", 'E"', 'E')}
    ct, lt = (c[CTY('C')], CTY('C')), (c[LTY('L')], LTY('L'))
    dd = (c[STKD('D')], STKD('D'))
    t1c, t2c, t3c, t4c, le1 = [(c[x], x) for x in ('T1 e. NN0', 'T" e. NN0', 'T0 e. NN0', "T' e. NN0", '1 <_ T"')]
    ns = {x: (c[SSS(x)], SSS(x)) for x in ('N', 'N1', 'N"', 'N0', "N'")}
    trip1, disj = c[TRIP_IP1], c[DISJ_IP]
    gbq = (gotocl(w, ph, tv, 'B"', lb['B"'][0]), STMT(GT('B"')))
    ge0 = (gotocl(w, ph, tv, 'E0', lb['E0'][0]), STMT(GT('E0')))
    C_P0, C_Bp, C_E = CLN('P0', 'N', 'D'), CLN("B'", 'N1', 'D'), CLN('E', "N'", 'D0')
    MB = '( ( ( T" + T0 ) + T\' ) + 1 )'

    def caseA(pha, cs):
        L = L_(w, pha)
        cx = Ctx(w, pha, (HT('N1', 'C'), HLD('N1', "N'", 'L'), 'D0 = D'), root=cs)
        ht, hl, de = cx[HT('N1', 'C')], cx[HLD('N1', "N'", 'L')], cx['D0 = D']
        b = brstep(w, pha, 'tm2lbrt', L(P), L(meqBp), L(lb["B'"]), L(lb['B"']), L(dd), L(ct), L(ge0), L(ns['N1']), ht, "B'", 'B"', 'N1', 'D')
        l = ldstep(w, pha, L(P), L(meqBq), L(lb['B"']), L(lb['E']), L(dd), L(lt), L(ns['N1']), L(ns["N'"]), hl, 'B"', 'E', 'N1', "N'", 'D')
        s = hrseq(w, pha, L(P), b, l, C_Bp, CLN('B"', 'N1', 'D'), CLN('E', "N'", 'D'), '1', '1')
        dec = w.s([de], 'eqcomd', '( %s -> D = D0 )' % pha)
        sr, _, _, _ = hrrw(w, pha, s, C_Bp, CLN('E', "N'", 'D'), '( 1 + 1 )', deq=clneq(w, pha, 'E', "N'", dec, 'D', 'D0'))
        return bound0(w, pha, L(P), sr, C_Bp, C_E, '( 1 + 1 )', MB, {'T"': L(t2c), 'T0': L(t3c), "T'": L(t4c)}, hyps=[L(le1)])

    def caseB(phb, cs):
        L = L_(w, phb)
        cx = Ctx(w, phb, (HTF('N1', 'C'), (TRIP_IPA, TRIP_IPB, TRIP_IPC)), root=cs)
        htf, ta, tb, tc = cx[HTF('N1', 'C')], cx[TRIP_IPA], cx[TRIP_IPB], cx[TRIP_IPC]
        b = brstep(w, phb, 'tm2fbrg', L(P), L(meqBp), L(lb["B'"]), L(lb['E0']), L(dd), L(ct), L(gbq), L(ns['N1']), htf, "B'", 'E0', 'N1', 'D')
        s1 = hrseq(w, phb, L(P), b, ta, C_Bp, CLN('E0', 'N1', 'D'), CLN("E'", 'N"', "D'"), '1', 'T"')
        s2 = hrseq(w, phb, L(P), s1, tb, C_Bp, CLN("E'", 'N"', "D'"), CLN('E"', 'N0', 'D"'), '( 1 + T" )', 'T0')
        s3 = hrseq(w, phb, L(P), s2, tc, C_Bp, CLN('E"', 'N0', 'D"'), C_E, '( ( 1 + T" ) + T0 )', "T'")
        return bound0(w, phb, L(P), s3, C_Bp, C_E, '( ( ( 1 + T" ) + T0 ) + T\' )', MB, {'T"': L(t2c), 'T0': L(t3c), "T'": L(t4c)})

    s = casesplit(w, ph, disj, DISJ_IP, CASE_IPA, CASE_IPB, caseA, caseB, TRI(C_Bp, C_E, MB))
    tot = hrseq(w, ph, phm, trip1, s, C_P0, C_Bp, C_E, 'T1', MB)
    bound0(w, ph, phm, tot, C_P0, C_E, '( T1 + %s )' % MB, triple_parts(CONCL_IPT)[2], {'T1': t1c[0], 'T"': t2c[0], 'T0': t3c[0], "T'": t4c[0]}, qed=True)
    return w.run()


def tm2fdot():
    lab = 'tm2fdot'
    tree, ph = TREE_DOT, cj(TREE_DOT)
    w = W(lab, 'The test phase ` divOutTest ` of the divide-out loop (TM/PrimTD.lean): ` dup xr s t ; dup xd t s ; '
               'divmodC ; isZero s t ; dropNum s ` is a hypothesis triple into ` N1 ` leaving the quotient on ` u ` '
               '(the stacks ` D\' ` ; T7: ~ tm2fdup , ~ tm2fdm + ~ tm2fcan , ~ tm2fisz , ~ tm2fdrop ); ` Frag.ite ` '
               'at ` B\' ` on ` flag ` (` r mod d = 0 `) runs ` isZero xf s ` as a triple and loads ` flag := -. flag ` '
               '(~ tm2lbrt , ~ tm2flg ), or skips (~ tm2fbrg , ~ tm2flg ).  Lean: ` divOutTest_le_B ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    P = (phm, PHM)
    meqBp = (c[MEQ("B'", BR('C', 'B"', "E'"))], MEQ("B'", BR('C', 'B"', "E'")))
    meqE0 = (c[MEQ('E0', LD('L', 'E'))], MEQ('E0', LD('L', 'E')))
    meqEp = (c[MEQ("E'", LD("L'", 'E'))], MEQ("E'", LD("L'", 'E')))
    lb = {x: (c[LAB(x)], LAB(x)) for x in ('A', "B'", 'B"', 'E0', "E'", 'E')}
    ct, lt, lpt = (c[CTY('C')], CTY('C')), (c[LTY('L')], LTY('L')), (c[LTY("L'")], LTY("L'"))
    dpd = (c[STKD("D'")], STKD("D'"))
    t1c, t2c = [(c[x], x) for x in ('T1 e. NN0', 'T" e. NN0')]
    ns = {x: (c[SSS(x)], SSS(x)) for x in ('N', 'N1', 'N"', "N'")}
    trip1, disj = c[TRIP_DO1], c[DISJ_DO]
    gbq = (gotocl(w, ph, tv, 'B"', lb['B"'][0]), STMT(GT('B"')))
    gep = (gotocl(w, ph, tv, "E'", lb["E'"][0]), STMT(GT("E'")))
    C_A, C_Bp, C_E = CLN('A', 'N', 'D'), CLN("B'", 'N1', "D'"), CLN('E', "N'", "D'")
    MB = '( T" + 2 )'

    def caseA(pha, cs):
        L = L_(w, pha)
        cx = Ctx(w, pha, (HT('N1', 'C'), TRIP_DO2, HLD('N"', "N'", 'L')), root=cs)
        ht, tr2, hl = cx[HT('N1', 'C')], cx[TRIP_DO2], cx[HLD('N"', "N'", 'L')]
        b = brstep(w, pha, 'tm2lbrt', L(P), L(meqBp), L(lb["B'"]), L(lb['B"']), L(dpd), L(ct), L(gep), L(ns['N1']), ht, "B'", 'B"', 'N1', "D'")
        s1 = hrseq(w, pha, L(P), b, tr2, C_Bp, CLN('B"', 'N1', "D'"), CLN('E0', 'N"', "D'"), '1', 'T"')
        l = ldstep(w, pha, L(P), L(meqE0), L(lb['E0']), L(lb['E']), L(dpd), L(lt), L(ns['N"']), L(ns["N'"]), hl, 'E0', 'E', 'N"', "N'", "D'")
        s2 = hrseq(w, pha, L(P), s1, l, C_Bp, CLN('E0', 'N"', "D'"), C_E, '( 1 + T" )', '1')
        return bound0(w, pha, L(P), s2, C_Bp, C_E, '( ( 1 + T" ) + 1 )', MB, {'T"': L(t2c)})

    def caseB(phb, cs):
        L = L_(w, phb)
        cx = Ctx(w, phb, (HTF('N1', 'C'), HLD('N1', "N'", "L'")), root=cs)
        htf, hl = cx[HTF('N1', 'C')], cx[HLD('N1', "N'", "L'")]
        b = brstep(w, phb, 'tm2fbrg', L(P), L(meqBp), L(lb["B'"]), L(lb["E'"]), L(dpd), L(ct), L(gbq), L(ns['N1']), htf, "B'", "E'", 'N1', "D'")
        l = ldstep(w, phb, L(P), L(meqEp), L(lb["E'"]), L(lb['E']), L(dpd), L(lpt), L(ns['N1']), L(ns["N'"]), hl, "E'", 'E', 'N1', "N'", "D'")
        s = hrseq(w, phb, L(P), b, l, C_Bp, CLN("E'", 'N1', "D'"), C_E, '1', '1')
        return bound0(w, phb, L(P), s, C_Bp, C_E, '( 1 + 1 )', MB, {'T"': L(t2c)})

    s = casesplit(w, ph, disj, DISJ_DO, CASE_DOA, CASE_DOB, caseA, caseB, TRI(C_Bp, C_E, MB))
    tot = hrseq(w, ph, phm, trip1, s, C_A, C_Bp, C_E, 'T1', MB)
    bound0(w, ph, phm, tot, C_A, C_E, '( T1 + %s )' % MB, '( ( T1 + T" ) + 2 )', {'T1': t1c[0], 'T"': t2c[0]}, qed=True)
    return w.run()


def tm2fdo():
    lab = 'tm2fdo'
    tree, ph = TREE_DO, cj(TREE_DO)
    w = W(lab, 'The divide-out loop ` divOutF ` of TM/PrimTD.lean: ` divOutTest ` is a hypothesis triple from ` P0 ` into '
               'the loop\'s family at ` 0 ` (~ tm2fdot ), the loop ~ tm2floopu runs ` R ` iterations of the body '
               '` dropNum xr ; moveEntry u xr s ; predNum xf s ; divOutTest ` , itself one triple per iteration '
               '(blueprint D3; T7: ~ tm2fdrop , ~ tm2lme , ~ tm2fprdn , ~ tm2fdot ), and ` dropNum u ` at the exit is '
               'a triple (~ tm2fdrop ).  Lean: the generic core of ` divOutF_le_B ` , ` R := ( divOut d r fuel ).2 ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    trip0, tripx = c[TRIP_DO0], c[TRIP_DOX]
    lp = applylem(w, ph, 'tm2floopu', leafsteps(TREE_LOOPU, lambda t: c[t]), CONCL_LOOPU)
    C0, C1, C2, C3 = CLN('P0', 'O', 'D'), CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R')), CLN("E'", "N'", "D'")
    LB = "( ( R x. ( T' + 1 ) ) + 1 )"
    s1 = hrseq(w, ph, phm, trip0, lp, C0, C1, C2, 'U', LB)
    w.qed([phm, s1, tripx], 'syl3anc', '( %s -> %s )' % (ph, TRI(C0, C3, "( ( U + %s ) + U' )" % LB)))
    return w.run()


def tm2fsg():
    lab = 'tm2fsg'
    tree, ph = TREE_SG, cj(TREE_SG)
    w = W(lab, 'The smoothness loop ` smoothGoF ` of TM/PrimTD.lean: ` isZero xF s ` is a hypothesis triple from ` P0 ` '
               'into the loop\'s family at ` 0 ` (T7: ~ tm2fisz ), then ~ tm2floop runs ` R ` (` = fuel `) iterations of '
               '` dup xr xf s ; divOutF ; dropNum xf ; incr xd s ; predNum xF s ; isZero xF s ` , one triple per '
               'iteration with its own cost ` ( U\' ` i ) ` (blueprint D3, D4; T7: ~ tm2fdup , ~ tm2fdo , ~ tm2fdrop , '
               '~ tm2fincr , ~ tm2fprdn , ~ tm2fisz ).  Lean: the generic core of ` smoothGoF_le_B ` ; its '
               '` Frag.loop_runs_budget ` is the Sigma form, T7 bounds the sum by the budget.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    trip0 = c[TRIP_SG0]
    m = {'U': "U'"}
    treeS = ren(TREE_LOOPS, m)
    assert sub(HYPS_LS, m) == HYPS_SG
    lp = applylem(w, ph, 'tm2floop', leafsteps(treeS, lambda t: c[t]), sub(CONCL_LOOPS, m))
    C0, C1, C2 = CLN('P0', 'O', PF('0')), CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R'))
    SB = triple_parts(sub(CONCL_LOOPS, m))[2]
    fin = TRI(C0, C2, '( U + %s )' % SB)
    assert fin == CONCL_SG, (fin, CONCL_SG)
    w.qed([phm, trip0, lp], 'syl3anc', '( %s -> %s )' % (ph, fin))
    return w.run()


def tm2fstd():
    lab = 'tm2fstd'
    tree, ph = TREE_STD, cj(TREE_STD)
    w = W(lab, 'The smoothness test ` smoothTDF ` of TM/PrimTD.lean: ` dup xy s t ; predNum s t ; moveEntry s xy t ; '
               'pushNum xd 2 ` , ` smoothGoF ` (~ tm2fsg ) and ` dropNum xy ; dropNum xd ; pushNum s 1 ; cmpFrag xr s ` '
               'are three hypothesis triples at the stacks each leaves, then ` load\' ( flag := cmp = eq ) ` at ` A\' ` '
               '(~ tm2flg ).  Lean: the generic core of ` smoothTDF_le_B ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    t1, t2, t3 = c[TRIP_ST1], c[TRIP_ST2], c[TRIP_ST3]
    l = ldstep(w, ph, phm, c[MEQ("A'", LD('L', 'E'))], c[LAB("A'")], c[LAB('E')], c[STKD('D0')], c[LTY('L')], c[SSS('N0')], c[SSS("N'")],
               c[HLD('N0', "N'", 'L')], "A'", 'E', 'N0', "N'", 'D0')
    C0, C1, C2, C3, C4 = CLN('P0', 'N', 'D'), CLN('P1', 'N1', "D'"), CLN('A', 'N"', 'D"'), CLN("A'", 'N0', 'D0'), CLN('E', "N'", 'D0')
    s1 = hrseq(w, ph, phm, t1, t2, C0, C1, C2, 'T1', 'T"')
    s2 = hrseq(w, ph, phm, s1, t3, C0, C2, C3, '( T1 + T" )', 'T0')
    w.qed([phm, s2, l], 'syl3anc', '( %s -> %s )' % (ph, TRI(C0, C4, '( ( ( T1 + T" ) + T0 ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    for f in [tm2fpgb, tm2fpgq, tm2fpg, tm2fipt, tm2fdot, tm2fdo, tm2fsg, tm2fstd]:
        if want(f.__name__): f()
