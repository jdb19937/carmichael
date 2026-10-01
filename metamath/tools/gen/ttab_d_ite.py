"""T-TAB: the fragments with an ` ite ` after a triple (blueprint D5):
~ tm2fsin (Lean ` setIfNoneF_runs `), ~ tm2flks (` lookupSlot_runs `),
~ tm2fdpb (` dpBodyF_runs `), ~ tm2frst (` resStep_runs `)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ttablib import *
from t6lib import gamk, lgk, wgk
from ttab_b_slot import LCtx, phmparts, instc, peekat, pushat6, brat, MTY

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def ite_case(w, pa, cs, c, tv, mt, ref, A, E, Q, gq, C, N, D, test, leaves):
    """the branch at A on N (stacks D) to E; returns (L, cx, step)"""
    L = LCtx(w, pa, c)
    tva, mta = L.L(tv, 'T e. V'), L.L(mt, MTY)
    cx = Ctx(w, pa, leaves, root=cs)
    b, bc = brat(w, pa, L, tva, mta, ref, A, E, GT(Q), C, N, D, {test: cx[test], STMT(GT(Q)): L.L(gq, STMT(GT(Q)))})
    assert triple_parts(bc)[:2] == (CLN(A, N, D), CLN(E, N, D)), bc
    return L, cx, b, tva, mta


def tm2fsin_lks(kind):
    sin = kind == 'sin'
    lab = 'tm2fsin' if sin else 'tm2flks'
    tree = TREE_SIN if sin else TREE_LKS
    ph = cj(tree)
    if sin:
        desc = ('` Alg.setIfNone ` on the DP table, ` setIfNoneF tbl j w s scr ` (TM/Table.lean): ` walkDown ` is a '
                'hypothesis triple (T7: ~ tm2fwdn ), ` peekKet tbl ` reads the slot\'s top letter ` Z ` (~ tm2lpk ), '
                '` Frag.ite ` on ` flag ` either pops the ` ket ` (~ tm2lpop ) and runs ` moveSlot w tbl s j ` as a '
                'triple (T7: ~ tm2fmvs ) or runs ` dropList w ` as a triple (T7: ~ tm2fdpl ), and ` walkUp ` is a '
                'triple (T7: ~ tm2fwup ).  Lean: ` setIfNoneF_runs ` , bound ` setC j N b m ` .')
    else:
        desc = ('Looking up a slot of the DP table, ` lookupSlot tbl j w s scr ` (TM/Table.lean): ` walkDown ` is a '
                'hypothesis triple, ` peekKet tbl ` reads the slot\'s top letter ` Z ` (~ tm2lpk ), ` Frag.ite ` on '
                '` flag ` either pushes the letter ` Y ` on ` J ` (~ tm2fpshn ; the class after the push is contained '
                'in ` N\' ` ) or runs ` copyList tbl w s j ` as a triple (T7: ~ tmilcpyn ), and ` walkUp ` is a triple.  '
                'Lean: ` lookupSlot_runs ` , bound ` lookC j N b m ` .')
    w = W(lab, desc)
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv, mt = phmparts(w, ph, phm)
    pk, cc = peekat(w, ph, c, tv, mt, {}, 'Q0', "B'", 'K', 'F', "D'", 'Z', 'X', 'N1', 'N"')
    C0, C1, C2, C3, C4 = (CLN('P0', 'N', 'D'), CLN('Q0', 'N1', "D'"), CLN("B'", 'N"', "D'"), CLN("A'", "N'", 'D"'),
                          CLN('E', 'O', 'D0'))
    assert triple_parts(cc)[:2] == (C1, C2), cc
    ge0 = gotocl(w, ph, tv, 'E0', c[LAB('E0')])
    gbq = gotocl(w, ph, tv, 'B"', c[LAB('B"')])
    MB = '( T1 + 2 )' if sin else '( T1 + 1 )'
    CASEA, CASEB, DISJ = (CASE_SINA, CASE_SINB, DISJ_SIN) if sin else (CASE_LKSA, CASE_LKSB, DISJ_LKS)
    CBq = CLN('B"', 'N"', "D'")

    def caseA(pha, cs):
        if sin:
            lv = (HT('N"', 'C'), HPK('N"', "F'", 'Z', 'N0'), TRIP_SINA)
        else:
            lv = (HT('N"', 'C'), 'N" C_ N\'', 'D" = %s' % YPUSH("D'", 'J', 'Y'))
        L, cx, b, tva, mta = ite_case(w, pha, cs, c, tv, mt, 'tm2lbrt', "B'", 'B"', 'E0', ge0, 'C', 'N"', "D'", HT('N"', 'C'), lv)
        if sin:
            pp, pc = peekat(w, pha, L, tva, mta, {HPK('N"', "F'", 'Z', 'N0'): cx[HPK('N"', "F'", 'Z', 'N0')]},
                            'B"', 'B1_', 'K', "F'", "D'", 'Z', 'X', 'N"', 'N0', ref='tm2lpop')
            CB1 = CLN('B1_', 'N0', UP("D'", 'K', 'X'))
            assert triple_parts(pc)[:2] == (CBq, CB1), pc
            q = hrseq(w, pha, L[PHM], b, pp, C2, CBq, CB1, '1', '1')
            q = hrseq(w, pha, L[PHM], q, cx[TRIP_SINA], C2, CB1, C3, '( 1 + 1 )', 'T1')
            return bound0(w, pha, L[PHM], q, C2, C3, '( ( 1 + 1 ) + T1 )', MB, {'T1': L['T1 e. NN0']})
        ps, psc, jd, gej = pushat6(w, pha, L, tva, mta, L[GEQ], L[GAMK('J')], L['Y e. %s' % GAM], 'B"', "A'", 'J', 'Y', 'N"',
                                   "D'", L[STKD("D'")], L[SSS('N"')])
        D2x = YPUSH("D'", 'J', 'Y')
        CAx = CLN("A'", 'N"', D2x)
        assert triple_parts(psc)[:2] == (CBq, CAx), psc
        de = w.s([cx['D" = %s' % D2x]], 'eqcomd', '( %s -> %s = D" )' % (pha, D2x))
        psr, _, _, _ = hrrw(w, pha, ps, CBq, CAx, '1', deq=clneq(w, pha, "A'", 'N"', de, D2x, 'D"'))
        ss = clnss(w, pha, "A'", 'N"', "N'", 'D"', cx['N" C_ N\''])
        acfg = cfgcl(w, pha, "A'", "N'", 'D"', tva, L[LAB("A'")], L[SSS("N'")], L[STKD('D"')])
        psr2 = hrssd(w, pha, L[PHM], psr, CBq, CLN("A'", 'N"', 'D"'), '1', C3, ss, acfg)
        q = hrseq(w, pha, L[PHM], b, psr2, C2, CBq, C3, '1', '1')
        return bound0(w, pha, L[PHM], q, C2, C3, '( 1 + 1 )', MB, {'T1': L['T1 e. NN0']}, hyps=[L['1 <_ T1']])

    def caseB(phb, cs):
        TR = TRIP_SINB if sin else TRIP_LKSB
        TB = 'T"' if sin else 'T1'
        L, cx, b, tvb, mtb = ite_case(w, phb, cs, c, tv, mt, 'tm2fbrg', "B'", 'E0', 'B"', gbq, 'C', 'N"', "D'",
                                      HTF('N"', 'C'), (HTF('N"', 'C'), TR))
        CE0 = CLN('E0', 'N"', "D'")
        q = hrseq(w, phb, L[PHM], b, cx[TR], C2, CE0, C3, '1', TB)
        lv = {'T1': L['T1 e. NN0']}
        hy = []
        if sin:
            lv['T"'] = L['T" e. NN0']; hy = [L['T" <_ ( T1 + 1 )']]
        return bound0(w, phb, L[PHM], q, C2, C3, '( 1 + %s )' % TB, MB, lv, hyps=hy)

    s = casesplit(w, ph, c[DISJ], DISJ, CASEA, CASEB, caseA, caseB, TRI(C2, C3, MB))
    q = hrseq(w, ph, phm, c[TRIP_SIN1], pk, C0, C1, C2, 'U', '1')
    q = hrseq(w, ph, phm, q, s, C0, C2, C3, '( U + 1 )', MB)
    q = hrseq(w, ph, phm, q, c[TRIP_SIN4], C0, C3, C4, '( ( U + 1 ) + %s )' % MB, "U'")
    bound0(w, ph, phm, q, C0, C4, "( ( ( U + 1 ) + %s ) + U' )" % MB, triple_parts(CONCL_SIN if sin else CONCL_LKS)[2],
           {'U': c['U e. NN0'], "U'": c["U' e. NN0"], 'T1': c['T1 e. NN0']}, qed=True)
    return w.run()


def tm2fdpb():
    lab = 'tm2fdpb'
    tree, ph = TREE_DPB, cj(TREE_DPB)
    w = W(lab, 'One iteration of the DP step, ` dpBodyF np nL snap acc s t ` (TM/Table.lean): ` resStep ` is a hypothesis '
               'triple (T7: ~ tm2frst ), ` peekKet snap ` reads the snapshot slot\'s top letter ` Z ` (~ tm2lpk ), and '
               '` Frag.ite ` on ` flag ` either pops the ` ket ` (~ tm2lpop ) or runs ` dup np snap s ; dup nL np s ; '
               'setIfNoneF acc np snap s t ` as one triple (T7: ~ tm2fdup , ~ tm2fsin ).  Lean: ` dpBodyF_runs ` , '
               'bound ` dpBodyC L N b ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv, mt = phmparts(w, ph, phm)
    pk, cc = peekat(w, ph, c, tv, mt, {}, 'Q0', "B'", 'K', 'F', "D'", 'Z', 'X', 'N1', 'N"')
    C0, C1, C2, C3 = CLN('P0', 'N', 'D'), CLN('Q0', 'N1', "D'"), CLN("B'", 'N"', "D'"), CLN('A', "N'", 'D"')
    assert triple_parts(cc)[:2] == (C1, C2), cc
    ge0 = gotocl(w, ph, tv, 'E0', c[LAB('E0')])
    gbq = gotocl(w, ph, tv, 'B"', c[LAB('B"')])
    MB = '( T1 + 1 )'
    CBq = CLN('B"', 'N"', "D'")
    TRB = TRI(CLN('E0', 'N"', "D'"), C3, 'T1')

    def caseA(pha, cs):
        lv = (HT('N"', 'C'), HPK('N"', "F'", 'Z', "N'"), 'D" = %s' % UP("D'", 'K', 'X'))
        L, cx, b, tva, mta = ite_case(w, pha, cs, c, tv, mt, 'tm2lbrt', "B'", 'B"', 'E0', ge0, 'C', 'N"', "D'", HT('N"', 'C'), lv)
        pp, pc = peekat(w, pha, L, tva, mta, {HPK('N"', "F'", 'Z', "N'"): cx[HPK('N"', "F'", 'Z', "N'")]},
                        'B"', 'A', 'K', "F'", "D'", 'Z', 'X', 'N"', "N'", ref='tm2lpop')
        D2x = UP("D'", 'K', 'X')
        CAx = CLN('A', "N'", D2x)
        assert triple_parts(pc)[:2] == (CBq, CAx), pc
        de = w.s([cx['D" = %s' % D2x]], 'eqcomd', '( %s -> %s = D" )' % (pha, D2x))
        ppr, _, _, _ = hrrw(w, pha, pp, CBq, CAx, '1', deq=clneq(w, pha, 'A', "N'", de, D2x, 'D"'))
        q = hrseq(w, pha, L[PHM], b, ppr, C2, CBq, C3, '1', '1')
        return bound0(w, pha, L[PHM], q, C2, C3, '( 1 + 1 )', MB, {'T1': L['T1 e. NN0']}, hyps=[L['1 <_ T1']])

    def caseB(phb, cs):
        L, cx, b, tvb, mtb = ite_case(w, phb, cs, c, tv, mt, 'tm2fbrg', "B'", 'E0', 'B"', gbq, 'C', 'N"', "D'",
                                      HTF('N"', 'C'), (HTF('N"', 'C'), TRB))
        q = hrseq(w, phb, L[PHM], b, cx[TRB], C2, CLN('E0', 'N"', "D'"), C3, '1', 'T1')
        return bound0(w, phb, L[PHM], q, C2, C3, '( 1 + T1 )', MB, {'T1': L['T1 e. NN0']})

    s = casesplit(w, ph, c[DISJ_DPB], DISJ_DPB, CASE_DPBA, CASE_DPBB, caseA, caseB, TRI(C2, C3, MB))
    q = hrseq(w, ph, phm, c[TRIP_DPB1], pk, C0, C1, C2, 'U', '1')
    q = hrseq(w, ph, phm, q, s, C0, C2, C3, '( U + 1 )', MB)
    bound0(w, ph, phm, q, C0, C3, '( ( U + 1 ) + %s )' % MB, '( ( U + T1 ) + 2 )', {'U': c['U e. NN0'], 'T1': c['T1 e. NN0']},
           qed=True)
    return w.run()


def tm2frst():
    lab = 'tm2frst'
    tree, ph = TREE_RST, cj(TREE_RST)
    w = W(lab, 'The residue update ` resStep nL np s t ` of the DP step (TM/Table.lean), alphabet-free: ` moveEntry ; dup ; '
               'dup ; cmpFrag ` is one hypothesis triple into ` N1 ` , ` Frag.ite ` on ` cmp = lt ` runs one of two '
               'triples (the seven calls computing ` L - ( q - a ) ` , or ` dup ; sub ` computing ` a - q ` ; T7: '
               '~ tm2fdup , ~ tm2fsubx , ~ tm2lme ), and ` moveEntry np nL s ` is a triple.  Lean: ` resStep_runs ` , '
               'bound ` 25 m + 53 ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv, mt = phmparts(w, ph, phm)
    C0, C1, C2, C3 = CLN('P0', 'N', 'D'), CLN("B'", 'N1', "D'"), CLN('A', 'N"', 'D"'), CLN('E', "N'", 'D0')
    ge0 = gotocl(w, ph, tv, 'E0', c[LAB('E0')])
    ge1 = gotocl(w, ph, tv, 'E1', c[LAB('E1')])
    MB = '( T" + 1 )'

    def caseA(pha, cs):
        L, cx, b, tva, mta = ite_case(w, pha, cs, c, tv, mt, 'tm2lbrt', "B'", 'E0', 'E1', ge1, 'C', 'N1', "D'", HT('N1', 'C'),
                                      (HT('N1', 'C'), TRIP_RSTA))
        q = hrseq(w, pha, L[PHM], b, cx[TRIP_RSTA], C1, CLN('E0', 'N1', "D'"), C2, '1', 'T"')
        return bound0(w, pha, L[PHM], q, C1, C2, '( 1 + T" )', MB, {'T"': L['T" e. NN0']})

    def caseB(phb, cs):
        L, cx, b, tvb, mtb = ite_case(w, phb, cs, c, tv, mt, 'tm2fbrg', "B'", 'E1', 'E0', ge0, 'C', 'N1', "D'", HTF('N1', 'C'),
                                      (HTF('N1', 'C'), TRIP_RSTB))
        q = hrseq(w, phb, L[PHM], b, cx[TRIP_RSTB], C1, CLN('E1', 'N1', "D'"), C2, '1', 'T0')
        return bound0(w, phb, L[PHM], q, C1, C2, '( 1 + T0 )', MB, {'T"': L['T" e. NN0'], 'T0': L['T0 e. NN0']},
                      hyps=[L['T0 <_ T"']])

    CASEA = '( %s /\\ %s )' % (HT('N1', 'C'), TRIP_RSTA)
    CASEB = '( %s /\\ %s )' % (HTF('N1', 'C'), TRIP_RSTB)
    s = casesplit(w, ph, c[DISJ_RST], DISJ_RST, CASEA, CASEB, caseA, caseB, TRI(C1, C2, MB))
    q = hrseq(w, ph, phm, c[TRIP_RST1], s, C0, C1, C2, 'T1', MB)
    q = hrseq(w, ph, phm, q, c[TRIP_RST4], C0, C2, C3, '( T1 + %s )' % MB, "T'")
    bound0(w, ph, phm, q, C0, C3, "( ( T1 + %s ) + T' )" % MB, triple_parts(CONCL_RST)[2],
           {'T1': c['T1 e. NN0'], 'T"': c['T" e. NN0'], "T'": c["T' e. NN0"]}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fsin'): tm2fsin_lks('sin')
    if want('tm2flks'): tm2fsin_lks('lks')
    if want('tm2fdpb'): tm2fdpb()
    if want('tm2frst'): tm2frst()
