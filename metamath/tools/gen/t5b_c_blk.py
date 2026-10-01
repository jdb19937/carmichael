"""T5b: one phase-1 iteration of the bit-length loop with the continuations
discharged (~ tm2fblk ): ~ tm2fblb with the ` flag ` -true branch by ~ tm2fincr
(the counter incremented, its precondition shrunk from the post-scan class
` O ` to the incr class ` N1 ` and its postcondition widened to ` N' ` ) and
the ` flag ` -false branch by ~ tm2flg ; blueprint D2, D3."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_b_iter import ldstep
from t5_d_scl import IFA as _IFA, IFB as _IFB

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def leafsteps(tree, look):
    if isinstance(tree, str):
        return look(tree)
    return tuple(leafsteps(t, look) for t in tree)


def z0word(w, ph, disj, DJ, casesspec, GA):
    """( ph -> Z0 e. Word GA ) by cases on the two-way disjunction DJ (a step disj)"""
    cases = []
    for casef, zeq, zw in casesspec:
        pha = '( %s /\\ %s )' % (ph, casef)
        cs = w.s([], 'simpr', '( %s -> %s )' % (pha, casef))
        czq = w.s([cs], 'simprd', '( %s -> Z0 = %s )' % (pha, zeq))
        zwa = lift(w, zw, pha, '%s e. Word %s' % (zeq, GA))
        cases.append(w.s([czq, zwa], 'eqeltrd', '( %s -> Z0 e. Word %s )' % (pha, GA)))
    allc = w.s(cases, 'jaodan', '( ( %s /\\ %s ) -> Z0 e. Word %s )' % (ph, DJ, GA))
    return w.s([disj, allc], 'mpdan', '( %s -> Z0 e. Word %s )' % (ph, GA))


def tm2fblk():
    lab = 'tm2fblk'
    tree, ph = TREE_BLK, cj(TREE_BLK)
    D1 = UP('D', 'K', 'X'); ZPDJ = CC(S1("Z'"), '( D ` J )'); D2 = D2_BLS1
    GWZ0 = CC(GW, 'Z0')
    POSTD = UP(D2, 'I', 'W0')
    w = W(lab, 'One iteration of the bit-length loop ` blBody ` (TM/Prims.lean) on a bit: '
               '~ tm2fblb with its continuations discharged --- when the ` flag ` is set '
               'the counter on stack ` I ` is incremented by ` incr ` (~ tm2fincr at the incr '
               'class ` N1 ` , entered from the post-scan class ` O ` by ~ tm2hssc and left '
               'into ` N\' ` by ~ tm2hssd , the run ` W ` of ones and the exit ` Z0 ` given by '
               'the incr disjunction), otherwise ` skip ` returns to the test (~ tm2flg ) '
               'and the counter is unchanged; the outcome ` W0 ` is named by the disjunction '
               '(blueprint D2, D3).  Lean: ` blBody_runs ` , the ` cons ` case, with '
               '` incr_correct ` and ` bl_step ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, ii, ip = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG], c["I' e. %s" % DG]
    nkj, nki, nji, nii = c['K =/= J'], c['K =/= I'], c['J =/= I'], c["I =/= I'"]
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)
    nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    dd, dke, dieq = c[STKD('D')], c['( D ` K ) = %s' % ZX], c['( D ` I ) = W1']
    zz, zp, xx = c['Z e. %s' % GK], c["Z' e. %s" % GJ], c[WRD('X', GK)]
    ww, xpw = c[WRD('W', 'B')], c[WRD("X'", GI)]
    yp, ypp = c["Y' e. %s" % GI], c['Y" e. %s' % GI]
    gf, bpi = c["G : B --> B'"], c["B' C_ %s" % GI]
    oss, n2s, n1s = c[SSS("O'")], c[SSS("N'")], c[SSS('N1')]
    hftn1 = c[HFT('N1')]
    disj, tt, t1 = c[DISJ_BLK], c["T' e. NN0"], c["1 <_ T'"]
    l1 = c[LTY("L'")]
    al, e0 = c[LAB('A')], c[LAB('E0')]
    meqE0 = c[MEQ('E0', STM_SK2)]
    # the stacks after the scan and the counter under them
    d1cl = updcl(w, ph, 'D', 'K', 'X', tv, dd, kk, xx)
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    zpdjw = ccatw(w, ph, s1w(w, ph, zp, "Z'", GJ), djw, S1("Z'"), '( D ` J )', GJ)
    d2cl = updcl(w, ph, D1, 'J', ZPDJ, tv, d1cl, jj, zpdjw)
    e1 = updnv(w, ph, D1, 'J', ZPDJ, 'I', tv, d1cl, jj, elv(w, ph, zpdjw, ZPDJ), ii, nij)
    e2 = updnv(w, ph, 'D', 'K', 'X', 'I', tv, dd, kk, elv(w, ph, xx, 'X'), ii, nik)
    d2i = w.s([w.s([e1, e2], 'eqtrd', '( %s -> ( %s ` I ) = ( D ` I ) )' % (ph, D2)), dieq], 'eqtrd',
               '( %s -> ( %s ` I ) = W1 )' % (ph, D2))
    C_E0 = CLN('E0', "O'", D2); C_A0 = CLN('A0', "O'", D2); POST = CLN('A', "N'", POSTD)
    TRB = lambda cont: TRI(CLN(cont, "O'", D2), POST, "T'")
    DISJ_TARGET = sub(DISJ_BLB, {'E"': 'A0', 'R': "T'", "D'": POSTD, 'O': "O'"})
    LEFT, RIGHT = '( %s /\\ %s )' % (HFT("O'"), TRB('A0')), '( %s /\\ %s )' % (HFF("O'"), TRB('E0'))
    assert DISJ_TARGET == '( %s \\/ %s )' % (LEFT, RIGHT), DISJ_TARGET
    # ---------------- the skip case
    pha = '( %s /\\ %s )' % (ph, SKPDJ)
    La = Lifter(w, pha)
    sk = w.s([], 'simpr', '( %s -> %s )' % (pha, SKPDJ))
    hff = w.s([sk, w.inst('simp1')], 'syl', '( %s -> %s )' % (pha, HFF("O'")))
    hsk = w.s([sk, w.inst('simp2')], 'syl', '( %s -> %s )' % (pha, HLOAD("O'", "N'")))
    w0e = w.s([sk, w.inst('simp3')], 'syl', '( %s -> W0 = W1 )' % pha)
    ta = ldstep(w, pha, La(phm, PHM), La(meqE0, MEQ('E0', STM_SK2)), La(e0, LAB('E0')), La(al, LAB('A')),
                La(d2cl, STKD(D2)), La(l1, LTY("L'")), La(oss, SSS("O'")), La(n2s, SSS("N'")), hsk, 'E0', 'A', "O'", "N'", D2)
    d2w0 = w.s([La(d2i, '( %s ` I ) = W1' % D2), w0e], 'eqtr4d', '( %s -> ( %s ` I ) = W0 )' % (pha, D2))
    uid = upidv(w, pha, D2, 'I', 'W0', d2w0, La(tv, 'T e. V'), La(d2cl, STKD(D2)), La(ii, 'I e. %s' % DG))
    uidc = w.s([uid], 'eqcomd', '( %s -> %s = %s )' % (pha, D2, POSTD))
    ta2, _, _, _ = hrrw(w, pha, ta, C_E0, CLN('A', "N'", D2), '1', deq=clneq(w, pha, 'A', "N'", uidc, D2, POSTD))
    ta3 = hrle(w, pha, La(phm, PHM), ta2, C_E0, POST, '1', "T'", La(tt, "T' e. NN0"), La(t1, "1 <_ T'"))
    ra = w.s([w.s([hff, ta3], 'jca', '( %s -> %s )' % (pha, RIGHT))], 'olcd', '( %s -> %s )' % (pha, DISJ_TARGET))
    # ---------------- the incr case
    phb = '( %s /\\ %s )' % (ph, INCDJ)
    Lb = Lifter(w, phb)
    inc = w.s([], 'simpr', '( %s -> %s )' % (phb, INCDJ))
    p1 = w.s([inc, w.inst('simp1')], 'syl', "( %s -> ( O' C_ N1 /\\ N1 C_ N' ) )" % phb)
    on1 = w.s([p1], 'simpld', "( %s -> O' C_ N1 )" % phb)
    n1n2 = w.s([p1], 'simprd', "( %s -> N1 C_ N' )" % phb)
    p2 = w.s([inc, w.inst('simp2')], 'syl', "( %s -> ( W1 = %s /\\ ( ( 2 x. ( # ` W ) ) + 3 ) <_ T' ) )" % (phb, CC('W', CC(S1('Z"'), "X'"))))
    w1e = w.s([p2], 'simpld', '( %s -> W1 = %s )' % (phb, CC('W', CC(S1('Z"'), "X'"))))
    lte = w.s([p2], 'simprd', "( %s -> ( ( 2 x. ( # ` W ) ) + 3 ) <_ T' )" % phb)
    p3 = w.s([inc, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ W0 = %s ) )' % (phb, DISJ_INC1, GWZ0))
    dinc = w.s([p3], 'simpld', '( %s -> %s )' % (phb, DISJ_INC1))
    w0e2 = w.s([p3], 'simprd', '( %s -> W0 = %s )' % (phb, GWZ0))
    d2ib = w.s([Lb(d2i, '( %s ` I ) = W1' % D2), w1e], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (phb, D2, CC('W', CC(S1('Z"'), "X'"))))
    # tm2fincr at D := D2
    inst = ren(INCR_TREE, {'D': D2})
    derived = {STKD(D2): Lb(d2cl, STKD(D2)), '( %s ` I ) = %s' % (D2, CC('W', CC(S1('Z"'), "X'"))): d2ib, DISJ_INC1: dinc}
    def look(t):
        if t in derived:
            return derived[t]
        return Lb(c[t], t)
    PRE0 = CLN('A0', 'N1', D2); POST0 = CLN('A', 'N1', UP(D2, 'I', GWZ0))
    NINC = '( ( 2 x. ( # ` W ) ) + 3 )'
    tb = applylem(w, phb, 'tm2fincr', leafsteps(inst, look), TRI(PRE0, POST0, NINC))
    # shrink the precondition to O, widen the postcondition to N'
    ssb = clnss(w, phb, 'A0', "O'", 'N1', D2, on1)
    tb2 = hrssc(w, phb, Lb(phm, PHM), tb, PRE0, POST0, NINC, C_A0, ssb)
    # Z0 e. Word GI and the post stacks
    ZA, ZB = CC(S1("Y'"), "X'"), CC(S1("Y'"), CC(S1('Y"'), "X'"))
    IFA1, IFB1 = sub(_IFA, INCR_MAP), sub(_IFB, INCR_MAP)
    zaw = ccatw(w, phb, s1w(w, phb, Lb(yp, "Y' e. %s" % GI), "Y'", GI), Lb(xpw, WRD("X'", GI)), S1("Y'"), "X'", GI)
    zbw0 = ccatw(w, phb, s1w(w, phb, Lb(ypp, 'Y" e. %s' % GI), 'Y"', GI), Lb(xpw, WRD("X'", GI)), S1('Y"'), "X'", GI)
    zbw = ccatw(w, phb, s1w(w, phb, Lb(yp, "Y' e. %s" % GI), "Y'", GI), zbw0, S1("Y'"), CC(S1('Y"'), "X'"), GI)
    casesspec = [('( %s /\\ Z0 = %s )' % (IFA1, ZA), ZA, zaw), ('( %s /\\ Z0 = %s )' % (IFB1, ZB), ZB, zbw)]
    assert DISJ_INC1 == '( %s \\/ %s )' % (casesspec[0][0], casesspec[1][0]), DISJ_INC1
    z0w = z0word(w, phb, dinc, DISJ_INC1, casesspec, GI)
    gwb = w.s([Lb(ww, WRD('W', 'B')), Lb(gf, "G : B --> B'"), w.inst('wrdco')], 'syl2anc', "( %s -> %s e. Word B' )" % (phb, GW))
    gwi = sswordd(w, phb, gwb, GW, "B'", GI, Lb(bpi, "B' C_ %s" % GI))
    gwz0w = ccatw(w, phb, gwi, z0w, GW, 'Z0', GI)
    pcl = updcl(w, phb, D2, 'I', GWZ0, Lb(tv, 'T e. V'), Lb(d2cl, STKD(D2)), Lb(ii, 'I e. %s' % DG), gwz0w)
    POST1 = CLN('A', "N'", UP(D2, 'I', GWZ0))
    ssd = clnss(w, phb, 'A', 'N1', "N'", UP(D2, 'I', GWZ0), n1n2)
    pcfg = cfgcl(w, phb, 'A', "N'", UP(D2, 'I', GWZ0), Lb(tv, 'T e. V'), Lb(al, LAB('A')), Lb(n2s, SSS("N'")), pcl)
    tb3 = hrssd(w, phb, Lb(phm, PHM), tb2, C_A0, POST0, NINC, POST1, ssd, pcfg)
    w0c = w.s([w0e2], 'eqcomd', '( %s -> %s = W0 )' % (phb, GWZ0))
    deq = clneq(w, phb, 'A', "N'", upeq(w, phb, D2, 'I', w0c, GWZ0, 'W0'), UP(D2, 'I', GWZ0), POSTD)
    tb4, _, _, _ = hrrw(w, phb, tb3, C_A0, POST1, NINC, deq=deq)
    tb5 = hrle(w, phb, Lb(phm, PHM), tb4, C_A0, POST, NINC, "T'", Lb(tt, "T' e. NN0"), lte)
    # flag true on O from N1
    sr = w.s([on1, w.inst('ssralv')], 'syl', '( %s -> ( %s -> %s ) )' % (phb, HFT('N1'), HFT("O'")))
    hfto = w.s([Lb(hftn1, HFT('N1')), sr], 'mpd', '( %s -> %s )' % (phb, HFT("O'")))
    rb = w.s([w.s([hfto, tb5], 'jca', '( %s -> %s )' % (phb, LEFT))], 'orcd', '( %s -> %s )' % (phb, DISJ_TARGET))
    # ---------------- the dispatch disjunction and tm2fblb
    both = w.s([ra, rb], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ_BLK, DISJ_TARGET))
    dt = w.s([disj, both], 'mpdan', '( %s -> %s )' % (ph, DISJ_TARGET))
    instb = ren(TREE_BLB, {'E"': 'A0', 'R': "T'", "D'": POSTD, 'O': "O'"})
    derived2 = {DISJ_TARGET: dt, "T' e. NN0": tt}
    def look2(t):
        if t in derived2:
            return derived2[t]
        return c[t]
    w.qed([jtree(w, ph, leafsteps(instb, look2))[0], w.inst('tm2fblb')], 'syl', '( %s -> %s )' % (ph, CONCL_BLK))
    return w.run()


if __name__ == '__main__':
    if want('tm2fblk'): tm2fblk()
